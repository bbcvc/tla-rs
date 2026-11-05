//! Computes SANY's level information for each definition, following tla-ts `levels.ts`, and the
//! order SANY checks `RECURSIVE` sections in (`ModuleNode.levelCheck`).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use tla_tools_ast::Span;

use super::data::{Data, Operator, Param, builtin_signature};
use super::layout::{FrameId, Layout};
use crate::ir::{DefBody, DefId, DefLevels, Level, Local, ModuleId, Spec};

/// A level error, and where it goes among the others.
#[derive(Debug)]
pub(crate) struct Found {
    /// The definition or instantiation the error is in, by the order the resolver made it.
    pub order: usize,
    pub module: ModuleId,
    pub span: Span,
    pub message: String,
    /// Whether SANY reports the error: it checks a module once by itself, not each instance of it.
    pub is_reported: bool,
}

/// What the level pass knows about a definition.
#[derive(Debug)]
pub(crate) struct DefInfo {
    /// The level information of the body, with the constraints of the definitions of its `LET`s.
    pub raw: Data,
    /// The parameters the body uses where the Leibniz rule fails.
    pub non_leibniz: BTreeSet<Param>,
    /// The definition as an operator of its own parameters.
    pub own: Rc<Operator>,
}

#[derive(Clone, Debug)]
enum State {
    Unvisited,
    /// The levels SANY assumes for a `RECURSIVE` operator not checked yet in its section.
    Preset(Rc<DefInfo>),
    /// Being analyzed. A recursive reference sees the levels so far.
    InProgress(Rc<DefInfo>),
    /// Analyzed in the first pass over a `RECURSIVE` section, to analyze again from these levels.
    Stale(Rc<DefInfo>),
    Done(Rc<DefInfo>),
}

/// The definition whose body is being analyzed, with the frames its locals refer to.
pub(crate) struct Body<'a> {
    pub def: Option<DefId>,
    /// The frames from the definition's own outward.
    pub chain: Vec<FrameId>,
    pub let_bodies: &'a [Span],
    pub label_bodies: &'a [Span],
}

impl<'a> Body<'a> {
    /// The body of a definition, or a value outside any definition when `def` is `None`.
    pub fn new(
        def: Option<DefId>,
        chain: Vec<FrameId>,
        let_bodies: &'a [Span],
        label_bodies: &'a [Span],
    ) -> Self {
        Self { def, chain, let_bodies, label_bodies }
    }

    pub fn param(&self, local: Local) -> Param {
        let frame = self.chain.get(local.hops).copied().unwrap_or(FrameId::MAX);
        Param::Slot(frame, local.slot)
    }

    pub fn slot(&self, slot: usize) -> Param {
        self.param(Local { hops: 0, slot })
    }

    /// Whether SANY sees an operator application here, rather than a `LET`.
    pub fn is_application(&self, span: Span) -> bool {
        !self.is_let_body(span) && !self.label_bodies.contains(&span)
    }

    pub fn is_let_body(&self, span: Span) -> bool {
        self.let_bodies.contains(&span)
    }
}

pub(crate) struct Analyzer<'a> {
    pub spec: &'a Spec,
    pub layout: &'a Layout,
    states: Vec<State>,
    builtins: HashMap<&'static str, Rc<Operator>>,
    /// A definition as an operator of the parameters of the given number of instances around it
    /// and its own.
    instance_views: HashMap<(DefId, usize), Rc<Operator>>,
    pub errors: Vec<Found>,
}

impl<'a> Analyzer<'a> {
    pub fn new(spec: &'a Spec, layout: &'a Layout) -> Self {
        Self {
            spec,
            layout,
            states: vec![State::Unvisited; spec.defs.len()],
            builtins: HashMap::new(),
            instance_views: HashMap::new(),
            errors: Vec::new(),
        }
    }

    pub fn builtin(&mut self, name: &'static str) -> Rc<Operator> {
        let operator = self.builtins.entry(name).or_insert_with(|| {
            let (level, max_levels, weights) = builtin_signature(name);
            Rc::new(Operator::builtin(name, level, max_levels, weights))
        });
        operator.clone()
    }

    /// Records a level error in a definition. A value outside any definition has none.
    pub fn error(&mut self, def: Option<DefId>, span: Span, message: impl Into<String>) {
        let Some(def) = def else { return };
        let is_reported = !self.layout.defs[def.index()].is_instantiated;
        self.errors.push(Found {
            order: def.index(),
            module: self.spec.def(def).module,
            span,
            message: message.into(),
            is_reported,
        });
    }

    /// The name SANY gives a definition: `I!Op` for a definition of the instance `I`.
    pub fn name(&self, def: DefId) -> Rc<str> {
        let layout = &self.layout.defs[def.index()];
        let name = self.spec.def(def).name;
        match &layout.qualifier {
            Some(qualifier) if layout.is_instantiated => format!("{qualifier}{name}").into(),
            _ => name.as_str().into(),
        }
    }

    /// The frame the definition captures: the one around its own.
    pub fn parent_frame(&self, def: DefId) -> Option<FrameId> {
        let frame = self.layout.defs[def.index()].frame?;
        self.layout.frames[frame].parent
    }

    fn chain(&self, def: DefId) -> Vec<FrameId> {
        let mut chain = Vec::new();
        let mut frame = self.layout.defs[def.index()].frame;
        while let Some(id) = frame {
            chain.push(id);
            frame = self.layout.frames[id].parent;
        }
        chain
    }

    /// The formal parameters of a definition: the first slots of its frame.
    fn formals(&self, def: DefId) -> Vec<Param> {
        let frame = self.layout.defs[def.index()].frame.unwrap_or(FrameId::MAX);
        (0..self.spec.def(def).params.len()).map(|slot| Param::Slot(frame, slot)).collect()
    }

    /// The arity of an operator parameter or constant.
    pub fn arity(&self, param: Param) -> usize {
        match param {
            Param::Slot(frame, slot) => self
                .layout
                .frames
                .get(frame)
                .and_then(|frame| frame.params.get(slot).copied())
                .unwrap_or(0),
            Param::Const(id) => self.spec.constants[id.index()].arity,
            Param::Var(_) => 0,
        }
    }

    /// `def` as an operator of `formals`, with the level information `raw` of its body. What
    /// `raw` says of the variables the body binds is dropped.
    pub fn view(
        &self,
        def: DefId,
        raw: &Data,
        non_leibniz: &BTreeSet<Param>,
        formals: Vec<Param>,
        arities: &[usize],
    ) -> Operator {
        let frame = self.layout.defs[def.index()].frame;
        let is_bound = |param: Param| match param {
            Param::Slot(slot_frame, _) => Some(slot_frame) == frame && !formals.contains(&param),
            _ => false,
        };
        let name = self.name(def);
        Operator::defined(name, raw, non_leibniz, formals.clone(), arities, is_bound)
    }

    /// The information of `def` with the level information `raw` of its body.
    fn def_info(&self, def: DefId, raw: Data, non_leibniz: BTreeSet<Param>) -> DefInfo {
        let formals = self.formals(def);
        let own = self.view(def, &raw, &non_leibniz, formals, &self.spec.def(def).params);
        DefInfo { raw, non_leibniz, own: Rc::new(own) }
    }

    /// The level information of a definition, analyzing it the first time.
    pub fn info(&mut self, def: DefId) -> Rc<DefInfo> {
        let previous = match &self.states[def.index()] {
            State::Done(info) | State::InProgress(info) | State::Preset(info) => {
                return info.clone();
            }
            State::Stale(info) => Some(info.clone()),
            State::Unvisited => None,
        };
        self.compute(def, previous)
    }

    /// Whether the definition's levels are final, so views of it can be kept.
    pub fn is_done(&self, def: DefId) -> bool {
        matches!(self.states[def.index()], State::Done(_))
    }

    pub fn instance_view(&self, def: DefId, instances: usize) -> Option<Rc<Operator>> {
        self.instance_views.get(&(def, instances)).cloned()
    }

    pub fn keep_instance_view(&mut self, def: DefId, instances: usize, view: Rc<Operator>) {
        self.instance_views.insert((def, instances), view);
    }

    /// Analyzes a definition. SANY's checks of a definition start from the levels it had before,
    /// which only `RECURSIVE` sections give it.
    fn compute(&mut self, def: DefId, previous: Option<Rc<DefInfo>>) -> Rc<DefInfo> {
        let provisional = match &previous {
            Some(info) => info.clone(),
            None => Rc::new(self.def_info(def, Data::default(), BTreeSet::new())),
        };
        self.states[def.index()] = State::InProgress(provisional);
        let mut info = self.analyze(def);
        if let Some(previous) = previous {
            info = self.combine(def, &previous, info);
        }
        let info = Rc::new(info);
        self.states[def.index()] = State::Done(info.clone());
        info
    }

    fn analyze(&mut self, def: DefId) -> DefInfo {
        let spec = self.spec;
        let layout = &self.layout.defs[def.index()];
        let body = Body::new(Some(def), self.chain(def), &layout.let_bodies, &layout.label_bodies);
        let mut non_leibniz = BTreeSet::new();
        let mut raw = match &spec.def(def).body {
            DefBody::Expr(expr) => {
                self.leibniz(&body, expr, false, &mut non_leibniz);
                self.expr(&body, expr)
            }
            DefBody::Function { bounds, body: value } => {
                for bound in bounds {
                    self.leibniz(&body, &bound.set, false, &mut non_leibniz);
                }
                self.leibniz(&body, value, false, &mut non_leibniz);
                self.function(&body, value.span, bounds, value)
            }
        };
        // SANY adds what the definitions of a `LET` require to what its body does.
        for &child in &layout.lets {
            let child = self.info(child);
            raw.add_constraints(&child.own.data, |_| true);
        }
        self.def_info(def, raw, non_leibniz)
    }

    /// Carries the levels of an earlier check of a definition into a new one, as SANY's fields
    /// keep them: the highest level, the lowest maximum levels, and every weight.
    fn combine(&self, def: DefId, previous: &DefInfo, info: DefInfo) -> DefInfo {
        let DefInfo { mut raw, mut non_leibniz, .. } = info;
        raw.level = raw.level.max(previous.raw.level);
        raw.params.extend(&previous.raw.params);
        raw.arg_params.extend(&previous.raw.arg_params);
        for formal in self.formals(def) {
            if let Some(&level) = previous.raw.constraints.get(&formal) {
                raw.constrain(formal, level);
            }
        }
        non_leibniz.extend(&previous.non_leibniz);
        self.def_info(def, raw, non_leibniz)
    }

    /// Analyzes every definition, the `RECURSIVE` sections first, as SANY does.
    pub fn run(&mut self) {
        let mut sections: BTreeMap<usize, Vec<DefId>> = BTreeMap::new();
        for (index, layout) in self.layout.defs.iter().enumerate() {
            if let Some(section) = layout.section {
                sections.entry(section).or_default().push(DefId(index as u32));
            }
        }
        for members in sections.values() {
            self.section(members);
        }
        for index in 0..self.spec.defs.len() {
            self.info(DefId(index as u32));
        }
        self.check_assumptions();
    }

    /// SANY checks the definitions of a `RECURSIVE` section twice: first assuming each recursive
    /// operator takes arguments up to action level, then from the highest level of any of them.
    fn section(&mut self, members: &[DefId]) {
        let recursive: Vec<DefId> = members
            .iter()
            .copied()
            .filter(|def| self.layout.defs[def.index()].is_recursive)
            .collect();
        for &def in &recursive {
            let mut raw = Data::default();
            for formal in self.formals(def) {
                raw.params.insert(formal);
                raw.constrain(formal, Level::Action);
            }
            let preset = self.def_info(def, raw, BTreeSet::new());
            self.states[def.index()] = State::Preset(Rc::new(preset));
        }
        for &def in members {
            match self.states[def.index()].clone() {
                State::Preset(info) => {
                    self.compute(def, Some(info));
                }
                _ => {
                    self.info(def);
                }
            }
        }
        let mut level = Level::Constant;
        let mut params = BTreeSet::new();
        for &def in &recursive {
            let info = self.info(def);
            for (index, max) in info.own.max_levels.iter().enumerate() {
                if *max < Level::Action {
                    let name = self.spec.def(def).name;
                    let message =
                        format!("Argument {} of recursive operator {name} is primed", index + 1);
                    self.error(Some(def), self.spec.def(def).span, message);
                }
            }
            level = level.max(info.own.data.level);
            params.extend(info.own.data.params.iter().copied());
        }
        for &def in members {
            let info = self.info(def);
            let mut raw = info.raw.clone();
            raw.level = raw.level.max(level);
            raw.params.extend(&params);
            let stale = self.def_info(def, raw, info.non_leibniz.clone());
            self.states[def.index()] = State::Stale(Rc::new(stale));
        }
        for &def in members {
            self.info(def);
        }
    }

    /// SANY requires every assumption to be a constant.
    fn check_assumptions(&mut self) {
        for &def in &self.spec.assumptions {
            let level = self.info(def).own.data.level;
            if level != Level::Constant {
                let message = format!(
                    "Level error: assumptions must be level 0 (Constant), \nbut this one has level {}.",
                    level.number()
                );
                self.error(Some(def), self.spec.def(def).span, message);
            }
        }
    }

    /// The levels of a definition, for the resolved program.
    pub fn def_levels(&mut self, def: DefId) -> DefLevels {
        let own = self.info(def).own.clone();
        DefLevels {
            level: own.data.level,
            max_levels: own.max_levels.clone(),
            weights: own.weights.clone(),
            min_max_levels: own.min_max_levels.clone(),
            leibniz: (0..own.arity).map(|index| !own.non_leibniz.contains(&index)).collect(),
        }
    }
}

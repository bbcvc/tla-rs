//! Prints the tree-sitter CST of a TLA+ file: `cargo run -p tla-tools-parser --example cst -- Spec.tla`
fn main() {
    let path = std::env::args().nth(1).expect("usage: cst <file.tla>");
    let source = std::fs::read_to_string(&path).expect("read file");
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&tree_sitter_tlaplus::LANGUAGE.into()).expect("load grammar");
    let tree = parser.parse(&source, None).expect("parse");
    print(tree.root_node(), &source, 0, None);
}

fn print(node: tree_sitter::Node, source: &str, depth: usize, field: Option<&str>) {
    if !node.is_named() {
        return;
    }
    let text = if node.child_count() == 0 {
        format!(" {:?}", &source[node.byte_range()])
    } else {
        String::new()
    };
    let label = field.map(|name| format!("{name}: ")).unwrap_or_default();
    println!("{}{label}{}{text}", "  ".repeat(depth), node.kind());
    let mut cursor = node.walk();
    for (index, child) in node.children(&mut cursor).enumerate() {
        print(child, source, depth + 1, node.field_name_for_child(index as u32));
    }
}

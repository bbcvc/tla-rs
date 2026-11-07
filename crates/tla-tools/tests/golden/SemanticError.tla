---- MODULE SemanticError ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = Successor(x)
====

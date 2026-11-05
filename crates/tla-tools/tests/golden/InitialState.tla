---- MODULE InitialState ----
EXTENDS Naturals
VARIABLES x, y
Init == x \in 1..3 /\ y = "s"
Next == UNCHANGED <<x, y>>
Positive == x > 1
====

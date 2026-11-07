---- MODULE InitialStateError ----
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Inv == IF x = 0 THEN TRUE ELSE x + 1
====

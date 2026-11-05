---- MODULE ActionProperty ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars
Increasing == [][x' > x]_vars
====

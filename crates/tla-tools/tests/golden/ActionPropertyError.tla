---- MODULE ActionPropertyError ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x
Step == [][x' \div (2 - x) >= 0]_x
====

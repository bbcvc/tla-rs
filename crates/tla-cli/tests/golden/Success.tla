---- MODULE Success ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ UNCHANGED y
        \/ y < 2 /\ y' = y + 1 /\ UNCHANGED x
        \/ x = 3 /\ y = 2 /\ UNCHANGED vars
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
TypeOK == x \in 0..3 /\ y \in 0..2
Done == <>(x = 3 /\ y = 2)
====

---- MODULE Stutter ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == \/ x < 2 /\ x' = x + 1
        \/ x = 2 /\ UNCHANGED x
Spec == Init /\ [][Next]_vars
Ends == <>(x = 3)
====

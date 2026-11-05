---- MODULE Lasso ----
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Up == x < 2 /\ x' = x + 1
Wrap == x = 2 /\ x' = 1
Next == Up \/ Wrap
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
ReachesZeroAgain == []<>(x = 0)
====

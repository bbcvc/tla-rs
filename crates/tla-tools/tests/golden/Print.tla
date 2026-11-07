---- MODULE Print ----
EXTENDS Naturals, TLC
VARIABLE x
Limit == Print("limit", 5)
ASSUME PrintT("assumption")
Init == PrintT("init") /\ x = 0
A == PrintT(<<"A", x>>) /\ x' = x + 1
B == PrintT(<<"B", x>>) /\ x' = x + 2
Next == A \/ B
Inv == x < Limit
====

---- MODULE InvariantError ----
EXTENDS Naturals, TLC
VARIABLE x
Init == PrintT("init") /\ x = 0
Next == PrintT(<<"next", x>>) /\ x' = x + 1
Inv == x \div (3 - x) >= 0
====

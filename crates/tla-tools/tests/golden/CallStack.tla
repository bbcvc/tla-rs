---- MODULE CallStack ----
EXTENDS Naturals, TLC
VARIABLE x
Init == PrintT("init") /\ x = 0
Ratio(a) == 10 \div (2 - a)
Next == /\ PrintT(<<"next", x>>)
        /\ x < 5 /\ x' = x + 1 /\ x' = Ratio(x) - Ratio(x) + x + 1
====

---- MODULE InitCallStack ----
EXTENDS Naturals
VARIABLE x
Limit == 3
Init == \E n \in 0..Limit : x = Limit \div (n - 1)
Next == x' = x
====

---- MODULE Deadlock ----
EXTENDS Naturals
VARIABLE n
Init == n \in {0, 1}
Next == n < 3 /\ n' = n + 1
====

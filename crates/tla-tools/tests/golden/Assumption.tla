---- MODULE Assumption ----
EXTENDS Naturals
CONSTANT N
ASSUME N > 0
ASSUME Small == N < 3
VARIABLE x
Init == x = N
Next == x' = x
====

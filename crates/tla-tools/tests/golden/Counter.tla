---- MODULE Counter ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
IncX == x < 3 /\ x' = x + 1 /\ UNCHANGED y
IncY == y < 2 /\ y' = y + 1 /\ UNCHANGED x
Next == IncX \/ IncY
Inv == x + y < 4
====

---- MODULE MissingModule ----
EXTENDS Naturals, NoSuchModule
VARIABLE x
Init == x = 0
Next == x' = x
====

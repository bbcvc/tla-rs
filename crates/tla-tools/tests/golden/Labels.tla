---- MODULE Labels ----
\* Bulleted actions, comments after them, and a record that TLC breaks across lines.
EXTENDS Naturals
VARIABLES x, y, log
Init == x = 0 /\ y = 0 /\ log = [first |-> "a fairly long string value", second |-> "another long string value", n |-> 0]
A ==
  /\ x < 2
  /\ x' = x + 1
  /\ UNCHANGED <<y, log>>
  \* a comment

B == /\ y < 1
     /\ y' = y + 1   \* trailing
     /\ x' = x
     /\ log' = [log EXCEPT !.n = @ + 1]
Next == A \/ B
Inv == x + y < 3
====

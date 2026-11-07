---- MODULE AliasLasso ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = IF x = 3 THEN 1 ELSE x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == <>(x = 7)
Alias == [now |-> x, next |-> x', level |-> TLCGet("level")]
====

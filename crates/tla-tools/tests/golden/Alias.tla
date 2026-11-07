---- MODULE Alias ----
EXTENDS Naturals, TLC
VARIABLES x, y
Init == PrintT("init") /\ x = 0 /\ y = "a"
Next == PrintT(<<"next", x>>) /\ x' = x + 1 /\ y' = y
Inv == x < 3
Alias == [count |-> x, label |-> y, next |-> x', level |-> TLCGet("level"),
          printed |-> PrintT(<<"alias", x>>), ratio |-> 10 \div (2 - x)]
====

---- MODULE DNL2_Commit ----

EXTENDS DNL2

S1 == SetAsFun({Pair("X", {"X1", "X2"})})
S3 == SetAsFun({Pair("X", {"X1", "X2"}), Pair("Y", {"Y1", "Y2"}), Pair("Z", {"Z1", "Z2"})})

InvNoNonTrivialCommit ==
 ~/\ TIDs = DOMAIN Txns
  /\ \A t \in TIDs: Txns[t].write \union Txns[t].read /= {}
  /\ UNION {Txns[t].write : t \in TIDs} /= {}
  /\ \A t \in TIDs: Coordinator_state[t] = "Commit"

====

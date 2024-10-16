---- MODULE DNL4_MC ----

EXTENDS Apalache, DNL4, TLC

S11 == SetAsFun({Pair("X", {"X1"})})
S12 == SetAsFun({Pair("X", {"X1", "X2"})})
S32 == SetAsFun({Pair("X", {"X1", "X2"}), Pair("Y", {"Y1", "Y2"}), Pair("Z", {"Z1", "Z2"})})

\* For Apalache
CInit ==
  /\ TIDs := {"t1", "t2", "t3"}
  /\ Shards := S32

Invs ==
  /\ InvSafetySteady
  /\ InvRecoverySafety
  /\ InvRecoveryDurability

SpecFault ==
/\ [][ReplicaReplicate("X1")]_vars

====

---- MODULE DNL2_MC ----

EXTENDS Apalache, DNL1, TLC

S1 == SetAsFun({Pair("X", {"X1", "X2"})})
S3 == SetAsFun({Pair("X", {"X1", "X2"}), Pair("Y", {"Y1", "Y2"}), Pair("Z", {"Z1", "Z2"})})

\* For Apalache
CInit ==
  /\ Txns := {"t1", "t2", "t3"}
  /\ Shards := S3

Invs ==
  /\ InvSafetySteady
  /\ InvRecoverySafety
  /\ InvRecoveryDurability

====

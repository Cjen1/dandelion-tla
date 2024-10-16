---- MODULE DNL1_MC ----

EXTENDS DNL1

S11 == SetAsFun({Pair("X", {"X1"})})
S12 == SetAsFun({Pair("X", {"X1", "X2"})})
S32 == SetAsFun({Pair("X", {"X1", "X2"}), Pair("Y", {"Y1", "Y2"}), Pair("Z", {"Z1", "Z2"})})

\* For Apalache
CInit ==
  /\ Txns := {"t1", "t2", "t3"}
  /\ Shards := S32

Invs ==
  /\ InvSafetySteady
  /\ InvRecoverySafety
  /\ InvRecoveryDurability

====

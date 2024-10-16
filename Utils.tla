---- MODULE Utils ----

EXTENDS Apalache, TLC

\* @type: (a, b) => <<a, b>>;
Pair(A,B) == << A,B >>

\* @type: (a->b, a, b) => a->b;
Set(F, k, v) == [x \in {k} \cup DOMAIN F |-> IF x = k THEN v ELSE F[x]]

\* @type: (x -> a) => Set(a);
Range(F) == {F[x] : x \in DOMAIN F}

Transitive(R) == 
LET Es == UNION {{t1, t2} : <<t1, t2>> \in R} IN
\A t1, t2, t3 \in Es: (Pair(t1,t2) \in R /\ Pair(t2, t3) \in R) => Pair(t1, t3) \in R

Irreflexive(R) ==
LET Es == UNION {{t1, t2} : <<t1, t2>> \in R} IN
\A t1 \in Es: Pair(t1, t1) \notin R


====

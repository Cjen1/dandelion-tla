---- MODULE DNL1 ----
\* Based on U2PC

EXTENDS Utils

(*
@typeAlias: key = Str;
@typeAlias: rid = Str;
@typeAlias: tid = Str;
@typeAlias: version = $tid;
@typeAlias: txn = {read: Set($key), write: Set($key)};
@typeAlias: dependencies = $key -> $version;
@typeAlias: logentry = {
  tag : Str, // in {unlocked, redo}
  tid : $tid, version: $version
};
*)
DNL1_ALIAS == TRUE

CONSTANTS
  \* @type: $key -> Set($rid);
  Shards,
  \* @type: Set($tid);
  TIDs

ASSUME \A k1, k2 \in DOMAIN Shards: k1 /= k2 => Shards[k1] \intersect Shards[k2] = {}

\* @type: Set($key);
Keys == DOMAIN Shards
\* @type: Set($rid);
RIDs == UNION Range(Shards)

VARIABLES
  \* @type: $rid -> {version : $version, applied : Set($version), log: $logentry};
  Replicas,
  \* @type: $tid -> Str;
  Coordinator_state,
  \* @type: $tid -> $txn;
  Txns,
  \* @type: $tid -> $dependencies;
  Txn_deps,
  \* @type: Set({tid : $tid, key : $key});
  M_read,
  \* @type: Set({src : $rid, tid : $tid, ver : $version});
  M_read_resp,
  \* @type: Set({tid : $tid, txn : $txn, deps : $dependencies});
  M_lock,
  \* @type: Set({src : $rid, tid : $tid, version : $tid, locked : Bool});
  M_lock_resp,
  \* @type: Set({tid : $tid, apply : Bool});
  M_unlock,
  \* @type: Set({src : $rid, tid : $tid});
  M_unlock_resp

vars == << Replicas, Coordinator_state, Txns, Txn_deps, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp>>
coord_vars == << Coordinator_state, Txns, Txn_deps >>

KeyLookup == [r \in RIDs |-> CHOOSE k \in DOMAIN Shards: r \in Shards[k]]

Unlocked == [tag |-> "unlocked", tid |-> "Init", version |-> "Init"]
Locked(tid, version) == [tag |-> "redo", tid |-> tid, version |-> version]

Init ==
/\ Replicas = [r \in RIDs |-> [version |-> "Init", applied |-> {}, log |-> Unlocked]]
/\ Coordinator_state = [t \in TIDs |-> "Exec"]
/\ Txns = SetAsFun({})
/\ Txn_deps = SetAsFun({})
/\ M_read = {} /\ M_read_resp = {}
/\ M_lock = {} /\ M_lock_resp = {}
/\ M_unlock = {} /\ M_unlock_resp = {}

(* Execution phase: nondeterministically choose written and read keys, send reads *)
CoordExec(t) ==
\E read \in SUBSET Keys: \E write \in SUBSET (Keys \ read):
/\ read \union write /= {}
/\ Coordinator_state[t] = "Exec"
/\ M_read' = M_read \union {[tid |-> t, key |-> k] : k \in read}
/\ Txns' = Set(Txns, t, [read |-> read, write |-> write])
/\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Lock"]
/\ UNCHANGED << Replicas, Txn_deps, M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp >>

ReplicaRead(r) ==
\E m \in M_read:
LET msg == [src |-> r, tid |-> m.tid, ver |-> Replicas[r].version] IN
/\ m.key = KeyLookup[r]
/\ ~\E m1 \in M_read_resp: m1 = msg
/\ M_read_resp' = M_read_resp \union {msg}
/\ UNCHANGED << Replicas, coord_vars, M_read, M_lock, M_lock_resp, M_unlock, M_unlock_resp >>

(* Start of Commit: once all reads return, set dependencies and submit locks for all requests *)
CoordLock(t) ==
/\ Coordinator_state[t] = "Lock"
\* responses for all reads
/\ \E R \in [Txns[t].read -> {m \in M_read_resp: m.tid = t}]: 
   LET read_deps == [k \in Txns[t].read |-> R[k].ver] IN
   /\ \A k \in DOMAIN R: R[k].src \in Shards[k]
   /\ Txn_deps' = Set(Txn_deps, t, read_deps)
   /\ M_lock' = M_lock \union 
        {[tid |-> t, txn |-> Txns[t], deps |-> read_deps]}
   /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Decide"]
/\ UNCHANGED << Replicas, Txns, M_read, M_read_resp, M_lock_resp, M_unlock, M_unlock_resp >>

ReplicaLock(r) ==
\E m \in M_lock:
/\ KeyLookup[r] \in m.txn.read \union m.txn.write
/\ ~\E nm \in M_lock_resp: nm.src = r /\ nm.tid = m.tid
/\ IF /\ Replicas[r].log.tag = "unlocked"
      /\ \/ /\ KeyLookup[r] \in m.txn.read \* read version matches
            /\ Replicas[r].version = m.deps[KeyLookup[r]]
         \/ KeyLookup[r] \in m.txn.write \* No write version check
   THEN /\ Replicas' = [Replicas EXCEPT ![r] = [
              Replicas[r] EXCEPT !.log = 
                Locked(m.tid, IF KeyLookup[r] \in m.txn.read THEN Replicas[r].version ELSE m.tid)
            ]]
        /\ M_lock_resp' = M_lock_resp \union 
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> TRUE]}
   ELSE /\ UNCHANGED Replicas
        /\ M_lock_resp' = M_lock_resp \union 
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> FALSE]}
/\ UNCHANGED << coord_vars, M_read, M_read_resp, M_lock, M_unlock, M_unlock_resp >>

(* Decide point: when all locks return, if all ack and writes use same previous version then commit otherwise abort *)
CoordDecide(t) ==
/\ Coordinator_state[t] = "Decide"
/\ \E R \in [(UNION {Shards[k]:k \in Txns[t].read \union Txns[t].write}) ->
              {m \in M_lock_resp: m.tid = t}]:
   \* Responses are from every replica and for t
   /\ \A r \in DOMAIN R: R[r].src = r /\ R[r].tid = t 
   /\ LET prev_write == [ 
            k \in Txns[t].write |-> 
              R[CHOOSE r \in DOMAIN R: KeyLookup[r] = k].version] IN
      IF 
         \* Locked on all
         /\ \A m \in Range(R): m.locked = TRUE
         \* All writes return same value
         /\ \A k \in Txns[t].write: 
               \A r \in Shards[k]: R[r].version = prev_write[k]
      THEN /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Commit"]
           /\ Txn_deps' = Set(Txn_deps, t, prev_write @@ Txn_deps[t])
           /\ M_unlock' = M_unlock \union {[tid |-> t, apply |-> TRUE]}
      ELSE /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "TryAbort"]
           /\ Txn_deps' = Set(Txn_deps, t, prev_write @@ Txn_deps[t])
           /\ M_unlock' = M_unlock \union {[tid |-> t, apply |-> FALSE]}
/\ UNCHANGED << Replicas, Txns, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock_resp >>

ReplicaUnlock(r) ==
\E m \in M_unlock:
\* locked on m.tid
/\ Replicas[r].log.tag = "redo" /\ Replicas[r].log.tid = m.tid 
/\ IF m.apply
   THEN Replicas' = [Replicas EXCEPT ![r] = [
          version |-> Replicas[r].log.version,
          applied |-> Replicas[r].applied \union {m.tid},
          log |-> Unlocked
        ]]
   ELSE Replicas' = [Replicas EXCEPT ![r] = [Replicas[r] EXCEPT !.log = Unlocked]]
/\ M_unlock_resp' = M_unlock_resp \union {[src |-> r, tid |-> m.tid]}
/\ UNCHANGED << coord_vars, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock >>

(* Once all replicas in any shard unlock and abort, then abort *)
CoordTryAbort(t) ==
/\ Coordinator_state[t] = "TryAbort"
\* All replicas in any relevant shard unlock abort
/\ \E k \in Txns[t].read \union Txns[t].write:
   \A r \in Shards[k]: \/ [src |-> r, tid |-> t] \in M_unlock_resp
                       \/ \E m \in M_lock_resp: /\ m.src = r
                                                /\ m.tid = t
                                                /\ m.locked = FALSE

/\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Abort"]
/\ UNCHANGED << Replicas, Txns, Txn_deps, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp >>

AntiDeadlock ==
/\ \A t \in TIDs: Coordinator_state[t] \in {"Commit", "Abort"}
/\ UNCHANGED vars

Next == 
\/ \E t \in TIDs: \/ CoordExec(t)
                  \/ CoordLock(t)
                  \/ CoordDecide(t)
                  \/ CoordTryAbort(t)
\/ \E r \in RIDs: \/ ReplicaRead(r)
                  \/ ReplicaLock(r)
                  \/ ReplicaUnlock(r)
\/ AntiDeadlock

Spec == Init /\ [][Next]_vars

Serialisability(C) == 
  \/ \A t1, t2 \in C: t1 = t2 \* At most one element => serialisable
  \/ \E R \in SUBSET (C \X C):
     \* R follows observed order
     /\ \A t1, t2 \in C: t1 \in Range(Txn_deps[t2]) => <<t1, t2>> \in R
     \* If two transactions interfere, there is an order
     /\ \A t1, t2 \in C:
        (/\ t1 /= t2
         /\ (Txns[t1].write \union Txns[t1].read) \intersect (Txns[t2].write \union Txns[t2].read) /= {})
        => <<t1, t2>> \in R \/ <<t2, t1>> \in R
     \* Ensure no cycles
     /\ Transitive(R) /\ Irreflexive(R)

CommittedTIDs == {t \in TIDs: Coordinator_state[t] = "Commit"}
InvSafetySteady == /\ \A r \in UNION Range(Shards): 
                      \/ Replicas[r].version = "Init"
                      \/ Coordinator_state[Replicas[r].version] = "Commit"
                   /\ Serialisability(CommittedTIDs)

RecoveryPredicate(t, live) ==
  \A r \in live:
   (KeyLookup[r] \in Txns[t].write \union Txns[t].read)
   => \/ /\ Replicas[r].log.tag = "redo"
         /\ Replicas[r].log.tid = t
      \/ t \in Replicas[r].applied

InvRecoverySafety ==
\A R \in SUBSET RIDs:
LET locked_replicas == {r \in R: Replicas[r].log.tag /= "unlocked"}
    recoverable_txs == {Replicas[r].log.tid : r \in locked_replicas}
    \* Recover if all recovered replicas have it as a log or applied
    commit_recover == {t \in recoverable_txs: RecoveryPredicate(t, R)}
    abort_recover == recoverable_txs \ commit_recover
IN
\* Valid recovery = at least 1 replica per shard
(\A k \in DOMAIN Shards: Shards[k] \intersect R /= {})
=>/\ Serialisability(CommittedTIDs \union commit_recover)

InvRecoveryDurability ==
\A R \in SUBSET RIDs:
LET locked_replicas == {r \in R: Replicas[r].log.tag /= "unlocked"}
    recoverable_txs == {Replicas[r].log.tid : r \in locked_replicas}
    \* Recover if all recovered replicas have it as a log or applied
    commit_recover == {t \in recoverable_txs: RecoveryPredicate(t, R)}
    abort_recover == recoverable_txs \ commit_recover
IN
\* Valid recovery = at least 1 replica per shard
(\A k \in DOMAIN Shards: Shards[k] \intersect R /= {})
=>/\ \A t \in TIDs: /\ Coordinator_state[t] = "Commit" => t \in commit_recover \/ t \notin recoverable_txs
                    /\ Coordinator_state[t] = "Abort" => t \in abort_recover \/ t \notin recoverable_txs

====

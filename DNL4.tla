---- MODULE DNL4 ----
EXTENDS Utils

(*
@typeAlias: key = Str;
@typeAlias: rid = Str;
@typeAlias: tid = Str;
@typeAlias: version = $tid;
@typeAlias: txn = {read: Set($key), write: Set($key)};
@typeAlias: dependencies = $key -> $version;
@typeAlias: logentry = {
  tag : Str, // in {unlocked, redo, undo}
  tid : $tid, version: $version, serialised : Bool
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

Primaries == [k \in DOMAIN Shards |-> (CHOOSE r \in Shards[k]: TRUE)]

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
  \* tag \in {"lock", "validate", "replicate"} required due to broadcast abstraction of messages
  \* @type: Set({tid : $tid, txn : $txn, deps : $dependencies, tag : Str});
  M_lock,
  \* @type: Set({src : $rid, tid : $tid, version : $tid, locked : Bool, ser: Bool});
  M_lock_resp,
  \* @type: Set({tid : $tid, apply : Bool});
  M_unlock,
  \* @type: Set({src : $rid, tid : $tid});
  M_unlock_resp

vars == << Replicas, Coordinator_state, Txns, Txn_deps, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp>>
coord_vars == << Coordinator_state, Txns, Txn_deps >>

KeyLookup == [r \in RIDs |-> CHOOSE k \in DOMAIN Shards: r \in Shards[k]]
IsPrimary == [r \in RIDs |-> Primaries[KeyLookup[r]] = r]
IsBackup == [r \in RIDs |-> Primaries[KeyLookup[r]] /= r]

Unlocked == [tag |-> "unlocked", tid |-> "Init", version |-> "Init", serialised |-> FALSE]
LockedRedo(tid, version, ser) == [tag |-> "redo", tid |-> tid, version |-> version, serialised |-> ser]
LockedUndo(tid, version, ser) == [tag |-> "undo", tid |-> tid, version |-> version, serialised |-> ser]

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
        {[tid |-> t, txn |-> Txns[t], deps |-> read_deps, tag |-> "lock"]}
   /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Validate"]
/\ UNCHANGED << Replicas, Txns, M_read, M_read_resp, M_lock_resp, M_unlock, M_unlock_resp >>

ReplicaLock(r) ==
\E m \in M_lock:
/\ KeyLookup[r] \in m.txn.write /\ m.tag = "lock"
/\ IsPrimary[r]
/\ ~\E nm \in M_lock_resp: nm.src = r /\ nm.tid = m.tid /\ nm.ser = FALSE
/\ IF Replicas[r].log.tag = "unlocked"
   THEN /\ Replicas' = [Replicas EXCEPT ![r] = [
              Replicas[r] EXCEPT !.log = 
                LockedRedo(m.tid,
                           IF KeyLookup[r] \in m.txn.read THEN Replicas[r].version ELSE m.tid,
                           m.tag = "replicate")]]
        /\ M_lock_resp' = M_lock_resp \union 
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> TRUE, ser |-> FALSE]}
   ELSE /\ UNCHANGED Replicas
        /\ M_lock_resp' = M_lock_resp \union 
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> FALSE, ser |-> FALSE]}
/\ UNCHANGED << coord_vars, M_read, M_read_resp, M_lock, M_unlock, M_unlock_resp >>

(* Validate read keys *)
CoordValidate(t) ==
LET write_deps == 
     [k \in Txns[t].write |-> (CHOOSE m \in M_lock_resp: m.tid = t /\ KeyLookup[m.src] = k).version] 
    new_deps == write_deps @@ Txn_deps[t] 
    resp_keys == {KeyLookup[m.src] : m \in {m \in M_lock_resp: m.tid = t}}
    locked_keys == {KeyLookup[m.src] : m \in {m \in M_lock_resp: m.tid = t /\ m.locked}}
IN
/\ Coordinator_state[t] = "Validate"
\* responses for all locks
/\ Txns[t].write = resp_keys
/\ IF Txns[t].write = locked_keys
   THEN /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Decide"]
        /\ M_lock' = M_lock \union 
             {[tid |-> t, txn |-> Txns[t], deps |-> new_deps, tag |-> "validate"]}
        /\ Txn_deps' = Set(Txn_deps, t, new_deps)
        /\ UNCHANGED << M_unlock >>
   ELSE /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Abort"]
        /\ M_unlock' = M_unlock \union {[tid |-> t, apply |-> FALSE]}
        /\ UNCHANGED << Txn_deps, M_lock >>
/\ UNCHANGED << Replicas, Txns, M_read, M_read_resp, M_lock_resp, M_unlock_resp >>

ReplicaValidate(r) ==
\E m \in M_lock:
/\ KeyLookup[r] \in m.txn.read /\ m.tag = "validate" 
/\ IsPrimary[r]
/\ ~\E nm \in M_lock_resp: nm.src = r /\ nm.tid = m.tid /\ nm.ser = FALSE
/\ IF /\ Replicas[r].log.tag = "unlocked"
      /\ Replicas[r].version = m.deps[KeyLookup[r]]
   THEN /\ M_lock_resp' = M_lock_resp \union 
             \* Not actually locked, just denoted as such
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> TRUE, ser |-> FALSE]}
   ELSE /\ M_lock_resp' = M_lock_resp \union 
             {[src |-> r, tid |-> m.tid, version |-> Replicas[r].version, locked |-> FALSE, ser |-> FALSE]}
/\ UNCHANGED << Replicas, coord_vars, M_read, M_read_resp, M_lock, M_unlock, M_unlock_resp >>

(* Decide point: when all primary locks return, if all ack then replicate otherwise abort *)
CoordDecide(t) ==
LET responses == {m \in M_lock_resp: m.tid = t}
    resp_keys == {KeyLookup[m.src] : m \in responses}
IN
/\ Coordinator_state[t] = "Decide"
/\ resp_keys = Txns[t].read \union Txns[t].write \* All locks and validates successful
/\ IF \A m \in responses: m.locked = TRUE
   THEN /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Unlock"]
        /\ M_lock' = M_lock \union {[tid |-> t, txn |-> Txns[t], deps |-> Txn_deps[t], tag |-> "replicate"]}
        /\ UNCHANGED << M_unlock >>
   ELSE /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Abort"]
        /\ M_unlock' = M_unlock \union {[tid |-> t, apply |-> FALSE]}
        /\ UNCHANGED << M_lock >>
/\ UNCHANGED << Replicas, Txn_deps, Txns, M_read, M_read_resp, M_lock_resp, M_unlock_resp >>

ReplicaReplicate(r) ==
\E m \in M_lock:
/\ KeyLookup[r] \in m.txn.write /\ m.tag = "replicate"
/\ \/ IsBackup[r] 
   \/ IsPrimary[r] /\ Replicas[r].log.tag /= "unlocked"
                   /\ Replicas[r].log.tid = m.tid
/\ ~\E nm \in M_lock_resp: nm.src = r /\ nm.tid = m.tid /\ nm.ser = TRUE
/\ Replicas' = [Replicas EXCEPT ![r] = [
        version |-> m.tid,
        applied |-> Replicas[r].applied \union {m.tid},
        log |-> LockedUndo(m.tid, Replicas[r].version, TRUE)
   ]]
/\ M_lock_resp' = M_lock_resp \union 
     {[src |-> r, tid |-> m.tid, version |-> m.tid, locked |-> TRUE, ser |-> TRUE]}
/\ UNCHANGED << coord_vars, M_read, M_read_resp, M_lock, M_unlock, M_unlock_resp >>

CoordUnlock(t) ==
LET ser_responses == {m \in M_lock_resp: m.tid = t /\ m.ser} 
    ser_replicas == {m.src : m \in ser_responses} 
    relevant_writes == UNION {Shards[k] : k \in Txns[t].write} 
    write_backups == {r \in relevant_writes: IsBackup[r]}
IN
/\ Coordinator_state[t] = "Unlock"
\* Response from every backup
/\ write_backups \subseteq ser_replicas
\* Exists a shard which every replica is serialised
/\ Txns[t].write /= {} => \E s \in Txns[t].write: Shards[s] \subseteq ser_replicas
/\ M_unlock' = M_unlock \union {[tid |-> t, apply |-> TRUE]}
/\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Commit"]
/\ UNCHANGED << Replicas, Txns, Txn_deps, M_read, M_read_resp, M_lock, M_lock_resp, M_unlock_resp >>

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

AntiDeadlock ==
/\ \A t \in TIDs: Coordinator_state[t] \in {"Commit", "Abort"}
/\ UNCHANGED vars

Next == 
\/ \E t \in TIDs: \/ CoordExec(t)
                  \/ CoordLock(t)
                  \/ CoordValidate(t)
                  \/ CoordDecide(t)
                  \/ CoordUnlock(t)
\/ \E r \in RIDs: \/ ReplicaRead(r)
                  \/ ReplicaLock(r)
                  \/ ReplicaValidate(r)
                  \/ ReplicaReplicate(r)
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
                      \/ Coordinator_state[Replicas[r].version] \in {"Unlock", "Commit"}
                   /\ Serialisability(CommittedTIDs)

RecoveryPredicate(t, live) == 
/\ \A r \in live:
   (KeyLookup[r] \in Txns[t].write)
   => \/ /\ Replicas[r].log.tag = "redo"
         /\ Replicas[r].log.tid = t
      \/ /\ Replicas[r].log.tag = "undo"
         /\ Replicas[r].log.tid = t
      \/ t \in Replicas[r].applied
/\ Txns[t].write /= {} 
   => \E r \in live: /\ (KeyLookup[r] \in Txns[t].write)
                     /\ Replicas[r].log.tag /= "unlocked"
                     /\ Replicas[r].log.tid = t
                     /\ Replicas[r].log.serialised

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

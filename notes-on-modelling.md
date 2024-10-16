# Notes on modelling in tla+
## Transactions model
During execution action, each transaction coordinator non-deterministically chooses a set of keys to read and write to, and dispatches the relevant read requests
This ensures that the model does not miss any combinations of reads and writes.

## Recovery per step
Dandelion's recovery procedure's uses a unique recovery coordinator (RC) to stop one replica per shard and use these responses to recover the transactions.

Consider some execution which ends in a recovery by the recovery coordinator.
Similar to partial order reduction techniques this can be reordered into the following execution without changing any transitions or state local to an action.

0. Things happen
1. RC broadcasts stop
2. Replicas receive stop, ack and then take no other action
3. RC recovers

Thus, a model where we do this reordering on every execution which ends in a recovery by the recovery coordinator is equivalent to one which has those three steps as an explicitly calculated invariant check.
However, the invariant version has a much smaller state space.

## Abstract receipt of messages

These models do not explicitly model received messages, instead actions are enabled upon enough messages being able to be received.
Since these models use unanimous responses (all eligible responses must exist), the relevant action would not change its result after it is enabled.

Thus although the following is more complete and is required in majority quorum models:
```
\E R \in [Replicas -> Messages]:
\* valid relation
/\ \A r \in DOMAIN R: R[r].src = r 
\* 
/\ DOMAIN R \in Quorums
```

We instead just use the relevant subset of messages.

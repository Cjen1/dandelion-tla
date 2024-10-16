# dandelion-tla

The test suite can be run using `test.sh`.
This checks that each spec (3 transactions, 3 shards with 2 replicas each) can non-trivially (they write to at least one shard) commit every transaction.
It also runs a 10 minute long simulation check for safety and durability.

To run a test manually use `tlc -simulate -workers auto Models/<spec>.tla`.
The `<spec>_MC.tla` tests run the invariant checks and should not produce any violations.
The `<spec>_Commit.tla` tests have an invariant that there is no non-trivial commit states, so should quickly produce such a trace.
Use these specs to examine representative executions.

Notes on the modelling approach are given in [notes-on-modelling](notes-on-modelling.md) file.

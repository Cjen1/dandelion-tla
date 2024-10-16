.PHONY:fast
fast: cpl-fast pappus-fast

.PHONY: all
all: cpl pappus

.PHONY: cpl
cpl: cpl-fast
	tlc CPLModels/ConsLarge.tla -workers auto

.PHONY:cpl-fast
cpl-fast:
	tlc CPLModels/Abort.tla -workers auto || echo "Expected Fail"
	tlc CPLModels/Commit.tla -workers auto || echo "Expected Fail"
	tlc CPLModels/Cons.tla -workers auto

.PHONY: pappus
pappus: pappus-fast
	tlc PappusModels/ConsLarge.tla -workers auto

.PHONY:pappus-fast
pappus-fast:
	tlc PappusModels/Abort.tla -workers auto || echo "Expected Fail"
	tlc PappusModels/Commit.tla -workers auto || echo "Expected Fail"
	tlc PappusModels/Cons.tla -workers auto

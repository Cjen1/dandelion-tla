#!usr/bin/env bash
# 
# requires tlc installed locally

run_expect_timeout() {
  local duration=$1
  shift
  local name=$1
  shift
  local command="$@"

  echo "Running $name"
  output=$(timeout $duration $command)
  local exit_status=$?

  if [ $exit_status -ne 124 ] && [ $exit_status -ne 0 ]; then
    echo "Error: $name ($command) failed with exit status $exit_status"
    echo $output
  else
    echo "'$name' successful"
  fi
}

run_expect_exit() {
  local duration=$1
  shift
  local name=$1
  shift
  local command="$@"

  echo "Running $name..."
  output=$(timeout $duration $command)
  local exit_status=$?

  if [ $exit_status -eq 124 ] && [ $exit_status -ne 0 ]; then
    echo "Error: $name ($command) failed with exit status $exit_status, output sent to $name.error.log"
    echo $output > $name.error.log
  else
    echo "'$name' successful"
  fi
}

run_expect_exit    30s "DNL1 commit" tlc -workers auto -simulate -deadlock Models/DNL1_Commit.tla
run_expect_exit    30s "DNL2 commit" tlc -workers auto -simulate -deadlock Models/DNL2_Commit.tla
run_expect_exit    30s "DNL4 commit" tlc -workers auto -simulate -deadlock Models/DNL4_Commit.tla

run_expect_timeout 10m "DNL1 invs" tlc -workers auto -simulate Models/DNL1_MC.tla
run_expect_timeout 10m "DNL2 invs" tlc -workers auto -simulate Models/DNL2_MC.tla
run_expect_timeout 10m "DNL4 invs" tlc -workers auto -simulate Models/DNL4_MC.tla

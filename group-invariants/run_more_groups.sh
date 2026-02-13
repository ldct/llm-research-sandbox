#!/bin/bash
# Driver script: compute invariants for new orders and check for NEW collisions
# Usage: ./run_more_groups.sh [max_order] [baseline_for_known_collisions]
set -e

cd "$(dirname "$0")"

MAX_ORDER=${1:-200}
BASELINE=${2:-64}
CSV=invariants_data.csv
LOG=run_more_groups.log

cumulative=$(tail -n +2 "$CSV" | wc -l)
last_order=$(tail -n +2 "$CSV" | tail -1 | cut -d, -f1)
start_order=$((last_order + 1))

echo "Starting from order $start_order (cumulative: $cumulative groups, baseline: $BASELINE)" | tee -a "$LOG"
echo "Target: order $MAX_ORDER" | tee -a "$LOG"

for n in $(seq $start_order $MAX_ORDER); do
    output=$(printf 'n:=%d;;\n' "$n" | cat - compute_order.g | gap -q 2>&1)
    
    if [ -z "$output" ]; then
        echo "Order $n: 0 groups (skipped), cumulative $cumulative — PASS" | tee -a "$LOG"
        continue
    fi
    
    num_new=$(echo "$output" | wc -l)
    cumulative=$((cumulative + num_new))
    
    echo "$output" >> "$CSV"
    
    collision_result=$(python3 check_new_collisions.py $BASELINE 2>&1)
    collision_exit=$?
    
    if [ $collision_exit -ne 0 ]; then
        echo "Order $n: $num_new groups, cumulative $cumulative — NEW COLLISION" | tee -a "$LOG"
        echo "$collision_result" | tee -a "$LOG"
        exit 1
    fi
    
    echo "Order $n: $num_new groups, cumulative $cumulative — PASS" | tee -a "$LOG"
done

echo "All orders up to $MAX_ORDER passed! $cumulative groups, no new collisions beyond baseline $BASELINE." | tee -a "$LOG"

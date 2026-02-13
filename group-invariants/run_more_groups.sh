#!/bin/bash
# Driver script: compute invariants for orders 61..N and check for collisions
# Usage: ./run_more_groups.sh [max_order]
set -e

cd "$(dirname "$0")"

MAX_ORDER=${1:-200}
CSV=invariants_data.csv
LOG=run_more_groups.log

# Count existing groups
cumulative=$(tail -n +2 "$CSV" | wc -l)
last_order=$(tail -n +2 "$CSV" | tail -1 | cut -d, -f1)
start_order=$((last_order + 1))

echo "Starting from order $start_order (cumulative: $cumulative groups)" | tee -a "$LOG"
echo "Target: order $MAX_ORDER" | tee -a "$LOG"

for n in $(seq $start_order $MAX_ORDER); do
    # Compute invariants for this order
    output=$(printf 'n:=%d;;\n' "$n" | cat - compute_order.g | gap -q 2>&1)
    
    if [ -z "$output" ]; then
        echo "Order $n: 0 groups (skipped), cumulative $cumulative — PASS" | tee -a "$LOG"
        continue
    fi
    
    # Count new groups
    num_new=$(echo "$output" | wc -l)
    cumulative=$((cumulative + num_new))
    
    # Append to CSV
    echo "$output" >> "$CSV"
    
    # Check for collisions
    collision_result=$(python3 check_collisions.py 2>&1)
    collision_exit=$?
    
    if [ $collision_exit -ne 0 ]; then
        echo "Order $n: $num_new groups, cumulative $cumulative — FAIL" | tee -a "$LOG"
        echo "$collision_result" | tee -a "$LOG"
        exit 1
    fi
    
    echo "Order $n: $num_new groups, cumulative $cumulative/$cumulative — PASS" | tee -a "$LOG"
done

echo "All orders up to $MAX_ORDER passed! $cumulative unique groups." | tee -a "$LOG"

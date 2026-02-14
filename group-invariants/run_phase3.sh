#!/bin/bash
set -e

OUTFILE="phase3_invariants.csv"
echo "order,index,t1,t2,t3,t4,t5,t6,t8,t9,t10,t11,t12,t14,t16" > "$OUTFILE"

ORDERS=(81 96 160 162 64 189 192 128)

for n in "${ORDERS[@]}"; do
  echo "$(date '+%H:%M:%S') Computing order $n ..."
  echo "n:=$n;;" | cat - compute_phase3.g | gap -q >> "$OUTFILE" 2>/dev/null
  echo "$(date '+%H:%M:%S') Done order $n"
done

echo "All done. Results in $OUTFILE"

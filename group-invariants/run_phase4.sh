#!/bin/bash
set -e

OUTFILE="phase4_invariants.csv"
echo "order,index,u2,u3,u4,u5,u7,u8,u10,u13,u14,u15,u17,u18,u19,u20" > "$OUTFILE"

# Only orders that still have collisions after phases 1-3
ORDERS=(81 96 160 162 64 189 192 128)

for n in "${ORDERS[@]}"; do
  echo "$(date '+%H:%M:%S') Computing order $n ..."
  echo "n:=$n;;" | cat - compute_phase4.g | gap -q >> "$OUTFILE" 2>/dev/null
  echo "$(date '+%H:%M:%S') Done order $n"
done

echo "All done. Results in $OUTFILE"

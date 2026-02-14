#!/bin/bash
set -e

OUTFILE="structural_invariants.csv"
echo "order,index,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18" > "$OUTFILE"

# All collision orders
ORDERS=(81 100 121 147 169 189 96 160 162 200 64 192 128)

for n in "${ORDERS[@]}"; do
  echo "$(date '+%H:%M:%S') Computing order $n ..."
  echo "n:=$n;;" | cat - compute_structural.g | gap -q >> "$OUTFILE" 2>/dev/null
  echo "$(date '+%H:%M:%S') Done order $n"
done

echo "All done. Results in $OUTFILE"

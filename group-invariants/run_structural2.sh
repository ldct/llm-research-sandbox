#!/bin/bash
set -e

OUTFILE="structural2_invariants.csv"
echo "order,index,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18" > "$OUTFILE"

# Only orders with remaining collisions + others for completeness
ORDERS=(81 100 121 147 169 189 96 160 162 200 64 192 128)

for n in "${ORDERS[@]}"; do
  echo "$(date '+%H:%M:%S') Computing order $n ..."
  echo "n:=$n;;" | cat - compute_structural2.g | gap -q >> "$OUTFILE" 2>/dev/null
  echo "$(date '+%H:%M:%S') Done order $n"
done

echo "All done. Results in $OUTFILE"

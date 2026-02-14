#!/bin/bash
# Run extended invariant computation for all collision orders
set -e

OUTFILE="extended_invariants.csv"
echo "order,index,pe8,pe9,pe11,pe13,pe16,pe25,pe27,pr2,pr3,pr4,pr5,pr7,pr8,pr9,pr11,pr13,mix1,mix2,mix3,mix4,mix5" > "$OUTFILE"

# Collision orders sorted by expected computation time (smallest first)
ORDERS=(81 100 121 147 169 189 96 160 162 200 64 192 128)

for n in "${ORDERS[@]}"; do
  echo "$(date '+%H:%M:%S') Computing order $n ..."
  echo "n:=$n;;" | cat - compute_extended.g | gap -q >> "$OUTFILE" 2>/dev/null
  echo "$(date '+%H:%M:%S') Done order $n"
done

echo "All done. Results in $OUTFILE"

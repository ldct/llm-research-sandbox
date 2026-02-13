# Plan: Extend 8 Invariants to Higher Orders

## Goal

Test whether the 8 O(n²) invariants from `eight_invariants.md` distinguish all groups of order ≤ N, incrementing N from 61 upward until the first collision occurs.

## Approach

1. For each new order n = 61, 62, 63, ...:
   - Compute all 8 invariants for every SmallGroup(n, k)
   - Check the new signatures against all previously computed signatures
   - If a collision is found, stop and report the colliding pair

2. Record results in a table: order, number of groups, cumulative total, pass/fail.

## Implementation

A single GAP script computes invariants for a given order. A driver script loops over orders, appends results to a CSV, and runs a Python collision check after each.

### GAP: compute one order

```gap
# Usage: gap -q compute_order.g <order>
n := <order>;
for k in [1..NumberSmallGroups(n)] do
  G := SmallGroup(n, k);
  elements := AsList(G);
  id := Identity(G);
  inv1:=0; inv3:=0; inv5:=0; inv6:=0; inv13:=0; invA:=0; invB:=0; invC:=0;
  for a in elements do
    a2 := a^2;
    for b in elements do
      ab := a*b;
      if ab = b*a then inv1:=inv1+1; fi;
      if a2 = b^2 then inv3:=inv3+1; fi;
      if a^3 = b^3 then inv5:=inv5+1; fi;
      if a2^2 = b^4 then inv6:=inv6+1; fi;
      if ab^2 = id then inv13:=inv13+1; fi;
      if ab = b*a and a2 = id then invA:=invA+1; fi;
      if ab^5 = id then invB:=invB+1; fi;
      if a^7 = b^7 then invC:=invC+1; fi;
    od;
  od;
  Print(n,",",k,",",IsAbelian(G),",",inv1,",",inv3,",",inv5,",",inv6,",",inv13,",",invA,",",invB,",",invC,"\n");
od;
```

### Python: collision check

After each order, load the full CSV and check for duplicate signatures. Report the first collision found.

## Scalability Notes

- O(n²) per group means order-64 groups take ~4096 pair evaluations each. There are 267 groups of order 64 — manageable.
- Order 128 has 2328 groups with n²=16384 pairs each — ~38M pair evaluations, still feasible.
- The SmallGroups library covers all orders up to 2000 (except 1024).
- **Order 64** (267 groups) and **order 96** (231 groups) are the first large jumps in group count. These are the most likely places for new collisions.

## Expected Output

A log like:

```
Order 61: 1 group, cumulative 313/313 — PASS
Order 62: 2 groups, cumulative 315/315 — PASS
Order 63: 4 groups, cumulative 319/319 — PASS
Order 64: 267 groups, cumulative 586/586 — PASS (or FAIL)
...
Order N: X groups — FAIL: SmallGroup(a,b) collides with SmallGroup(c,d)
```

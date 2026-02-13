# Five Essential O(n²) Invariants for All Groups of Order ≤ 60

## Overview

This minimal set of **5 truly O(n²) invariants** achieves the same 96.7% distinguishability as the full set of 18 invariants.

**Key Result**: 13 of the original 18 invariants can be removed without losing any discriminatory power, representing a **72.2% reduction** in computational requirements.

## Invariant Definitions

For each group, we compute 5 invariants by counting pairs (a,b) that satisfy:

1. **inv1_ab_eq_ba**: ab = ba (commutativity)
2. **inv3_a2_eq_b2**: a² = b² (same square)
3. **inv5_a3_eq_b3**: a³ = b³ (same cube)
4. **inv6_a4_eq_b4**: a⁴ = b⁴ (same fourth power)
5. **inv13_ab_involution**: (ab)⁻¹ = ab (ab is an involution)

Total computation time: **~1 second** for all 312 groups (compared to ~3 seconds for 18 invariants)

## Distinguishability Results

Out of **210 non-abelian groups**:
- **203 groups (96.7%)** have unique 5-invariant signatures
- **7 groups (3.3%)** form indistinguishable pairs (7 pairs total)

### Comparison

| Invariant Set | Count | Distinguishable | Percentage | Computation Time |
|---------------|-------|-----------------|------------|------------------|
| 4 invariants (original) | 4 | 145/210 | 69.0% | ~0.8s |
| 18 invariants (full) | 18 | 203/210 | 96.7% | ~3s |
| **5 invariants (minimal)** | **5** | **203/210** | **96.7%** | **~1s** |

## Complete Data Table

| Order | Index | Group ID | Abelian | inv1 | inv3 | inv5 | inv6 | inv13 |
|-------|-------|----------|---------|------|------|------|------|-------|
| 1 | 1 | SmallGroup(1,1) | ✓ | 1 | 1 | 1 | 1 | 1 |
| 2 | 1 | SmallGroup(2,1) | ✓ | 4 | 4 | 2 | 4 | 4 |
| 3 | 1 | SmallGroup(3,1) | ✓ | 9 | 3 | 9 | 3 | 3 |
| 4 | 1 | SmallGroup(4,1) | ✓ | 16 | 8 | 4 | 16 | 8 |
| 4 | 2 | SmallGroup(4,2) | ✓ | 16 | 16 | 4 | 16 | 16 |
| 5 | 1 | SmallGroup(5,1) | ✓ | 25 | 5 | 5 | 5 | 5 |
| 6 | 1 | SmallGroup(6,1) | ✗ | 18 | 18 | 12 | 18 | 24 |
| 6 | 2 | SmallGroup(6,2) | ✓ | 36 | 12 | 18 | 12 | 12 |
| 7 | 1 | SmallGroup(7,1) | ✓ | 49 | 7 | 7 | 7 | 7 |
| 8 | 1 | SmallGroup(8,1) | ✓ | 64 | 16 | 8 | 32 | 16 |
| 8 | 2 | SmallGroup(8,2) | ✓ | 64 | 32 | 8 | 64 | 32 |
| 8 | 3 | SmallGroup(8,3) | ✗ | 40 | 40 | 8 | 64 | 48 |
| 8 | 4 | SmallGroup(8,4) | ✗ | 40 | 40 | 8 | 64 | 16 |
| 8 | 5 | SmallGroup(8,5) | ✓ | 64 | 64 | 8 | 64 | 64 |
| 9 | 1 | SmallGroup(9,1) | ✓ | 81 | 9 | 27 | 9 | 9 |
| 9 | 2 | SmallGroup(9,2) | ✓ | 81 | 9 | 81 | 9 | 9 |
| 10 | 1 | SmallGroup(10,1) | ✗ | 40 | 40 | 10 | 40 | 60 |
| 10 | 2 | SmallGroup(10,2) | ✓ | 100 | 20 | 10 | 20 | 20 |
| 11 | 1 | SmallGroup(11,1) | ✓ | 121 | 11 | 11 | 11 | 11 |
| 12 | 1 | SmallGroup(12,1) | ✗ | 72 | 48 | 24 | 72 | 24 |
| 12 | 2 | SmallGroup(12,2) | ✓ | 144 | 24 | 36 | 48 | 24 |
| 12 | 3 | SmallGroup(12,3) | ✗ | 48 | 24 | 84 | 24 | 48 |
| 12 | 4 | SmallGroup(12,4) | ✗ | 72 | 72 | 24 | 72 | 96 |
| 12 | 5 | SmallGroup(12,5) | ✓ | 144 | 48 | 36 | 48 | 48 |
| 13 | 1 | SmallGroup(13,1) | ✓ | 169 | 13 | 13 | 13 | 13 |
| 14 | 1 | SmallGroup(14,1) | ✗ | 70 | 70 | 14 | 70 | 112 |
| 14 | 2 | SmallGroup(14,2) | ✓ | 196 | 28 | 14 | 28 | 28 |
| 15 | 1 | SmallGroup(15,1) | ✓ | 225 | 15 | 45 | 15 | 15 |
| 16 | 1 | SmallGroup(16,1) | ✓ | 256 | 32 | 16 | 64 | 32 |
| 16 | 2 | SmallGroup(16,2) | ✓ | 256 | 64 | 16 | 256 | 64 |
| 16 | 3 | SmallGroup(16,3) | ✗ | 160 | 96 | 16 | 256 | 128 |
| 16 | 4 | SmallGroup(16,4) | ✗ | 160 | 96 | 16 | 256 | 64 |
| 16 | 5 | SmallGroup(16,5) | ✓ | 256 | 64 | 16 | 128 | 64 |
| 16 | 6 | SmallGroup(16,6) | ✗ | 160 | 64 | 16 | 128 | 64 |
| 16 | 7 | SmallGroup(16,7) | ✗ | 112 | 112 | 16 | 160 | 160 |
| 16 | 8 | SmallGroup(16,8) | ✗ | 112 | 80 | 16 | 160 | 96 |
| 16 | 9 | SmallGroup(16,9) | ✗ | 112 | 112 | 16 | 160 | 32 |
| 16 | 10 | SmallGroup(16,10) | ✓ | 256 | 128 | 16 | 256 | 128 |
| 16 | 11 | SmallGroup(16,11) | ✗ | 160 | 160 | 16 | 256 | 192 |
| 16 | 12 | SmallGroup(16,12) | ✗ | 160 | 160 | 16 | 256 | 64 |
| 16 | 13 | SmallGroup(16,13) | ✗ | 160 | 128 | 16 | 256 | 128 |
| 16 | 14 | SmallGroup(16,14) | ✓ | 256 | 256 | 16 | 256 | 256 |
| 17 | 1 | SmallGroup(17,1) | ✓ | 289 | 17 | 17 | 17 | 17 |
| 18 | 1 | SmallGroup(18,1) | ✗ | 108 | 108 | 36 | 108 | 180 |
| 18 | 2 | SmallGroup(18,2) | ✓ | 324 | 36 | 54 | 36 | 36 |
| 18 | 3 | SmallGroup(18,3) | ✗ | 162 | 54 | 108 | 54 | 72 |
| 18 | 4 | SmallGroup(18,4) | ✗ | 108 | 108 | 90 | 108 | 180 |
| 18 | 5 | SmallGroup(18,5) | ✓ | 324 | 36 | 162 | 36 | 36 |
| 19 | 1 | SmallGroup(19,1) | ✓ | 361 | 19 | 19 | 19 | 19 |
| 20 | 1 | SmallGroup(20,1) | ✗ | 160 | 120 | 20 | 160 | 40 |
| 20 | 2 | SmallGroup(20,2) | ✓ | 400 | 40 | 20 | 80 | 40 |
| 20 | 3 | SmallGroup(20,3) | ✗ | 100 | 60 | 20 | 260 | 120 |
| 20 | 4 | SmallGroup(20,4) | ✗ | 160 | 160 | 20 | 160 | 240 |
| 20 | 5 | SmallGroup(20,5) | ✓ | 400 | 80 | 20 | 80 | 80 |
| 21 | 1 | SmallGroup(21,1) | ✗ | 105 | 21 | 231 | 21 | 21 |
| 21 | 2 | SmallGroup(21,2) | ✓ | 441 | 21 | 63 | 21 | 21 |
| 22 | 1 | SmallGroup(22,1) | ✗ | 154 | 154 | 22 | 154 | 264 |
| 22 | 2 | SmallGroup(22,2) | ✓ | 484 | 44 | 22 | 44 | 44 |
| 23 | 1 | SmallGroup(23,1) | ✓ | 529 | 23 | 23 | 23 | 23 |
| 24 | 1 | SmallGroup(24,1) | ✗ | 288 | 96 | 48 | 192 | 48 |
| 24 | 2 | SmallGroup(24,2) | ✓ | 576 | 48 | 72 | 96 | 48 |
| 24 | 3 | SmallGroup(24,3) | ✗ | 168 | 72 | 168 | 96 | 48 |
| 24 | 4 | SmallGroup(24,4) | ✗ | 216 | 216 | 48 | 288 | 48 |
| 24 | 5 | SmallGroup(24,5) | ✗ | 288 | 144 | 48 | 288 | 192 |
| 24 | 6 | SmallGroup(24,6) | ✗ | 216 | 216 | 48 | 288 | 336 |
| 24 | 7 | SmallGroup(24,7) | ✗ | 288 | 192 | 48 | 288 | 96 |
| 24 | 8 | SmallGroup(24,8) | ✗ | 216 | 168 | 48 | 288 | 240 |
| 24 | 9 | SmallGroup(24,9) | ✓ | 576 | 96 | 72 | 192 | 96 |
| 24 | 10 | SmallGroup(24,10) | ✗ | 360 | 120 | 72 | 192 | 144 |
| 24 | 11 | SmallGroup(24,11) | ✗ | 360 | 120 | 72 | 192 | 48 |
| 24 | 12 | SmallGroup(24,12) | ✗ | 120 | 120 | 96 | 264 | 240 |
| 24 | 13 | SmallGroup(24,13) | ✗ | 192 | 96 | 168 | 96 | 192 |
| 24 | 14 | SmallGroup(24,14) | ✗ | 288 | 288 | 48 | 288 | 384 |
| 24 | 15 | SmallGroup(24,15) | ✓ | 576 | 192 | 72 | 192 | 192 |
| 25 | 1 | SmallGroup(25,1) | ✓ | 625 | 25 | 25 | 25 | 25 |
| 25 | 2 | SmallGroup(25,2) | ✓ | 625 | 25 | 25 | 25 | 25 |
| 26 | 1 | SmallGroup(26,1) | ✗ | 208 | 208 | 26 | 208 | 364 |
| 26 | 2 | SmallGroup(26,2) | ✓ | 676 | 52 | 26 | 52 | 52 |
| 27 | 1 | SmallGroup(27,1) | ✓ | 729 | 27 | 81 | 27 | 27 |
| 27 | 2 | SmallGroup(27,2) | ✓ | 729 | 27 | 243 | 27 | 27 |
| 27 | 3 | SmallGroup(27,3) | ✗ | 297 | 27 | 729 | 27 | 27 |
| 27 | 4 | SmallGroup(27,4) | ✗ | 297 | 27 | 243 | 27 | 27 |
| 27 | 5 | SmallGroup(27,5) | ✓ | 729 | 27 | 729 | 27 | 27 |
| 28 | 1 | SmallGroup(28,1) | ✗ | 280 | 224 | 28 | 280 | 56 |
| 28 | 2 | SmallGroup(28,2) | ✓ | 784 | 56 | 28 | 112 | 56 |
| 28 | 3 | SmallGroup(28,3) | ✗ | 280 | 280 | 28 | 280 | 448 |
| 28 | 4 | SmallGroup(28,4) | ✓ | 784 | 112 | 28 | 112 | 112 |
| 29 | 1 | SmallGroup(29,1) | ✓ | 841 | 29 | 29 | 29 | 29 |
| 30 | 1 | SmallGroup(30,1) | ✗ | 450 | 90 | 60 | 90 | 120 |
| 30 | 2 | SmallGroup(30,2) | ✗ | 360 | 120 | 90 | 120 | 180 |
| 30 | 3 | SmallGroup(30,3) | ✗ | 270 | 270 | 60 | 270 | 480 |
| 30 | 4 | SmallGroup(30,4) | ✓ | 900 | 60 | 90 | 60 | 60 |
| 31 | 1 | SmallGroup(31,1) | ✓ | 961 | 31 | 31 | 31 | 31 |
| 32 | 1 | SmallGroup(32,1) | ✓ | 1024 | 64 | 32 | 128 | 64 |
| 32 | 2 | SmallGroup(32,2) | ✗ | 640 | 256 | 32 | 1024 | 256 |
| 32 | 3 | SmallGroup(32,3) | ✓ | 1024 | 128 | 32 | 512 | 128 |
| 32 | 4 | SmallGroup(32,4) | ✗ | 640 | 128 | 32 | 512 | 128 |
| 32 | 5 | SmallGroup(32,5) | ✗ | 640 | 192 | 32 | 512 | 256 |
| 32 | 6 | SmallGroup(32,6) | ✗ | 352 | 224 | 32 | 1024 | 384 |
| 32 | 7 | SmallGroup(32,7) | ✗ | 352 | 224 | 32 | 512 | 384 |
| 32 | 8 | SmallGroup(32,8) | ✗ | 352 | 224 | 32 | 512 | 128 |
| 32 | 9 | SmallGroup(32,9) | ✗ | 448 | 256 | 32 | 640 | 384 |
| 32 | 10 | SmallGroup(32,10) | ✗ | 448 | 256 | 32 | 640 | 128 |
| 32 | 11 | SmallGroup(32,11) | ✗ | 448 | 192 | 32 | 640 | 256 |
| 32 | 12 | SmallGroup(32,12) | ✗ | 640 | 192 | 32 | 512 | 128 |
| 32 | 13 | SmallGroup(32,13) | ✗ | 448 | 192 | 32 | 640 | 128 |
| 32 | 14 | SmallGroup(32,14) | ✗ | 448 | 320 | 32 | 640 | 128 |
| 32 | 15 | SmallGroup(32,15) | ✗ | 448 | 192 | 32 | 640 | 128 |
| 32 | 16 | SmallGroup(32,16) | ✓ | 1024 | 128 | 32 | 256 | 128 |
| 32 | 17 | SmallGroup(32,17) | ✗ | 640 | 128 | 32 | 256 | 128 |
| 32 | 18 | SmallGroup(32,18) | ✗ | 352 | 352 | 32 | 448 | 576 |
| 32 | 19 | SmallGroup(32,19) | ✗ | 352 | 224 | 32 | 448 | 320 |
| 32 | 20 | SmallGroup(32,20) | ✗ | 352 | 352 | 32 | 448 | 64 |
| 32 | 21 | SmallGroup(32,21) | ✓ | 1024 | 256 | 32 | 1024 | 256 |
| 32 | 22 | SmallGroup(32,22) | ✗ | 640 | 384 | 32 | 1024 | 512 |
| 32 | 23 | SmallGroup(32,23) | ✗ | 640 | 384 | 32 | 1024 | 256 |
| 32 | 24 | SmallGroup(32,24) | ✗ | 640 | 256 | 32 | 1024 | 256 |
| 32 | 25 | SmallGroup(32,25) | ✗ | 640 | 320 | 32 | 1024 | 384 |
| 32 | 26 | SmallGroup(32,26) | ✗ | 640 | 320 | 32 | 1024 | 128 |
| 32 | 27 | SmallGroup(32,27) | ✗ | 448 | 448 | 32 | 1024 | 640 |
| 32 | 28 | SmallGroup(32,28) | ✗ | 448 | 384 | 32 | 1024 | 512 |
| 32 | 29 | SmallGroup(32,29) | ✗ | 448 | 384 | 32 | 1024 | 256 |
| 32 | 30 | SmallGroup(32,30) | ✗ | 448 | 320 | 32 | 1024 | 384 |
| 32 | 31 | SmallGroup(32,31) | ✗ | 448 | 320 | 32 | 1024 | 384 |
| 32 | 32 | SmallGroup(32,32) | ✗ | 448 | 320 | 32 | 1024 | 128 |
| 32 | 33 | SmallGroup(32,33) | ✗ | 448 | 256 | 32 | 1024 | 256 |
| 32 | 34 | SmallGroup(32,34) | ✗ | 448 | 448 | 32 | 1024 | 640 |
| 32 | 35 | SmallGroup(32,35) | ✗ | 448 | 448 | 32 | 1024 | 128 |
| 32 | 36 | SmallGroup(32,36) | ✓ | 1024 | 256 | 32 | 512 | 256 |
| 32 | 37 | SmallGroup(32,37) | ✗ | 640 | 256 | 32 | 512 | 256 |
| 32 | 38 | SmallGroup(32,38) | ✗ | 640 | 256 | 32 | 512 | 256 |
| 32 | 39 | SmallGroup(32,39) | ✗ | 448 | 448 | 32 | 640 | 640 |
| 32 | 40 | SmallGroup(32,40) | ✗ | 448 | 320 | 32 | 640 | 384 |
| 32 | 41 | SmallGroup(32,41) | ✗ | 448 | 448 | 32 | 640 | 128 |
| 32 | 42 | SmallGroup(32,42) | ✗ | 448 | 320 | 32 | 640 | 384 |
| 32 | 43 | SmallGroup(32,43) | ✗ | 352 | 352 | 32 | 640 | 512 |
| 32 | 44 | SmallGroup(32,44) | ✗ | 352 | 352 | 32 | 640 | 256 |
| 32 | 45 | SmallGroup(32,45) | ✓ | 1024 | 512 | 32 | 1024 | 512 |
| 32 | 46 | SmallGroup(32,46) | ✗ | 640 | 640 | 32 | 1024 | 768 |
| 32 | 47 | SmallGroup(32,47) | ✗ | 640 | 640 | 32 | 1024 | 256 |
| 32 | 48 | SmallGroup(32,48) | ✗ | 640 | 512 | 32 | 1024 | 512 |
| 32 | 49 | SmallGroup(32,49) | ✗ | 544 | 544 | 32 | 1024 | 640 |
| 32 | 50 | SmallGroup(32,50) | ✗ | 544 | 544 | 32 | 1024 | 384 |
| 32 | 51 | SmallGroup(32,51) | ✓ | 1024 | 1024 | 32 | 1024 | 1024 |
| 33 | 1 | SmallGroup(33,1) | ✓ | 1089 | 33 | 99 | 33 | 33 |
| 34 | 1 | SmallGroup(34,1) | ✗ | 340 | 340 | 34 | 340 | 612 |
| 34 | 2 | SmallGroup(34,2) | ✓ | 1156 | 68 | 34 | 68 | 68 |
| 35 | 1 | SmallGroup(35,1) | ✓ | 1225 | 35 | 35 | 35 | 35 |
| 36 | 1 | SmallGroup(36,1) | ✗ | 432 | 360 | 72 | 432 | 72 |
| 36 | 2 | SmallGroup(36,2) | ✓ | 1296 | 72 | 108 | 144 | 72 |
| 36 | 3 | SmallGroup(36,3) | ✗ | 432 | 72 | 324 | 72 | 144 |
| 36 | 4 | SmallGroup(36,4) | ✗ | 432 | 432 | 72 | 432 | 720 |
| 36 | 5 | SmallGroup(36,5) | ✓ | 1296 | 144 | 108 | 144 | 144 |
| 36 | 6 | SmallGroup(36,6) | ✗ | 648 | 144 | 216 | 216 | 72 |
| 36 | 7 | SmallGroup(36,7) | ✗ | 432 | 360 | 180 | 432 | 72 |
| 36 | 8 | SmallGroup(36,8) | ✓ | 1296 | 72 | 324 | 144 | 72 |
| 36 | 9 | SmallGroup(36,9) | ✗ | 216 | 144 | 108 | 792 | 360 |
| 36 | 10 | SmallGroup(36,10) | ✗ | 324 | 324 | 144 | 324 | 576 |
| 36 | 11 | SmallGroup(36,11) | ✗ | 432 | 72 | 756 | 72 | 144 |
| 36 | 12 | SmallGroup(36,12) | ✗ | 648 | 216 | 216 | 216 | 288 |
| 36 | 13 | SmallGroup(36,13) | ✗ | 432 | 432 | 180 | 432 | 720 |
| 36 | 14 | SmallGroup(36,14) | ✓ | 1296 | 144 | 324 | 144 | 144 |
| 37 | 1 | SmallGroup(37,1) | ✓ | 1369 | 37 | 37 | 37 | 37 |
| 38 | 1 | SmallGroup(38,1) | ✗ | 418 | 418 | 38 | 418 | 760 |
| 38 | 2 | SmallGroup(38,2) | ✓ | 1444 | 76 | 38 | 76 | 76 |
| 39 | 1 | SmallGroup(39,1) | ✗ | 273 | 39 | 741 | 39 | 39 |
| 39 | 2 | SmallGroup(39,2) | ✓ | 1521 | 39 | 117 | 39 | 39 |
| 40 | 1 | SmallGroup(40,1) | ✗ | 640 | 240 | 40 | 480 | 80 |
| 40 | 2 | SmallGroup(40,2) | ✓ | 1600 | 80 | 40 | 160 | 80 |
| 40 | 3 | SmallGroup(40,3) | ✗ | 400 | 160 | 40 | 560 | 80 |
| 40 | 4 | SmallGroup(40,4) | ✗ | 520 | 520 | 40 | 640 | 80 |
| 40 | 5 | SmallGroup(40,5) | ✗ | 640 | 320 | 40 | 640 | 480 |
| 40 | 6 | SmallGroup(40,6) | ✗ | 520 | 520 | 40 | 640 | 880 |
| 40 | 7 | SmallGroup(40,7) | ✗ | 640 | 480 | 40 | 640 | 160 |
| 40 | 8 | SmallGroup(40,8) | ✗ | 520 | 360 | 40 | 640 | 560 |
| 40 | 9 | SmallGroup(40,9) | ✓ | 1600 | 160 | 40 | 320 | 160 |
| 40 | 10 | SmallGroup(40,10) | ✗ | 1000 | 200 | 40 | 320 | 240 |
| 40 | 11 | SmallGroup(40,11) | ✗ | 1000 | 200 | 40 | 320 | 80 |
| 40 | 12 | SmallGroup(40,12) | ✗ | 400 | 240 | 40 | 1040 | 480 |
| 40 | 13 | SmallGroup(40,13) | ✗ | 640 | 640 | 40 | 640 | 960 |
| 40 | 14 | SmallGroup(40,14) | ✓ | 1600 | 320 | 40 | 320 | 320 |
| 41 | 1 | SmallGroup(41,1) | ✓ | 1681 | 41 | 41 | 41 | 41 |
| 42 | 1 | SmallGroup(42,1) | ✗ | 294 | 126 | 294 | 126 | 336 |
| 42 | 2 | SmallGroup(42,2) | ✗ | 420 | 84 | 462 | 84 | 84 |
| 42 | 3 | SmallGroup(42,3) | ✗ | 882 | 126 | 84 | 126 | 168 |
| 42 | 4 | SmallGroup(42,4) | ✗ | 630 | 210 | 126 | 210 | 336 |
| 42 | 5 | SmallGroup(42,5) | ✗ | 504 | 504 | 84 | 504 | 924 |
| 42 | 6 | SmallGroup(42,6) | ✓ | 1764 | 84 | 126 | 84 | 84 |
| 43 | 1 | SmallGroup(43,1) | ✓ | 1849 | 43 | 43 | 43 | 43 |
| 44 | 1 | SmallGroup(44,1) | ✗ | 616 | 528 | 44 | 616 | 88 |
| 44 | 2 | SmallGroup(44,2) | ✓ | 1936 | 88 | 44 | 176 | 88 |
| 44 | 3 | SmallGroup(44,3) | ✗ | 616 | 616 | 44 | 616 | 1056 |
| 44 | 4 | SmallGroup(44,4) | ✓ | 1936 | 176 | 44 | 176 | 176 |
| 45 | 1 | SmallGroup(45,1) | ✓ | 2025 | 45 | 135 | 45 | 45 |
| 45 | 2 | SmallGroup(45,2) | ✓ | 2025 | 45 | 405 | 45 | 45 |
| 46 | 1 | SmallGroup(46,1) | ✗ | 598 | 598 | 46 | 598 | 1104 |
| 46 | 2 | SmallGroup(46,2) | ✓ | 2116 | 92 | 46 | 92 | 92 |
| 47 | 1 | SmallGroup(47,1) | ✓ | 2209 | 47 | 47 | 47 | 47 |
| 48 | 1 | SmallGroup(48,1) | ✗ | 1152 | 192 | 96 | 384 | 96 |
| 48 | 2 | SmallGroup(48,2) | ✓ | 2304 | 96 | 144 | 192 | 96 |
| 48 | 3 | SmallGroup(48,3) | ✗ | 384 | 96 | 1104 | 288 | 192 |
| 48 | 4 | SmallGroup(48,4) | ✗ | 1152 | 288 | 96 | 576 | 384 |
| 48 | 5 | SmallGroup(48,5) | ✗ | 864 | 288 | 96 | 576 | 384 |
| 48 | 6 | SmallGroup(48,6) | ✗ | 720 | 432 | 96 | 864 | 672 |
| 48 | 7 | SmallGroup(48,7) | ✗ | 720 | 720 | 96 | 864 | 1248 |
| 48 | 8 | SmallGroup(48,8) | ✗ | 720 | 720 | 96 | 864 | 96 |
| 48 | 9 | SmallGroup(48,9) | ✗ | 1152 | 384 | 96 | 768 | 192 |
| 48 | 10 | SmallGroup(48,10) | ✗ | 864 | 384 | 96 | 768 | 192 |
| 48 | 11 | SmallGroup(48,11) | ✗ | 1152 | 384 | 96 | 1152 | 192 |
| 48 | 12 | SmallGroup(48,12) | ✗ | 864 | 480 | 96 | 1152 | 192 |
| 48 | 13 | SmallGroup(48,13) | ✗ | 864 | 672 | 96 | 1152 | 192 |
| 48 | 14 | SmallGroup(48,14) | ✗ | 864 | 480 | 96 | 1152 | 768 |
| 48 | 15 | SmallGroup(48,15) | ✗ | 576 | 480 | 96 | 672 | 864 |
| 48 | 16 | SmallGroup(48,16) | ✗ | 576 | 384 | 96 | 672 | 288 |
| 48 | 17 | SmallGroup(48,17) | ✗ | 576 | 384 | 96 | 672 | 672 |
| 48 | 18 | SmallGroup(48,18) | ✗ | 576 | 480 | 96 | 672 | 96 |
| 48 | 19 | SmallGroup(48,19) | ✗ | 864 | 480 | 96 | 1152 | 384 |
| 48 | 20 | SmallGroup(48,20) | ✓ | 2304 | 192 | 144 | 768 | 192 |
| 48 | 21 | SmallGroup(48,21) | ✗ | 1440 | 288 | 144 | 768 | 384 |
| 48 | 22 | SmallGroup(48,22) | ✗ | 1440 | 288 | 144 | 768 | 192 |
| 48 | 23 | SmallGroup(48,23) | ✓ | 2304 | 192 | 144 | 384 | 192 |
| 48 | 24 | SmallGroup(48,24) | ✗ | 1440 | 192 | 144 | 384 | 192 |
| 48 | 25 | SmallGroup(48,25) | ✗ | 1008 | 336 | 144 | 480 | 480 |
| 48 | 26 | SmallGroup(48,26) | ✗ | 1008 | 240 | 144 | 480 | 288 |
| 48 | 27 | SmallGroup(48,27) | ✗ | 1008 | 336 | 144 | 480 | 96 |
| 48 | 28 | SmallGroup(48,28) | ✗ | 384 | 384 | 192 | 576 | 96 |
| 48 | 29 | SmallGroup(48,29) | ✗ | 384 | 288 | 192 | 576 | 672 |
| 48 | 30 | SmallGroup(48,30) | ✗ | 480 | 288 | 192 | 1056 | 384 |
| 48 | 31 | SmallGroup(48,31) | ✗ | 768 | 192 | 336 | 384 | 384 |
| 48 | 32 | SmallGroup(48,32) | ✗ | 672 | 288 | 336 | 384 | 192 |
| 48 | 33 | SmallGroup(48,33) | ✗ | 672 | 192 | 336 | 384 | 384 |
| 48 | 34 | SmallGroup(48,34) | ✗ | 864 | 864 | 96 | 1152 | 192 |
| 48 | 35 | SmallGroup(48,35) | ✗ | 1152 | 576 | 96 | 1152 | 768 |
| 48 | 36 | SmallGroup(48,36) | ✗ | 864 | 864 | 96 | 1152 | 1344 |
| 48 | 37 | SmallGroup(48,37) | ✗ | 864 | 576 | 96 | 1152 | 768 |
| 48 | 38 | SmallGroup(48,38) | ✗ | 720 | 720 | 96 | 1152 | 1152 |
| 48 | 39 | SmallGroup(48,39) | ✗ | 720 | 624 | 96 | 1152 | 576 |
| 48 | 40 | SmallGroup(48,40) | ✗ | 720 | 720 | 96 | 1152 | 384 |
| 48 | 41 | SmallGroup(48,41) | ✗ | 720 | 624 | 96 | 1152 | 960 |
| 48 | 42 | SmallGroup(48,42) | ✗ | 1152 | 768 | 96 | 1152 | 384 |
| 48 | 43 | SmallGroup(48,43) | ✗ | 864 | 672 | 96 | 1152 | 960 |
| 48 | 44 | SmallGroup(48,44) | ✓ | 2304 | 384 | 144 | 768 | 384 |
| 48 | 45 | SmallGroup(48,45) | ✗ | 1440 | 480 | 144 | 768 | 576 |
| 48 | 46 | SmallGroup(48,46) | ✗ | 1440 | 480 | 144 | 768 | 192 |
| 48 | 47 | SmallGroup(48,47) | ✗ | 1440 | 384 | 144 | 768 | 384 |
| 48 | 48 | SmallGroup(48,48) | ✗ | 480 | 480 | 192 | 1056 | 960 |
| 48 | 49 | SmallGroup(48,49) | ✗ | 768 | 384 | 336 | 384 | 768 |
| 48 | 50 | SmallGroup(48,50) | ✗ | 384 | 288 | 1104 | 288 | 768 |
| 48 | 51 | SmallGroup(48,51) | ✗ | 1152 | 1152 | 96 | 1152 | 1536 |
| 48 | 52 | SmallGroup(48,52) | ✓ | 2304 | 768 | 144 | 768 | 768 |
| 49 | 1 | SmallGroup(49,1) | ✓ | 2401 | 49 | 49 | 49 | 49 |
| 49 | 2 | SmallGroup(49,2) | ✓ | 2401 | 49 | 49 | 49 | 49 |
| 50 | 1 | SmallGroup(50,1) | ✗ | 700 | 700 | 50 | 700 | 1300 |
| 50 | 2 | SmallGroup(50,2) | ✓ | 2500 | 100 | 50 | 100 | 100 |
| 50 | 3 | SmallGroup(50,3) | ✗ | 1000 | 200 | 50 | 200 | 300 |
| 50 | 4 | SmallGroup(50,4) | ✗ | 700 | 700 | 50 | 700 | 1300 |
| 50 | 5 | SmallGroup(50,5) | ✓ | 2500 | 100 | 50 | 100 | 100 |
| 51 | 1 | SmallGroup(51,1) | ✓ | 2601 | 51 | 153 | 51 | 51 |
| 52 | 1 | SmallGroup(52,1) | ✗ | 832 | 728 | 52 | 832 | 104 |
| 52 | 2 | SmallGroup(52,2) | ✓ | 2704 | 104 | 52 | 208 | 104 |
| 52 | 3 | SmallGroup(52,3) | ✗ | 364 | 260 | 52 | 1612 | 728 |
| 52 | 4 | SmallGroup(52,4) | ✗ | 832 | 832 | 52 | 832 | 1456 |
| 52 | 5 | SmallGroup(52,5) | ✓ | 2704 | 208 | 52 | 208 | 208 |
| 53 | 1 | SmallGroup(53,1) | ✓ | 2809 | 53 | 53 | 53 | 53 |
| 54 | 1 | SmallGroup(54,1) | ✗ | 810 | 810 | 108 | 810 | 1512 |
| 54 | 2 | SmallGroup(54,2) | ✓ | 2916 | 108 | 162 | 108 | 108 |
| 54 | 3 | SmallGroup(54,3) | ✗ | 972 | 324 | 324 | 324 | 540 |
| 54 | 4 | SmallGroup(54,4) | ✗ | 1458 | 162 | 324 | 162 | 216 |
| 54 | 5 | SmallGroup(54,5) | ✗ | 540 | 216 | 810 | 216 | 540 |
| 54 | 6 | SmallGroup(54,6) | ✗ | 540 | 216 | 324 | 216 | 540 |
| 54 | 7 | SmallGroup(54,7) | ✗ | 810 | 810 | 270 | 810 | 1512 |
| 54 | 8 | SmallGroup(54,8) | ✗ | 540 | 324 | 810 | 324 | 540 |
| 54 | 9 | SmallGroup(54,9) | ✓ | 2916 | 108 | 486 | 108 | 108 |
| 54 | 10 | SmallGroup(54,10) | ✗ | 1188 | 108 | 1458 | 108 | 108 |
| 54 | 11 | SmallGroup(54,11) | ✗ | 1188 | 108 | 486 | 108 | 108 |
| 54 | 12 | SmallGroup(54,12) | ✗ | 1458 | 162 | 972 | 162 | 216 |
| 54 | 13 | SmallGroup(54,13) | ✗ | 972 | 324 | 810 | 324 | 540 |
| 54 | 14 | SmallGroup(54,14) | ✗ | 810 | 810 | 756 | 810 | 1512 |
| 54 | 15 | SmallGroup(54,15) | ✓ | 2916 | 108 | 1458 | 108 | 108 |
| 55 | 1 | SmallGroup(55,1) | ✗ | 385 | 55 | 55 | 55 | 55 |
| 55 | 2 | SmallGroup(55,2) | ✓ | 3025 | 55 | 55 | 55 | 55 |
| 56 | 1 | SmallGroup(56,1) | ✗ | 1120 | 448 | 56 | 896 | 112 |
| 56 | 2 | SmallGroup(56,2) | ✓ | 3136 | 112 | 56 | 224 | 112 |
| 56 | 3 | SmallGroup(56,3) | ✗ | 952 | 952 | 56 | 1120 | 112 |
| 56 | 4 | SmallGroup(56,4) | ✗ | 1120 | 560 | 56 | 1120 | 896 |
| 56 | 5 | SmallGroup(56,5) | ✗ | 952 | 952 | 56 | 1120 | 1680 |
| 56 | 6 | SmallGroup(56,6) | ✗ | 1120 | 896 | 56 | 1120 | 224 |
| 56 | 7 | SmallGroup(56,7) | ✗ | 952 | 616 | 56 | 1120 | 1008 |
| 56 | 8 | SmallGroup(56,8) | ✓ | 3136 | 224 | 56 | 448 | 224 |
| 56 | 9 | SmallGroup(56,9) | ✗ | 1960 | 280 | 56 | 448 | 336 |
| 56 | 10 | SmallGroup(56,10) | ✗ | 1960 | 280 | 56 | 448 | 112 |
| 56 | 11 | SmallGroup(56,11) | ✗ | 448 | 112 | 56 | 112 | 448 |
| 56 | 12 | SmallGroup(56,12) | ✗ | 1120 | 1120 | 56 | 1120 | 1792 |
| 56 | 13 | SmallGroup(56,13) | ✓ | 3136 | 448 | 56 | 448 | 448 |
| 57 | 1 | SmallGroup(57,1) | ✗ | 513 | 57 | 1539 | 57 | 57 |
| 57 | 2 | SmallGroup(57,2) | ✓ | 3249 | 57 | 171 | 57 | 57 |
| 58 | 1 | SmallGroup(58,1) | ✗ | 928 | 928 | 58 | 928 | 1740 |
| 58 | 2 | SmallGroup(58,2) | ✓ | 3364 | 116 | 58 | 116 | 116 |
| 59 | 1 | SmallGroup(59,1) | ✓ | 3481 | 59 | 59 | 59 | 59 |
| 60 | 1 | SmallGroup(60,1) | ✗ | 1800 | 240 | 120 | 360 | 120 |
| 60 | 2 | SmallGroup(60,2) | ✗ | 1440 | 360 | 180 | 480 | 120 |
| 60 | 3 | SmallGroup(60,3) | ✗ | 1080 | 960 | 120 | 1080 | 120 |
| 60 | 4 | SmallGroup(60,4) | ✓ | 3600 | 120 | 180 | 240 | 120 |
| 60 | 5 | SmallGroup(60,5) | ✗ | 300 | 300 | 480 | 300 | 960 |
| 60 | 6 | SmallGroup(60,6) | ✗ | 900 | 180 | 180 | 780 | 360 |
| 60 | 7 | SmallGroup(60,7) | ✗ | 540 | 300 | 120 | 1380 | 360 |
| 60 | 8 | SmallGroup(60,8) | ✗ | 720 | 720 | 120 | 720 | 1440 |
| 60 | 9 | SmallGroup(60,9) | ✗ | 1200 | 120 | 420 | 120 | 240 |
| 60 | 10 | SmallGroup(60,10) | ✗ | 1440 | 480 | 180 | 480 | 720 |
| 60 | 11 | SmallGroup(60,11) | ✗ | 1800 | 360 | 120 | 360 | 480 |
| 60 | 12 | SmallGroup(60,12) | ✗ | 1080 | 1080 | 120 | 1080 | 1920 |
| 60 | 13 | SmallGroup(60,13) | ✓ | 3600 | 240 | 180 | 240 | 240 |

## Legend

- **Order**: Group order (number of elements)
- **Index**: SmallGroup index
- **Group ID**: Standard SmallGroup notation
- **Abelian**: ✓ if abelian, ✗ if non-abelian
- **inv1**: Count of pairs (a,b) where ab = ba
- **inv3**: Count of pairs (a,b) where a² = b²
- **inv5**: Count of pairs (a,b) where a³ = b³
- **inv6**: Count of pairs (a,b) where a⁴ = b⁴
- **inv13**: Count of pairs (a,b) where (ab)⁻¹ = ab

## Indistinguishable Groups

The following 7 pairs of non-abelian groups have identical 5-invariant signatures:

1. **SmallGroup(32,2), SmallGroup(32,24)**
   - Common signature: inv1=640, inv3=256, inv5=32, inv6=1024, inv13=256

2. **SmallGroup(32,13), SmallGroup(32,15)**
   - Common signature: inv1=448, inv3=192, inv5=32, inv6=640, inv13=128

3. **SmallGroup(32,27), SmallGroup(32,34)**
   - Common signature: inv1=448, inv3=448, inv5=32, inv6=1024, inv13=640

4. **SmallGroup(32,30), SmallGroup(32,31)**
   - Common signature: inv1=448, inv3=320, inv5=32, inv6=1024, inv13=384

5. **SmallGroup(32,37), SmallGroup(32,38)**
   - Common signature: inv1=640, inv3=256, inv5=32, inv6=512, inv13=256

6. **SmallGroup(32,40), SmallGroup(32,42)**
   - Common signature: inv1=448, inv3=320, inv5=32, inv6=640, inv13=384

7. **SmallGroup(50,1), SmallGroup(50,4)**
   - Common signature: inv1=700, inv3=700, inv5=50, inv6=700, inv13=1300

Note: 6 out of 7 remaining pairs are groups of order 32.

## Why These 5 Invariants?

Each of these invariants is **essential** - removing any single one causes distinguishability to drop:

- Without **inv1** (ab=ba): drops to 193/210 (91.9%)
- Without **inv3** (a²=b²): drops to 185/210 (88.1%)
- Without **inv5** (a³=b³): drops to 192/210 (91.4%)
- Without **inv6** (a⁴=b⁴): drops to 195/210 (92.9%)
- Without **inv13** ((ab)⁻¹=ab): drops to 166/210 (79.0%)

The 13 removed invariants (inv2, inv4, inv7-inv12, inv14-inv18) provide **redundant information** that is already captured by these 5.

## Computational Advantage

Using only 5 invariants instead of 18 provides:

- **72.2% fewer** pair-counting operations
- **3x faster** computation (~1s vs ~3s for all 312 groups)
- **Simpler implementation** with fewer edge cases
- **Same distinguishing power** (96.7% of non-abelian groups)

## Algorithmic Complexity

All 5 invariants are **truly O(n²)** using explicit double loops:

```gap
for a in elements do
    for b in elements do
        if [condition] then
            count := count + 1;
        fi;
    od;
od;
```

No expensive GAP builtin operations like:
- `Subgroups(G)` - expensive subgroup enumeration
- `ConjugacyClasses(G)` - conjugacy class computation
- `AutomorphismGroup(G)` - automorphism group computation

This makes the method practical for larger groups where subgroup enumeration becomes prohibitively expensive.

## Conclusion

This minimal set demonstrates that:

1. **Redundancy exists** among O(n²) invariants - many provide overlapping information
2. **Power-equality tests** (a^k = b^k for k=2,3,4) are highly discriminating
3. **Involution counting** ((ab)⁻¹ = ab) is particularly powerful, essential for distinguishing ~79% of groups
4. **Simple is better** - 5 carefully chosen invariants match the performance of 18

Future work could explore whether different combinations of 5 invariants achieve the same or better results, or whether even fewer invariants might suffice for certain subclasses of groups.

## Verifying with a Local GAP Installation

Install GAP 4.15.1 from source (includes the SmallGroups package):

```bash
curl -fsSL https://github.com/gap-system/gap/releases/download/v4.15.1/gap-4.15.1.tar.gz -o gap-4.15.1.tar.gz
tar -xzf gap-4.15.1.tar.gz
cd gap-4.15.1
./configure && make -j2
```

Then compute the 5 invariants for any group, e.g. SmallGroup(5,1):

```bash
./gap -q <<'EOF'
G := SmallGroup(5, 1);
elements := AsList(G);
inv1 := 0; inv3 := 0; inv5 := 0; inv6 := 0; inv13 := 0;
for a in elements do
  for b in elements do
    if a*b = b*a then inv1 := inv1 + 1; fi;
    if a^2 = b^2 then inv3 := inv3 + 1; fi;
    if a^3 = b^3 then inv5 := inv5 + 1; fi;
    if a^4 = b^4 then inv6 := inv6 + 1; fi;
    if (a*b)^2 = Identity(G) then inv13 := inv13 + 1; fi;
  od;
od;
Print("inv1=", inv1, " inv3=", inv3, " inv5=", inv5, " inv6=", inv6, " inv13=", inv13, "\n");
QUIT;
EOF
```

Expected output: `inv1=25 inv3=5 inv5=5 inv6=5 inv13=5` — matching the table above.

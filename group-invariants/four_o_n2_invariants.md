# Four O(n²) Invariants for All Groups of Order ≤ 60

## Invariant Definitions

For each group, we compute 4 truly O(n²) invariants:

1. **inv1_ab_eq_ba**: Count of pairs (a,b) where ab = ba (commutativity)
2. **inv2_a2b_eq_b2a**: Count of pairs (a,b) where a²b = b²a (square compatibility)
3. **inv3_a2_eq_b2**: Count of pairs (a,b) where a² = b² (same square)
4. **inv4_conj_is_inv**: Count of pairs (a,b) where a⁻¹ba = b⁻¹ (conjugate equals inverse)

Total computation time: **~3 seconds** for all 312 groups

## Distinguishability Results

Out of **210 non-abelian groups**:
- **145 groups (69.0%)** have unique 4-invariant signatures
- **65 groups (31.0%)** share signatures with other groups (46 indistinguishable sets)

When combined with fast O(n) properties (exponent, center_size, derived_subgroup_size, etc.),
the success rate increases to **98.6%** (207/210 groups distinguishable).

## Indistinguishable Groups (by 4 O(n²) invariants alone)

The following 46 sets of groups have identical values for all 4 invariants:

### Pair 1: Order 8
**Groups**: SmallGroup(8,3), SmallGroup(8,4)

**Common signature**:
- ab=ba: 40
- a²b=b²a: 8
- a²=b²: 40
- a⁻¹ba=b⁻¹: 40

### Pair 2: Order 16
**Groups**: SmallGroup(16,3), SmallGroup(16,4)

**Common signature**:
- ab=ba: 160
- a²b=b²a: 16
- a²=b²: 96
- a⁻¹ba=b⁻¹: 96

### Pair 3: Order 16
**Groups**: SmallGroup(16,7), SmallGroup(16,9)

**Common signature**:
- ab=ba: 112
- a²b=b²a: 16
- a²=b²: 112
- a⁻¹ba=b⁻¹: 112

### Pair 4: Order 16
**Groups**: SmallGroup(16,11), SmallGroup(16,12)

**Common signature**:
- ab=ba: 160
- a²b=b²a: 16
- a²=b²: 160
- a⁻¹ba=b⁻¹: 160

### Pair 5: Order 18
**Groups**: SmallGroup(18,1), SmallGroup(18,4)

**Common signature**:
- ab=ba: 108
- a²b=b²a: 18
- a²=b²: 108
- a⁻¹ba=b⁻¹: 108

### Pair 6: Order 24
**Groups**: SmallGroup(24,4), SmallGroup(24,6)

**Common signature**:
- ab=ba: 216
- a²b=b²a: 24
- a²=b²: 216
- a⁻¹ba=b⁻¹: 216

### Pair 7: Order 24
**Groups**: SmallGroup(24,10), SmallGroup(24,11)

**Common signature**:
- ab=ba: 360
- a²b=b²a: 24
- a²=b²: 120
- a⁻¹ba=b⁻¹: 120

### Pair 8: Order 27
**Groups**: SmallGroup(27,3), SmallGroup(27,4)

**Common signature**:
- ab=ba: 297
- a²b=b²a: 27
- a²=b²: 27
- a⁻¹ba=b⁻¹: 27

### Quadruple 9: Order 32
**Groups**: SmallGroup(32,2), SmallGroup(32,24), SmallGroup(32,37), SmallGroup(32,38)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 256
- a⁻¹ba=b⁻¹: 256

### Pair 10: Order 32
**Groups**: SmallGroup(32,4), SmallGroup(32,17)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 128
- a⁻¹ba=b⁻¹: 128

### Pair 11: Order 32
**Groups**: SmallGroup(32,5), SmallGroup(32,12)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 192
- a⁻¹ba=b⁻¹: 192

### Quadruple 12: Order 32
**Groups**: SmallGroup(32,6), SmallGroup(32,7), SmallGroup(32,8), SmallGroup(32,19)

**Common signature**:
- ab=ba: 352
- a²b=b²a: 32
- a²=b²: 224
- a⁻¹ba=b⁻¹: 224

### Triple 13: Order 32
**Groups**: SmallGroup(32,9), SmallGroup(32,10), SmallGroup(32,33)

**Common signature**:
- ab=ba: 448
- a²b=b²a: 32
- a²=b²: 256
- a⁻¹ba=b⁻¹: 256

### Triple 14: Order 32
**Groups**: SmallGroup(32,11), SmallGroup(32,13), SmallGroup(32,15)

**Common signature**:
- ab=ba: 448
- a²b=b²a: 32
- a²=b²: 192
- a⁻¹ba=b⁻¹: 192

### 6-tuple 15: Order 32
**Groups**: SmallGroup(32,14), SmallGroup(32,30), SmallGroup(32,31), SmallGroup(32,32), SmallGroup(32,40), SmallGroup(32,42)

**Common signature**:
- ab=ba: 448
- a²b=b²a: 32
- a²=b²: 320
- a⁻¹ba=b⁻¹: 320

### Quadruple 16: Order 32
**Groups**: SmallGroup(32,18), SmallGroup(32,20), SmallGroup(32,43), SmallGroup(32,44)

**Common signature**:
- ab=ba: 352
- a²b=b²a: 32
- a²=b²: 352
- a⁻¹ba=b⁻¹: 352

### Pair 17: Order 32
**Groups**: SmallGroup(32,22), SmallGroup(32,23)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 384
- a⁻¹ba=b⁻¹: 384

### Pair 18: Order 32
**Groups**: SmallGroup(32,25), SmallGroup(32,26)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 320
- a⁻¹ba=b⁻¹: 320

### Quintuple 19: Order 32
**Groups**: SmallGroup(32,27), SmallGroup(32,34), SmallGroup(32,35), SmallGroup(32,39), SmallGroup(32,41)

**Common signature**:
- ab=ba: 448
- a²b=b²a: 32
- a²=b²: 448
- a⁻¹ba=b⁻¹: 448

### Pair 20: Order 32
**Groups**: SmallGroup(32,28), SmallGroup(32,29)

**Common signature**:
- ab=ba: 448
- a²b=b²a: 32
- a²=b²: 384
- a⁻¹ba=b⁻¹: 384

### Pair 21: Order 32
**Groups**: SmallGroup(32,46), SmallGroup(32,47)

**Common signature**:
- ab=ba: 640
- a²b=b²a: 32
- a²=b²: 640
- a⁻¹ba=b⁻¹: 640

### Pair 22: Order 32
**Groups**: SmallGroup(32,49), SmallGroup(32,50)

**Common signature**:
- ab=ba: 544
- a²b=b²a: 32
- a²=b²: 544
- a⁻¹ba=b⁻¹: 544

### Pair 23: Order 36
**Groups**: SmallGroup(36,1), SmallGroup(36,7)

**Common signature**:
- ab=ba: 432
- a²b=b²a: 36
- a²=b²: 360
- a⁻¹ba=b⁻¹: 360

### Pair 24: Order 36
**Groups**: SmallGroup(36,3), SmallGroup(36,11)

**Common signature**:
- ab=ba: 432
- a²b=b²a: 108
- a²=b²: 72
- a⁻¹ba=b⁻¹: 72

### Pair 25: Order 36
**Groups**: SmallGroup(36,4), SmallGroup(36,13)

**Common signature**:
- ab=ba: 432
- a²b=b²a: 36
- a²=b²: 432
- a⁻¹ba=b⁻¹: 432

### Pair 26: Order 40
**Groups**: SmallGroup(40,4), SmallGroup(40,6)

**Common signature**:
- ab=ba: 520
- a²b=b²a: 40
- a²=b²: 520
- a⁻¹ba=b⁻¹: 520

### Pair 27: Order 40
**Groups**: SmallGroup(40,10), SmallGroup(40,11)

**Common signature**:
- ab=ba: 1000
- a²b=b²a: 40
- a²=b²: 200
- a⁻¹ba=b⁻¹: 200

### Quadruple 28: Order 48
**Groups**: SmallGroup(48,7), SmallGroup(48,8), SmallGroup(48,38), SmallGroup(48,40)

**Common signature**:
- ab=ba: 720
- a²b=b²a: 48
- a²=b²: 720
- a⁻¹ba=b⁻¹: 720

### Pair 29: Order 48
**Groups**: SmallGroup(48,9), SmallGroup(48,11)

**Common signature**:
- ab=ba: 1152
- a²b=b²a: 48
- a²=b²: 384
- a⁻¹ba=b⁻¹: 384

### Triple 30: Order 48
**Groups**: SmallGroup(48,12), SmallGroup(48,14), SmallGroup(48,19)

**Common signature**:
- ab=ba: 864
- a²b=b²a: 48
- a²=b²: 480
- a⁻¹ba=b⁻¹: 480

### Pair 31: Order 48
**Groups**: SmallGroup(48,13), SmallGroup(48,43)

**Common signature**:
- ab=ba: 864
- a²b=b²a: 48
- a²=b²: 672
- a⁻¹ba=b⁻¹: 672

### Pair 32: Order 48
**Groups**: SmallGroup(48,15), SmallGroup(48,18)

**Common signature**:
- ab=ba: 576
- a²b=b²a: 48
- a²=b²: 480
- a⁻¹ba=b⁻¹: 480

### Pair 33: Order 48
**Groups**: SmallGroup(48,16), SmallGroup(48,17)

**Common signature**:
- ab=ba: 576
- a²b=b²a: 48
- a²=b²: 384
- a⁻¹ba=b⁻¹: 384

### Pair 34: Order 48
**Groups**: SmallGroup(48,21), SmallGroup(48,22)

**Common signature**:
- ab=ba: 1440
- a²b=b²a: 48
- a²=b²: 288
- a⁻¹ba=b⁻¹: 288

### Pair 35: Order 48
**Groups**: SmallGroup(48,25), SmallGroup(48,27)

**Common signature**:
- ab=ba: 1008
- a²b=b²a: 48
- a²=b²: 336
- a⁻¹ba=b⁻¹: 336

### Pair 36: Order 48
**Groups**: SmallGroup(48,34), SmallGroup(48,36)

**Common signature**:
- ab=ba: 864
- a²b=b²a: 48
- a²=b²: 864
- a⁻¹ba=b⁻¹: 864

### Pair 37: Order 48
**Groups**: SmallGroup(48,39), SmallGroup(48,41)

**Common signature**:
- ab=ba: 720
- a²b=b²a: 48
- a²=b²: 624
- a⁻¹ba=b⁻¹: 624

### Pair 38: Order 48
**Groups**: SmallGroup(48,45), SmallGroup(48,46)

**Common signature**:
- ab=ba: 1440
- a²b=b²a: 48
- a²=b²: 480
- a⁻¹ba=b⁻¹: 480

### Pair 39: Order 50
**Groups**: SmallGroup(50,1), SmallGroup(50,4)

**Common signature**:
- ab=ba: 700
- a²b=b²a: 50
- a²=b²: 700
- a⁻¹ba=b⁻¹: 700

### Triple 40: Order 54
**Groups**: SmallGroup(54,1), SmallGroup(54,7), SmallGroup(54,14)

**Common signature**:
- ab=ba: 810
- a²b=b²a: 54
- a²=b²: 810
- a⁻¹ba=b⁻¹: 810

### Pair 41: Order 54
**Groups**: SmallGroup(54,3), SmallGroup(54,13)

**Common signature**:
- ab=ba: 972
- a²b=b²a: 54
- a²=b²: 324
- a⁻¹ba=b⁻¹: 324

### Pair 42: Order 54
**Groups**: SmallGroup(54,4), SmallGroup(54,12)

**Common signature**:
- ab=ba: 1458
- a²b=b²a: 54
- a²=b²: 162
- a⁻¹ba=b⁻¹: 162

### Pair 43: Order 54
**Groups**: SmallGroup(54,5), SmallGroup(54,6)

**Common signature**:
- ab=ba: 540
- a²b=b²a: 54
- a²=b²: 216
- a⁻¹ba=b⁻¹: 216

### Pair 44: Order 54
**Groups**: SmallGroup(54,10), SmallGroup(54,11)

**Common signature**:
- ab=ba: 1188
- a²b=b²a: 54
- a²=b²: 108
- a⁻¹ba=b⁻¹: 108

### Pair 45: Order 56
**Groups**: SmallGroup(56,3), SmallGroup(56,5)

**Common signature**:
- ab=ba: 952
- a²b=b²a: 56
- a²=b²: 952
- a⁻¹ba=b⁻¹: 952

### Pair 46: Order 56
**Groups**: SmallGroup(56,9), SmallGroup(56,10)

**Common signature**:
- ab=ba: 1960
- a²b=b²a: 56
- a²=b²: 280
- a⁻¹ba=b⁻¹: 280

## Data Table

| Order | Index | Group ID | Abelian | ab=ba | a²b=b²a | a²=b² | a⁻¹ba=b⁻¹ |
|-------|-------|----------|---------|-------|---------|-------|------------|
| 1 | 1 | SmallGroup(1,1) | ✓ | 1 | 1 | 1 | 1 |
| 2 | 1 | SmallGroup(2,1) | ✓ | 4 | 2 | 4 | 4 |
| 3 | 1 | SmallGroup(3,1) | ✓ | 9 | 3 | 3 | 3 |
| 4 | 1 | SmallGroup(4,1) | ✓ | 16 | 4 | 8 | 8 |
| 4 | 2 | SmallGroup(4,2) | ✓ | 16 | 4 | 16 | 16 |
| 5 | 1 | SmallGroup(5,1) | ✓ | 25 | 5 | 5 | 5 |
| 6 | 1 | SmallGroup(6,1) | ✗ | 18 | 6 | 18 | 18 |
| 6 | 2 | SmallGroup(6,2) | ✓ | 36 | 6 | 12 | 12 |
| 7 | 1 | SmallGroup(7,1) | ✓ | 49 | 7 | 7 | 7 |
| 8 | 1 | SmallGroup(8,1) | ✓ | 64 | 8 | 16 | 16 |
| 8 | 2 | SmallGroup(8,2) | ✓ | 64 | 8 | 32 | 32 |
| 8 | 3 | SmallGroup(8,3) | ✗ | 40 | 8 | 40 | 40 |
| 8 | 4 | SmallGroup(8,4) | ✗ | 40 | 8 | 40 | 40 |
| 8 | 5 | SmallGroup(8,5) | ✓ | 64 | 8 | 64 | 64 |
| 9 | 1 | SmallGroup(9,1) | ✓ | 81 | 9 | 9 | 9 |
| 9 | 2 | SmallGroup(9,2) | ✓ | 81 | 9 | 9 | 9 |
| 10 | 1 | SmallGroup(10,1) | ✗ | 40 | 10 | 40 | 40 |
| 10 | 2 | SmallGroup(10,2) | ✓ | 100 | 10 | 20 | 20 |
| 11 | 1 | SmallGroup(11,1) | ✓ | 121 | 11 | 11 | 11 |
| 12 | 1 | SmallGroup(12,1) | ✗ | 72 | 12 | 48 | 48 |
| 12 | 2 | SmallGroup(12,2) | ✓ | 144 | 12 | 24 | 24 |
| 12 | 3 | SmallGroup(12,3) | ✗ | 48 | 36 | 24 | 24 |
| 12 | 4 | SmallGroup(12,4) | ✗ | 72 | 12 | 72 | 72 |
| 12 | 5 | SmallGroup(12,5) | ✓ | 144 | 12 | 48 | 48 |
| 13 | 1 | SmallGroup(13,1) | ✓ | 169 | 13 | 13 | 13 |
| 14 | 1 | SmallGroup(14,1) | ✗ | 70 | 14 | 70 | 70 |
| 14 | 2 | SmallGroup(14,2) | ✓ | 196 | 14 | 28 | 28 |
| 15 | 1 | SmallGroup(15,1) | ✓ | 225 | 15 | 15 | 15 |
| 16 | 1 | SmallGroup(16,1) | ✓ | 256 | 16 | 32 | 32 |
| 16 | 2 | SmallGroup(16,2) | ✓ | 256 | 16 | 64 | 64 |
| 16 | 3 | SmallGroup(16,3) | ✗ | 160 | 16 | 96 | 96 |
| 16 | 4 | SmallGroup(16,4) | ✗ | 160 | 16 | 96 | 96 |
| 16 | 5 | SmallGroup(16,5) | ✓ | 256 | 16 | 64 | 64 |
| 16 | 6 | SmallGroup(16,6) | ✗ | 160 | 16 | 64 | 64 |
| 16 | 7 | SmallGroup(16,7) | ✗ | 112 | 16 | 112 | 112 |
| 16 | 8 | SmallGroup(16,8) | ✗ | 112 | 16 | 80 | 80 |
| 16 | 9 | SmallGroup(16,9) | ✗ | 112 | 16 | 112 | 112 |
| 16 | 10 | SmallGroup(16,10) | ✓ | 256 | 16 | 128 | 128 |
| 16 | 11 | SmallGroup(16,11) | ✗ | 160 | 16 | 160 | 160 |
| 16 | 12 | SmallGroup(16,12) | ✗ | 160 | 16 | 160 | 160 |
| 16 | 13 | SmallGroup(16,13) | ✗ | 160 | 16 | 128 | 128 |
| 16 | 14 | SmallGroup(16,14) | ✓ | 256 | 16 | 256 | 256 |
| 17 | 1 | SmallGroup(17,1) | ✓ | 289 | 17 | 17 | 17 |
| 18 | 1 | SmallGroup(18,1) | ✗ | 108 | 18 | 108 | 108 |
| 18 | 2 | SmallGroup(18,2) | ✓ | 324 | 18 | 36 | 36 |
| 18 | 3 | SmallGroup(18,3) | ✗ | 162 | 18 | 54 | 54 |
| 18 | 4 | SmallGroup(18,4) | ✗ | 108 | 18 | 108 | 108 |
| 18 | 5 | SmallGroup(18,5) | ✓ | 324 | 18 | 36 | 36 |
| 19 | 1 | SmallGroup(19,1) | ✓ | 361 | 19 | 19 | 19 |
| 20 | 1 | SmallGroup(20,1) | ✗ | 160 | 20 | 120 | 120 |
| 20 | 2 | SmallGroup(20,2) | ✓ | 400 | 20 | 40 | 40 |
| 20 | 3 | SmallGroup(20,3) | ✗ | 100 | 40 | 60 | 60 |
| 20 | 4 | SmallGroup(20,4) | ✗ | 160 | 20 | 160 | 160 |
| 20 | 5 | SmallGroup(20,5) | ✓ | 400 | 20 | 80 | 80 |
| 21 | 1 | SmallGroup(21,1) | ✗ | 105 | 21 | 21 | 21 |
| 21 | 2 | SmallGroup(21,2) | ✓ | 441 | 21 | 21 | 21 |
| 22 | 1 | SmallGroup(22,1) | ✗ | 154 | 22 | 154 | 154 |
| 22 | 2 | SmallGroup(22,2) | ✓ | 484 | 22 | 44 | 44 |
| 23 | 1 | SmallGroup(23,1) | ✓ | 529 | 23 | 23 | 23 |
| 24 | 1 | SmallGroup(24,1) | ✗ | 288 | 24 | 96 | 96 |
| 24 | 2 | SmallGroup(24,2) | ✓ | 576 | 24 | 48 | 48 |
| 24 | 3 | SmallGroup(24,3) | ✗ | 168 | 72 | 72 | 72 |
| 24 | 4 | SmallGroup(24,4) | ✗ | 216 | 24 | 216 | 216 |
| 24 | 5 | SmallGroup(24,5) | ✗ | 288 | 24 | 144 | 144 |
| 24 | 6 | SmallGroup(24,6) | ✗ | 216 | 24 | 216 | 216 |
| 24 | 7 | SmallGroup(24,7) | ✗ | 288 | 24 | 192 | 192 |
| 24 | 8 | SmallGroup(24,8) | ✗ | 216 | 24 | 168 | 168 |
| 24 | 9 | SmallGroup(24,9) | ✓ | 576 | 24 | 96 | 96 |
| 24 | 10 | SmallGroup(24,10) | ✗ | 360 | 24 | 120 | 120 |
| 24 | 11 | SmallGroup(24,11) | ✗ | 360 | 24 | 120 | 120 |
| 24 | 12 | SmallGroup(24,12) | ✗ | 120 | 48 | 120 | 120 |
| 24 | 13 | SmallGroup(24,13) | ✗ | 192 | 72 | 96 | 96 |
| 24 | 14 | SmallGroup(24,14) | ✗ | 288 | 24 | 288 | 288 |
| 24 | 15 | SmallGroup(24,15) | ✓ | 576 | 24 | 192 | 192 |
| 25 | 1 | SmallGroup(25,1) | ✓ | 625 | 25 | 25 | 25 |
| 25 | 2 | SmallGroup(25,2) | ✓ | 625 | 25 | 25 | 25 |
| 26 | 1 | SmallGroup(26,1) | ✗ | 208 | 26 | 208 | 208 |
| 26 | 2 | SmallGroup(26,2) | ✓ | 676 | 26 | 52 | 52 |
| 27 | 1 | SmallGroup(27,1) | ✓ | 729 | 27 | 27 | 27 |
| 27 | 2 | SmallGroup(27,2) | ✓ | 729 | 27 | 27 | 27 |
| 27 | 3 | SmallGroup(27,3) | ✗ | 297 | 27 | 27 | 27 |
| 27 | 4 | SmallGroup(27,4) | ✗ | 297 | 27 | 27 | 27 |
| 27 | 5 | SmallGroup(27,5) | ✓ | 729 | 27 | 27 | 27 |
| 28 | 1 | SmallGroup(28,1) | ✗ | 280 | 28 | 224 | 224 |
| 28 | 2 | SmallGroup(28,2) | ✓ | 784 | 28 | 56 | 56 |
| 28 | 3 | SmallGroup(28,3) | ✗ | 280 | 28 | 280 | 280 |
| 28 | 4 | SmallGroup(28,4) | ✓ | 784 | 28 | 112 | 112 |
| 29 | 1 | SmallGroup(29,1) | ✓ | 841 | 29 | 29 | 29 |
| 30 | 1 | SmallGroup(30,1) | ✗ | 450 | 30 | 90 | 90 |
| 30 | 2 | SmallGroup(30,2) | ✗ | 360 | 30 | 120 | 120 |
| 30 | 3 | SmallGroup(30,3) | ✗ | 270 | 30 | 270 | 270 |
| 30 | 4 | SmallGroup(30,4) | ✓ | 900 | 30 | 60 | 60 |
| 31 | 1 | SmallGroup(31,1) | ✓ | 961 | 31 | 31 | 31 |
| 32 | 1 | SmallGroup(32,1) | ✓ | 1024 | 32 | 64 | 64 |
| 32 | 2 | SmallGroup(32,2) | ✗ | 640 | 32 | 256 | 256 |
| 32 | 3 | SmallGroup(32,3) | ✓ | 1024 | 32 | 128 | 128 |
| 32 | 4 | SmallGroup(32,4) | ✗ | 640 | 32 | 128 | 128 |
| 32 | 5 | SmallGroup(32,5) | ✗ | 640 | 32 | 192 | 192 |
| 32 | 6 | SmallGroup(32,6) | ✗ | 352 | 32 | 224 | 224 |
| 32 | 7 | SmallGroup(32,7) | ✗ | 352 | 32 | 224 | 224 |
| 32 | 8 | SmallGroup(32,8) | ✗ | 352 | 32 | 224 | 224 |
| 32 | 9 | SmallGroup(32,9) | ✗ | 448 | 32 | 256 | 256 |
| 32 | 10 | SmallGroup(32,10) | ✗ | 448 | 32 | 256 | 256 |
| 32 | 11 | SmallGroup(32,11) | ✗ | 448 | 32 | 192 | 192 |
| 32 | 12 | SmallGroup(32,12) | ✗ | 640 | 32 | 192 | 192 |
| 32 | 13 | SmallGroup(32,13) | ✗ | 448 | 32 | 192 | 192 |
| 32 | 14 | SmallGroup(32,14) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 15 | SmallGroup(32,15) | ✗ | 448 | 32 | 192 | 192 |
| 32 | 16 | SmallGroup(32,16) | ✓ | 1024 | 32 | 128 | 128 |
| 32 | 17 | SmallGroup(32,17) | ✗ | 640 | 32 | 128 | 128 |
| 32 | 18 | SmallGroup(32,18) | ✗ | 352 | 32 | 352 | 352 |
| 32 | 19 | SmallGroup(32,19) | ✗ | 352 | 32 | 224 | 224 |
| 32 | 20 | SmallGroup(32,20) | ✗ | 352 | 32 | 352 | 352 |
| 32 | 21 | SmallGroup(32,21) | ✓ | 1024 | 32 | 256 | 256 |
| 32 | 22 | SmallGroup(32,22) | ✗ | 640 | 32 | 384 | 384 |
| 32 | 23 | SmallGroup(32,23) | ✗ | 640 | 32 | 384 | 384 |
| 32 | 24 | SmallGroup(32,24) | ✗ | 640 | 32 | 256 | 256 |
| 32 | 25 | SmallGroup(32,25) | ✗ | 640 | 32 | 320 | 320 |
| 32 | 26 | SmallGroup(32,26) | ✗ | 640 | 32 | 320 | 320 |
| 32 | 27 | SmallGroup(32,27) | ✗ | 448 | 32 | 448 | 448 |
| 32 | 28 | SmallGroup(32,28) | ✗ | 448 | 32 | 384 | 384 |
| 32 | 29 | SmallGroup(32,29) | ✗ | 448 | 32 | 384 | 384 |
| 32 | 30 | SmallGroup(32,30) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 31 | SmallGroup(32,31) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 32 | SmallGroup(32,32) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 33 | SmallGroup(32,33) | ✗ | 448 | 32 | 256 | 256 |
| 32 | 34 | SmallGroup(32,34) | ✗ | 448 | 32 | 448 | 448 |
| 32 | 35 | SmallGroup(32,35) | ✗ | 448 | 32 | 448 | 448 |
| 32 | 36 | SmallGroup(32,36) | ✓ | 1024 | 32 | 256 | 256 |
| 32 | 37 | SmallGroup(32,37) | ✗ | 640 | 32 | 256 | 256 |
| 32 | 38 | SmallGroup(32,38) | ✗ | 640 | 32 | 256 | 256 |
| 32 | 39 | SmallGroup(32,39) | ✗ | 448 | 32 | 448 | 448 |
| 32 | 40 | SmallGroup(32,40) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 41 | SmallGroup(32,41) | ✗ | 448 | 32 | 448 | 448 |
| 32 | 42 | SmallGroup(32,42) | ✗ | 448 | 32 | 320 | 320 |
| 32 | 43 | SmallGroup(32,43) | ✗ | 352 | 32 | 352 | 352 |
| 32 | 44 | SmallGroup(32,44) | ✗ | 352 | 32 | 352 | 352 |
| 32 | 45 | SmallGroup(32,45) | ✓ | 1024 | 32 | 512 | 512 |
| 32 | 46 | SmallGroup(32,46) | ✗ | 640 | 32 | 640 | 640 |
| 32 | 47 | SmallGroup(32,47) | ✗ | 640 | 32 | 640 | 640 |
| 32 | 48 | SmallGroup(32,48) | ✗ | 640 | 32 | 512 | 512 |
| 32 | 49 | SmallGroup(32,49) | ✗ | 544 | 32 | 544 | 544 |
| 32 | 50 | SmallGroup(32,50) | ✗ | 544 | 32 | 544 | 544 |
| 32 | 51 | SmallGroup(32,51) | ✓ | 1024 | 32 | 1024 | 1024 |
| 33 | 1 | SmallGroup(33,1) | ✓ | 1089 | 33 | 33 | 33 |
| 34 | 1 | SmallGroup(34,1) | ✗ | 340 | 34 | 340 | 340 |
| 34 | 2 | SmallGroup(34,2) | ✓ | 1156 | 34 | 68 | 68 |
| 35 | 1 | SmallGroup(35,1) | ✓ | 1225 | 35 | 35 | 35 |
| 36 | 1 | SmallGroup(36,1) | ✗ | 432 | 36 | 360 | 360 |
| 36 | 2 | SmallGroup(36,2) | ✓ | 1296 | 36 | 72 | 72 |
| 36 | 3 | SmallGroup(36,3) | ✗ | 432 | 108 | 72 | 72 |
| 36 | 4 | SmallGroup(36,4) | ✗ | 432 | 36 | 432 | 432 |
| 36 | 5 | SmallGroup(36,5) | ✓ | 1296 | 36 | 144 | 144 |
| 36 | 6 | SmallGroup(36,6) | ✗ | 648 | 36 | 144 | 144 |
| 36 | 7 | SmallGroup(36,7) | ✗ | 432 | 36 | 360 | 360 |
| 36 | 8 | SmallGroup(36,8) | ✓ | 1296 | 36 | 72 | 72 |
| 36 | 9 | SmallGroup(36,9) | ✗ | 216 | 36 | 144 | 144 |
| 36 | 10 | SmallGroup(36,10) | ✗ | 324 | 36 | 324 | 324 |
| 36 | 11 | SmallGroup(36,11) | ✗ | 432 | 108 | 72 | 72 |
| 36 | 12 | SmallGroup(36,12) | ✗ | 648 | 36 | 216 | 216 |
| 36 | 13 | SmallGroup(36,13) | ✗ | 432 | 36 | 432 | 432 |
| 36 | 14 | SmallGroup(36,14) | ✓ | 1296 | 36 | 144 | 144 |
| 37 | 1 | SmallGroup(37,1) | ✓ | 1369 | 37 | 37 | 37 |
| 38 | 1 | SmallGroup(38,1) | ✗ | 418 | 38 | 418 | 418 |
| 38 | 2 | SmallGroup(38,2) | ✓ | 1444 | 38 | 76 | 76 |
| 39 | 1 | SmallGroup(39,1) | ✗ | 273 | 39 | 39 | 39 |
| 39 | 2 | SmallGroup(39,2) | ✓ | 1521 | 39 | 39 | 39 |
| 40 | 1 | SmallGroup(40,1) | ✗ | 640 | 40 | 240 | 240 |
| 40 | 2 | SmallGroup(40,2) | ✓ | 1600 | 40 | 80 | 80 |
| 40 | 3 | SmallGroup(40,3) | ✗ | 400 | 80 | 160 | 160 |
| 40 | 4 | SmallGroup(40,4) | ✗ | 520 | 40 | 520 | 520 |
| 40 | 5 | SmallGroup(40,5) | ✗ | 640 | 40 | 320 | 320 |
| 40 | 6 | SmallGroup(40,6) | ✗ | 520 | 40 | 520 | 520 |
| 40 | 7 | SmallGroup(40,7) | ✗ | 640 | 40 | 480 | 480 |
| 40 | 8 | SmallGroup(40,8) | ✗ | 520 | 40 | 360 | 360 |
| 40 | 9 | SmallGroup(40,9) | ✓ | 1600 | 40 | 160 | 160 |
| 40 | 10 | SmallGroup(40,10) | ✗ | 1000 | 40 | 200 | 200 |
| 40 | 11 | SmallGroup(40,11) | ✗ | 1000 | 40 | 200 | 200 |
| 40 | 12 | SmallGroup(40,12) | ✗ | 400 | 80 | 240 | 240 |
| 40 | 13 | SmallGroup(40,13) | ✗ | 640 | 40 | 640 | 640 |
| 40 | 14 | SmallGroup(40,14) | ✓ | 1600 | 40 | 320 | 320 |
| 41 | 1 | SmallGroup(41,1) | ✓ | 1681 | 41 | 41 | 41 |
| 42 | 1 | SmallGroup(42,1) | ✗ | 294 | 42 | 126 | 126 |
| 42 | 2 | SmallGroup(42,2) | ✗ | 420 | 42 | 84 | 84 |
| 42 | 3 | SmallGroup(42,3) | ✗ | 882 | 42 | 126 | 126 |
| 42 | 4 | SmallGroup(42,4) | ✗ | 630 | 42 | 210 | 210 |
| 42 | 5 | SmallGroup(42,5) | ✗ | 504 | 42 | 504 | 504 |
| 42 | 6 | SmallGroup(42,6) | ✓ | 1764 | 42 | 84 | 84 |
| 43 | 1 | SmallGroup(43,1) | ✓ | 1849 | 43 | 43 | 43 |
| 44 | 1 | SmallGroup(44,1) | ✗ | 616 | 44 | 528 | 528 |
| 44 | 2 | SmallGroup(44,2) | ✓ | 1936 | 44 | 88 | 88 |
| 44 | 3 | SmallGroup(44,3) | ✗ | 616 | 44 | 616 | 616 |
| 44 | 4 | SmallGroup(44,4) | ✓ | 1936 | 44 | 176 | 176 |
| 45 | 1 | SmallGroup(45,1) | ✓ | 2025 | 45 | 45 | 45 |
| 45 | 2 | SmallGroup(45,2) | ✓ | 2025 | 45 | 45 | 45 |
| 46 | 1 | SmallGroup(46,1) | ✗ | 598 | 46 | 598 | 598 |
| 46 | 2 | SmallGroup(46,2) | ✓ | 2116 | 46 | 92 | 92 |
| 47 | 1 | SmallGroup(47,1) | ✓ | 2209 | 47 | 47 | 47 |
| 48 | 1 | SmallGroup(48,1) | ✗ | 1152 | 48 | 192 | 192 |
| 48 | 2 | SmallGroup(48,2) | ✓ | 2304 | 48 | 96 | 96 |
| 48 | 3 | SmallGroup(48,3) | ✗ | 384 | 144 | 96 | 96 |
| 48 | 4 | SmallGroup(48,4) | ✗ | 1152 | 48 | 288 | 288 |
| 48 | 5 | SmallGroup(48,5) | ✗ | 864 | 48 | 288 | 288 |
| 48 | 6 | SmallGroup(48,6) | ✗ | 720 | 48 | 432 | 432 |
| 48 | 7 | SmallGroup(48,7) | ✗ | 720 | 48 | 720 | 720 |
| 48 | 8 | SmallGroup(48,8) | ✗ | 720 | 48 | 720 | 720 |
| 48 | 9 | SmallGroup(48,9) | ✗ | 1152 | 48 | 384 | 384 |
| 48 | 10 | SmallGroup(48,10) | ✗ | 864 | 48 | 384 | 384 |
| 48 | 11 | SmallGroup(48,11) | ✗ | 1152 | 48 | 384 | 384 |
| 48 | 12 | SmallGroup(48,12) | ✗ | 864 | 48 | 480 | 480 |
| 48 | 13 | SmallGroup(48,13) | ✗ | 864 | 48 | 672 | 672 |
| 48 | 14 | SmallGroup(48,14) | ✗ | 864 | 48 | 480 | 480 |
| 48 | 15 | SmallGroup(48,15) | ✗ | 576 | 48 | 480 | 480 |
| 48 | 16 | SmallGroup(48,16) | ✗ | 576 | 48 | 384 | 384 |
| 48 | 17 | SmallGroup(48,17) | ✗ | 576 | 48 | 384 | 384 |
| 48 | 18 | SmallGroup(48,18) | ✗ | 576 | 48 | 480 | 480 |
| 48 | 19 | SmallGroup(48,19) | ✗ | 864 | 48 | 480 | 480 |
| 48 | 20 | SmallGroup(48,20) | ✓ | 2304 | 48 | 192 | 192 |
| 48 | 21 | SmallGroup(48,21) | ✗ | 1440 | 48 | 288 | 288 |
| 48 | 22 | SmallGroup(48,22) | ✗ | 1440 | 48 | 288 | 288 |
| 48 | 23 | SmallGroup(48,23) | ✓ | 2304 | 48 | 192 | 192 |
| 48 | 24 | SmallGroup(48,24) | ✗ | 1440 | 48 | 192 | 192 |
| 48 | 25 | SmallGroup(48,25) | ✗ | 1008 | 48 | 336 | 336 |
| 48 | 26 | SmallGroup(48,26) | ✗ | 1008 | 48 | 240 | 240 |
| 48 | 27 | SmallGroup(48,27) | ✗ | 1008 | 48 | 336 | 336 |
| 48 | 28 | SmallGroup(48,28) | ✗ | 384 | 96 | 384 | 384 |
| 48 | 29 | SmallGroup(48,29) | ✗ | 384 | 96 | 288 | 288 |
| 48 | 30 | SmallGroup(48,30) | ✗ | 480 | 96 | 288 | 288 |
| 48 | 31 | SmallGroup(48,31) | ✗ | 768 | 144 | 192 | 192 |
| 48 | 32 | SmallGroup(48,32) | ✗ | 672 | 144 | 288 | 288 |
| 48 | 33 | SmallGroup(48,33) | ✗ | 672 | 144 | 192 | 192 |
| 48 | 34 | SmallGroup(48,34) | ✗ | 864 | 48 | 864 | 864 |
| 48 | 35 | SmallGroup(48,35) | ✗ | 1152 | 48 | 576 | 576 |
| 48 | 36 | SmallGroup(48,36) | ✗ | 864 | 48 | 864 | 864 |
| 48 | 37 | SmallGroup(48,37) | ✗ | 864 | 48 | 576 | 576 |
| 48 | 38 | SmallGroup(48,38) | ✗ | 720 | 48 | 720 | 720 |
| 48 | 39 | SmallGroup(48,39) | ✗ | 720 | 48 | 624 | 624 |
| 48 | 40 | SmallGroup(48,40) | ✗ | 720 | 48 | 720 | 720 |
| 48 | 41 | SmallGroup(48,41) | ✗ | 720 | 48 | 624 | 624 |
| 48 | 42 | SmallGroup(48,42) | ✗ | 1152 | 48 | 768 | 768 |
| 48 | 43 | SmallGroup(48,43) | ✗ | 864 | 48 | 672 | 672 |
| 48 | 44 | SmallGroup(48,44) | ✓ | 2304 | 48 | 384 | 384 |
| 48 | 45 | SmallGroup(48,45) | ✗ | 1440 | 48 | 480 | 480 |
| 48 | 46 | SmallGroup(48,46) | ✗ | 1440 | 48 | 480 | 480 |
| 48 | 47 | SmallGroup(48,47) | ✗ | 1440 | 48 | 384 | 384 |
| 48 | 48 | SmallGroup(48,48) | ✗ | 480 | 96 | 480 | 480 |
| 48 | 49 | SmallGroup(48,49) | ✗ | 768 | 144 | 384 | 384 |
| 48 | 50 | SmallGroup(48,50) | ✗ | 384 | 528 | 288 | 288 |
| 48 | 51 | SmallGroup(48,51) | ✗ | 1152 | 48 | 1152 | 1152 |
| 48 | 52 | SmallGroup(48,52) | ✓ | 2304 | 48 | 768 | 768 |
| 49 | 1 | SmallGroup(49,1) | ✓ | 2401 | 49 | 49 | 49 |
| 49 | 2 | SmallGroup(49,2) | ✓ | 2401 | 49 | 49 | 49 |
| 50 | 1 | SmallGroup(50,1) | ✗ | 700 | 50 | 700 | 700 |
| 50 | 2 | SmallGroup(50,2) | ✓ | 2500 | 50 | 100 | 100 |
| 50 | 3 | SmallGroup(50,3) | ✗ | 1000 | 50 | 200 | 200 |
| 50 | 4 | SmallGroup(50,4) | ✗ | 700 | 50 | 700 | 700 |
| 50 | 5 | SmallGroup(50,5) | ✓ | 2500 | 50 | 100 | 100 |
| 51 | 1 | SmallGroup(51,1) | ✓ | 2601 | 51 | 51 | 51 |
| 52 | 1 | SmallGroup(52,1) | ✗ | 832 | 52 | 728 | 728 |
| 52 | 2 | SmallGroup(52,2) | ✓ | 2704 | 52 | 104 | 104 |
| 52 | 3 | SmallGroup(52,3) | ✗ | 364 | 52 | 260 | 260 |
| 52 | 4 | SmallGroup(52,4) | ✗ | 832 | 52 | 832 | 832 |
| 52 | 5 | SmallGroup(52,5) | ✓ | 2704 | 52 | 208 | 208 |
| 53 | 1 | SmallGroup(53,1) | ✓ | 2809 | 53 | 53 | 53 |
| 54 | 1 | SmallGroup(54,1) | ✗ | 810 | 54 | 810 | 810 |
| 54 | 2 | SmallGroup(54,2) | ✓ | 2916 | 54 | 108 | 108 |
| 54 | 3 | SmallGroup(54,3) | ✗ | 972 | 54 | 324 | 324 |
| 54 | 4 | SmallGroup(54,4) | ✗ | 1458 | 54 | 162 | 162 |
| 54 | 5 | SmallGroup(54,5) | ✗ | 540 | 54 | 216 | 216 |
| 54 | 6 | SmallGroup(54,6) | ✗ | 540 | 54 | 216 | 216 |
| 54 | 7 | SmallGroup(54,7) | ✗ | 810 | 54 | 810 | 810 |
| 54 | 8 | SmallGroup(54,8) | ✗ | 540 | 54 | 324 | 324 |
| 54 | 9 | SmallGroup(54,9) | ✓ | 2916 | 54 | 108 | 108 |
| 54 | 10 | SmallGroup(54,10) | ✗ | 1188 | 54 | 108 | 108 |
| 54 | 11 | SmallGroup(54,11) | ✗ | 1188 | 54 | 108 | 108 |
| 54 | 12 | SmallGroup(54,12) | ✗ | 1458 | 54 | 162 | 162 |
| 54 | 13 | SmallGroup(54,13) | ✗ | 972 | 54 | 324 | 324 |
| 54 | 14 | SmallGroup(54,14) | ✗ | 810 | 54 | 810 | 810 |
| 54 | 15 | SmallGroup(54,15) | ✓ | 2916 | 54 | 108 | 108 |
| 55 | 1 | SmallGroup(55,1) | ✗ | 385 | 165 | 55 | 55 |
| 55 | 2 | SmallGroup(55,2) | ✓ | 3025 | 55 | 55 | 55 |
| 56 | 1 | SmallGroup(56,1) | ✗ | 1120 | 56 | 448 | 448 |
| 56 | 2 | SmallGroup(56,2) | ✓ | 3136 | 56 | 112 | 112 |
| 56 | 3 | SmallGroup(56,3) | ✗ | 952 | 56 | 952 | 952 |
| 56 | 4 | SmallGroup(56,4) | ✗ | 1120 | 56 | 560 | 560 |
| 56 | 5 | SmallGroup(56,5) | ✗ | 952 | 56 | 952 | 952 |
| 56 | 6 | SmallGroup(56,6) | ✗ | 1120 | 56 | 896 | 896 |
| 56 | 7 | SmallGroup(56,7) | ✗ | 952 | 56 | 616 | 616 |
| 56 | 8 | SmallGroup(56,8) | ✓ | 3136 | 56 | 224 | 224 |
| 56 | 9 | SmallGroup(56,9) | ✗ | 1960 | 56 | 280 | 280 |
| 56 | 10 | SmallGroup(56,10) | ✗ | 1960 | 56 | 280 | 280 |
| 56 | 11 | SmallGroup(56,11) | ✗ | 448 | 56 | 112 | 112 |
| 56 | 12 | SmallGroup(56,12) | ✗ | 1120 | 56 | 1120 | 1120 |
| 56 | 13 | SmallGroup(56,13) | ✓ | 3136 | 56 | 448 | 448 |
| 57 | 1 | SmallGroup(57,1) | ✗ | 513 | 57 | 57 | 57 |
| 57 | 2 | SmallGroup(57,2) | ✓ | 3249 | 57 | 57 | 57 |
| 58 | 1 | SmallGroup(58,1) | ✗ | 928 | 58 | 928 | 928 |
| 58 | 2 | SmallGroup(58,2) | ✓ | 3364 | 58 | 116 | 116 |
| 59 | 1 | SmallGroup(59,1) | ✓ | 3481 | 59 | 59 | 59 |
| 60 | 1 | SmallGroup(60,1) | ✗ | 1800 | 60 | 240 | 240 |
| 60 | 2 | SmallGroup(60,2) | ✗ | 1440 | 60 | 360 | 360 |
| 60 | 3 | SmallGroup(60,3) | ✗ | 1080 | 60 | 960 | 960 |
| 60 | 4 | SmallGroup(60,4) | ✓ | 3600 | 60 | 120 | 120 |
| 60 | 5 | SmallGroup(60,5) | ✗ | 300 | 180 | 300 | 300 |
| 60 | 6 | SmallGroup(60,6) | ✗ | 900 | 120 | 180 | 180 |
| 60 | 7 | SmallGroup(60,7) | ✗ | 540 | 120 | 300 | 300 |
| 60 | 8 | SmallGroup(60,8) | ✗ | 720 | 60 | 720 | 720 |
| 60 | 9 | SmallGroup(60,9) | ✗ | 1200 | 180 | 120 | 120 |
| 60 | 10 | SmallGroup(60,10) | ✗ | 1440 | 60 | 480 | 480 |
| 60 | 11 | SmallGroup(60,11) | ✗ | 1800 | 60 | 360 | 360 |
| 60 | 12 | SmallGroup(60,12) | ✗ | 1080 | 60 | 1080 | 1080 |
| 60 | 13 | SmallGroup(60,13) | ✓ | 3600 | 60 | 240 | 240 |

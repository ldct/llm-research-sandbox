"""
Quadratic Sieve factorization — self-contained demo.

Usage:
    python quadratic_sieve.py [N]

If no argument is given, a default semiprime is used.
"""

import math
import sys
import time
from random import randint


# ── small helpers ──────────────────────────────────────────────────────────

def isqrt(n):
    """Integer square root."""
    if n < 0:
        raise ValueError
    if n < 2:
        return n
    x = n
    y = (x + 1) // 2
    while y < x:
        x = y
        y = (x + n // x) // 2
    return x


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13):
        if n == p:
            return True
        if n % p == 0:
            return False
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, x, n) if False else pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def small_primes(limit):
    """Sieve of Eratosthenes up to *limit*."""
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i, v in enumerate(sieve) if v]


def tonelli_shanks(n, p):
    """Square root of n mod p (p odd prime). Returns root or None."""
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while True:
        if t == 1:
            return r
        i = 1
        tmp = (t * t) % p
        while tmp != 1:
            tmp = (tmp * tmp) % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, (b * b) % p, (t * b * b) % p, (r * b) % p


# ── GF(2) linear algebra (find null-space vectors) ────────────────────────

def gf2_nullspace(matrix, ncols):
    """
    Given a list of rows (each a list of 0/1 ints of length ncols),
    return vectors in the left null-space over GF(2).
    """
    nrows = len(matrix)
    # augment each row with an identity
    aug = [row[:] + [1 if i == j else 0 for j in range(nrows)]
           for i, row in enumerate(matrix)]
    pivot_col = [None] * ncols
    for col in range(ncols):
        # find pivot
        piv = None
        for row in range(nrows):
            if aug[row][col] == 1 and pivot_col[col] is None:
                piv = row
                break
        if piv is None:
            continue
        pivot_col[col] = piv
        for row in range(nrows):
            if row != piv and aug[row][col] == 1:
                for k in range(len(aug[row])):
                    aug[row][k] ^= aug[piv][k]
    # rows that became zero in the left part are null-space vectors
    results = []
    for i in range(nrows):
        if all(aug[i][c] == 0 for c in range(ncols)):
            vec = aug[i][ncols:]
            results.append(vec)
    return results


# ── Quadratic Sieve ───────────────────────────────────────────────────────

def choose_factor_base_size(n):
    """Heuristic: B ≈ exp(0.5 * sqrt(ln n * ln ln n))."""
    ln_n = math.log(n)
    ln_ln_n = math.log(ln_n)
    B = math.exp(0.5 * math.sqrt(ln_n * ln_ln_n))
    return max(int(B), 30)


def quadratic_sieve(n):
    """Return a non-trivial factor of n, or None on failure."""
    if n % 2 == 0:
        return 2
    if is_prime(n):
        return n

    # check perfect power
    for e in range(2, n.bit_length()):
        r = round(n ** (1.0 / e))
        for c in (r - 1, r, r + 1):
            if c > 1 and c**e == n:
                return c

    sqrt_n = isqrt(n)
    if sqrt_n * sqrt_n == n:
        return sqrt_n

    B = choose_factor_base_size(n)
    primes = small_primes(B)
    # keep only primes where n is a quadratic residue
    factor_base = []
    for p in primes:
        if p == 2:
            factor_base.append(p)
        elif pow(n, (p - 1) // 2, p) == 1:
            factor_base.append(p)

    fb_size = len(factor_base)
    needed = fb_size + 10  # want a few more relations than primes

    # sieve
    sieve_radius = max(fb_size * 30, 10000)
    relations = []  # (x, exponent_vector) where x^2 - n is smooth
    smooth_vals = []  # the actual x values

    # precompute roots
    roots = {}
    for p in factor_base:
        if p == 2:
            roots[2] = [sqrt_n % 2]  # simplified
        else:
            r = tonelli_shanks(n % p, p)
            if r is not None:
                roots[p] = [r, p - r]
            else:
                roots[p] = []

    offset = 0
    while len(relations) < needed:
        # sieve block
        block = sieve_radius
        logs = [0.0] * block
        start = sqrt_n + 1 + offset

        # fill log approximations
        for p in factor_base:
            if p not in roots:
                continue
            logp = math.log(p)
            for r in roots[p]:
                # we need (start + j)^2 ≡ 0 (mod p), i.e. start + j ≡ ±r (mod p)
                begin = (r - (start % p)) % p
                for j in range(begin, block, p):
                    logs[j] += logp
                if p != 2:
                    begin2 = (p - r - (start % p)) % p
                    if begin2 != begin:
                        for j in range(begin2, block, p):
                            logs[j] += logp

        # threshold
        threshold = math.log(n) * 0.5 - 5  # generous
        for j in range(block):
            if logs[j] < threshold:
                continue
            x = start + j
            val = x * x - n
            if val <= 0:
                continue
            # trial divide
            v = val
            exponents = [0] * fb_size
            for idx, p in enumerate(factor_base):
                while v % p == 0:
                    v //= p
                    exponents[idx] += 1
            if v == 1:
                relations.append((x, exponents))
                smooth_vals.append(x)
                if len(relations) >= needed:
                    break
        offset += block

        if offset > sieve_radius * 50:
            # bail — increase B and retry
            return None

    # build matrix mod 2
    matrix = []
    for _, exponents in relations:
        matrix.append([e % 2 for e in exponents])

    null_vecs = gf2_nullspace(matrix, fb_size)

    for vec in null_vecs:
        # combine the relations indicated by vec
        lhs = 1  # product of x_i
        rhs_exp = [0] * fb_size
        for i, bit in enumerate(vec):
            if bit:
                lhs = (lhs * relations[i][0]) % n
                for j in range(fb_size):
                    rhs_exp[j] += relations[i][1][j]
        rhs = 1
        for j in range(fb_size):
            rhs = (rhs * pow(factor_base[j], rhs_exp[j] // 2, n)) % n
        for a, b in ((lhs, rhs), (lhs, n - rhs)):
            g = math.gcd(abs(a - b), n)
            if 1 < g < n:
                return g
    return None


# ── driver ────────────────────────────────────────────────────────────────

def full_factor(n):
    """Recursively factor n into primes."""
    if n <= 1:
        return []
    if is_prime(n):
        return [n]
    d = quadratic_sieve(n)
    if d is None or d == n:
        # fallback: Pollard rho
        d = pollard_rho(n)
    return sorted(full_factor(d) + full_factor(n // d))


def pollard_rho(n):
    """Fallback factoring method."""
    if n % 2 == 0:
        return 2
    while True:
        c = randint(1, n - 1)
        x = y = randint(0, n - 1)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def generate_semiprime(bits):
    """Generate a semiprime of approximately *bits* bits."""
    import random
    half = bits // 2
    while True:
        p = random.getrandbits(half) | (1 << (half - 1)) | 1
        if is_prime(p):
            break
    while True:
        q = random.getrandbits(bits - half) | (1 << (bits - half - 1)) | 1
        if is_prime(q) and q != p:
            break
    return p * q, p, q


def demo():
    print("=" * 60)
    print("  Quadratic Sieve — Demonstration")
    print("=" * 60)

    # Small warm-up examples
    examples = [
        15, 1009 * 1013, 10007 * 10009, 100003 * 100019,
    ]
    for n in examples:
        t0 = time.perf_counter()
        factors = full_factor(n)
        dt = time.perf_counter() - t0
        print(f"\n  n = {n}")
        print(f"  factors = {' × '.join(map(str, factors))}")
        print(f"  time = {dt:.4f}s")

    # Estimate largest factorable in ~5s by binary search on bit-length
    print("\n" + "-" * 60)
    print("  Finding largest semiprime factorable in ~5 seconds...")
    print("-" * 60)

    best_bits = 0
    for bits in range(30, 120, 5):
        n, p, q = generate_semiprime(bits)
        t0 = time.perf_counter()
        factors = full_factor(n)
        dt = time.perf_counter() - t0
        print(f"  {bits:3d} bits | {n} | {dt:.2f}s | {'✓' if dt < 5 else '✗'}")
        assert sorted(factors) == sorted([p, q]), f"Wrong factors for {n}"
        if dt > 5:
            break
        best_bits = bits

    print(f"\n  ➜ Largest factorable in ~5s: ~{best_bits}-bit semiprimes")
    print(f"    (roughly {best_bits // 3}-digit numbers)\n")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        n = int(sys.argv[1])
        t0 = time.perf_counter()
        factors = full_factor(n)
        dt = time.perf_counter() - t0
        print(f"n = {n}")
        print(f"factors = {' × '.join(map(str, factors))}")
        print(f"time = {dt:.4f}s")
    else:
        demo()

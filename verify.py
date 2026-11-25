#!/usr/bin/env python3
"""Verify the six-versus-seven separation using only the Python standard library."""
from collections import Counter
from itertools import combinations

N = 6
PAIRS = tuple(combinations(range(N), 2))
POINTS = range(1 << N)


def target(x):
    a, b, c, d, e, f = x
    return (a*b ^ a*c ^ a*d,
            a*c ^ a*d ^ c*d,
            a*b ^ a*c ^ b*c ^ b*d ^ c*d,
            a*c ^ b*c ^ a*d ^ c*d ^ a*e ^ c*e ^ d*e ^ b*f ^ d*f,
            a*c ^ b*c ^ a*d ^ a*e ^ b*e ^ d*e ^ d*f)


def six(x):
    a, b, c, d, e, f = x
    g1 = (b ^ c ^ d) & (a ^ b ^ c ^ d)
    g2 = (a ^ d) & (c ^ d)
    g3 = (a ^ b ^ d) & (a ^ c ^ d)
    u, v = g1 ^ g2 ^ b ^ c ^ e, g3 ^ a ^ b ^ f
    g4 = u & v
    g5 = (u ^ b ^ d) & (v ^ a ^ c ^ d)
    g6 = (u ^ d) & (v ^ a ^ b ^ d)
    return (g1 ^ b ^ c ^ d, g2 ^ d, g3 ^ a ^ d,
            g4 ^ g5 ^ g3 ^ a ^ b ^ d,
            g4 ^ g6 ^ g1 ^ g2 ^ g3 ^ a ^ b ^ c ^ d)


def seven(x):
    a, b, c, d, e, f = x
    p1 = (b ^ c ^ d) & (a ^ b ^ c ^ d)
    p2 = (a ^ d) & (c ^ d)
    p3 = (a ^ b ^ d) & (a ^ c ^ d)
    p4 = (a ^ b ^ c) & e
    p5 = (b ^ d) & (a ^ b ^ e ^ f)
    p6 = (a ^ b) & (c ^ e)
    p7 = d & (a ^ e ^ f)
    return (p1 ^ b ^ c ^ d, p2 ^ d, p3 ^ a ^ d,
            p3 ^ p4 ^ p5 ^ a ^ b ^ d, p6 ^ p7)


def bits(x):
    return tuple((x >> i) & 1 for i in range(N))


def span(vectors):
    result = {0}
    for v in vectors:
        result |= {w ^ v for w in result}
    return result


def wedge(u, v):
    return sum((((u >> i & 1) * (v >> j & 1)) ^
                ((u >> j & 1) * (v >> i & 1))) << k
               for k, (i, j) in enumerate(PAIRS))


def dimension(space):
    return len(space).bit_length() - 1


def verify():
    for point in POINTS:
        x = bits(point)
        assert six(x) == target(x) == seven(x), x
    print('Both circuits agree with the five quadratic forms on all 64 inputs.')

    # Since target is homogeneous quadratic, evaluation on e_i + e_j
    # extracts the coefficient of x_i x_j directly.
    basis = [sum(target(bits((1 << i) | (1 << j)))[k] << p
                 for p, (i, j) in enumerate(PAIRS)) for k in range(5)]
    W = span(basis)
    R = {wedge(u, v) for u, v in combinations(range(1, 1 << N), 2)}
    assert len(W) == 32 and len(R) == 651 and 0 not in R
    assert W & R == set(basis[:3])
    print('Quadratic coefficient masks:', basis)
    print('dim(W) = 5; nonzero decomposable forms = 651.')

    # Over F_2, each nonzero coset of W gives exactly one 6D superspace.
    seen = set(W)
    histogram = Counter()
    for v in range(1 << len(PAIRS)):
        if v in seen:
            continue
        coset = {v ^ w for w in W}
        seen.update(coset)
        X = W | coset
        histogram[dimension(span(X & R))] += 1
    assert len(seen) == 1 << len(PAIRS)
    assert histogram == {3: 604, 4: 323, 5: 96}
    print('Dimensions of decomposable spans in 1,023 six-dimensional superspaces:')
    print(dict(sorted(histogram.items())))
    print('No superspace is spanned by six decomposable forms.')

    # An independent five-gate obstruction: in any five-gate circuit,
    # the quadratic parts must span W, and all gates must be quadratic.
    # The first gate outside S has inputs in Aff + S. Check those products.
    S = span(basis[:3])
    forms = {}
    for z in W:
        forms[z] = sum((sum((z >> k & 1) * (x >> i & 1) * (x >> j & 1)
                             for k, (i, j) in enumerate(PAIRS)) & 1) << x
                       for x in POINTS)
    affine = {sum((((u & x).bit_count() + c) & 1) << x for x in POINTS)
              for u in POINTS for c in (0, 1)}
    inputs = {forms[z] ^ l for z in S for l in affine}
    forbidden = {forms[z] ^ l for z in W - S for l in affine}
    assert len(inputs) == 1024 and len(forbidden) == 3072
    assert all((p & q) not in forbidden for p in inputs for q in inputs)
    print('No five-gate circuit can leave the initial three-dimensional subspace.')
    print('Verified: MC = 6 < 7 = level-one MC.')


if __name__ == '__main__':
    verify()

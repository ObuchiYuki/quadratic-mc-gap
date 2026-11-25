# Six AND Gates Beat Seven

**A counterexample to quadratic-circuit optimality over \(\mathbb F_2\).**

Can allowing higher-degree intermediate computations make a quadratic Boolean function cheaper to compute?

**Yes.** Five quadratic outputs on six input bits can be computed with six AND gates, but every quadratic circuit needs at least seven. XOR gates are free in this cost model.

$$
\boxed{\mathrm{MC}(Q)=6<7=\mathrm{qMC}(Q)}
$$

This gives a negative answer to the general quadratic-circuit optimality question posed by Mirwald and Schnorr (1992, §5) and revisited by Boyar and Find (2014/2018, §4). Quadratic circuits are known to be optimal for one or two quadratic outputs; the example below shows that this does not extend to arbitrary output families.

## The idea

A circuit need not remain quadratic at every intermediate step just because its final outputs are quadratic. In this example, three cubic intermediate expressions share the same cubic part. Taking their XOR differences cancels that part, yielding two quadratic outputs while saving an AND gate.

| Circuit class | Minimum AND gates |
| :--- | ---: |
| Unrestricted XOR–AND | **6** |
| Quadratic (AND-depth one) | **7** |

The separation concerns exact multiplicative complexity, not just the cost of two particular implementations.

## The counterexample

Write \(x_{ij}=x_i x_j\). All sums are over \(\mathbb F_2\), and the variables are Boolean, so \(x_i^2=x_i\).

The homogeneous quadratic map \(Q:\mathbb F_2^6\to\mathbb F_2^5\) is given by

$$
\begin{aligned}
q_1 &= x_{12}+x_{13}+x_{14},\\
q_2 &= x_{13}+x_{14}+x_{34},\\
q_3 &= x_{12}+x_{13}+x_{23}+x_{24}+x_{34},\\
q_4 &= x_{13}+x_{23}+x_{14}+x_{34}\\
    &\quad+x_{15}+x_{35}+x_{45}+x_{26}+x_{46},\\
q_5 &= x_{13}+x_{23}+x_{14}+x_{15}+x_{25}+x_{45}+x_{46}.
\end{aligned}
$$

### A six-AND circuit

$$
\begin{aligned}
g_1&=(x_2+x_3+x_4)(x_1+x_2+x_3+x_4),\\
g_2&=(x_1+x_4)(x_3+x_4),\\
g_3&=(x_1+x_2+x_4)(x_1+x_3+x_4),\\
a&=g_1+g_2+x_2+x_3+x_5,\\
b&=g_3+x_1+x_2+x_6,\\
g_4&=ab,\\
g_5&=(a+x_2+x_4)(b+x_1+x_3+x_4),\\
g_6&=(a+x_4)(b+x_1+x_2+x_4).
\end{aligned}
$$

Read out the five outputs using XOR only:

$$
\begin{aligned}
q_1&=g_1+x_2+x_3+x_4,\\
q_2&=g_2+x_4,\\
q_3&=g_3+x_1+x_4,\\
q_4&=g_4+g_5+g_3+x_1+x_2+x_4,\\
q_5&=g_4+g_6+g_1+g_2+g_3+x_1+x_2+x_3+x_4.
\end{aligned}
$$

There are exactly six binary AND gates, \(g_1,\ldots,g_6\), and no constants are needed.

## Why seven are necessary in a quadratic circuit

Modulo affine functions, a quadratic Boolean form is an element of the 15-dimensional space \(\Lambda^2\mathbb F_2^6\). Each product of two affine linear forms contributes a decomposable bivector (an alternating form of rank at most two).

Let \(W\) be the five-dimensional space spanned by the quadratic outputs. A quadratic circuit with at most six AND gates would require a subspace of dimension at most six containing \(W\) and spanned by decomposable bivectors. No such subspace exists.

This can be shown algebraically, or verified exhaustively by examining the \(2^{10}-1=1,023\) six-dimensional superspaces of \(W\).

The proof also rules out an unrestricted five-AND circuit and exhibits a quadratic seven-AND circuit. Thus both minima are exact.

## Proof and verification

- [PROOF.md](PROOF.md) — complete mathematical argument, including the equivalence of the two quadratic-circuit complexity definitions and the exact lower bounds.
- [verify.py](verify.py) — standalone exhaustive verifier, using only the Python standard library (Python 3.10+).

Run:

```sh
python3 verify.py
```

The verifier checks both circuits on all 64 inputs, enumerates all 651 nonzero decomposable bivectors and all 1,023 six-dimensional superspaces, and independently excludes five-gate unrestricted circuits.

## Scope

Here MC counts binary AND gates in unrestricted XOR–AND circuits, with free affine operations. qMC counts binary AND gates in circuits where all AND inputs are affine forms in the original variables (level-one or \(\Sigma\Pi\Sigma\) circuits). The same minimum is obtained if all intermediate Boolean functions are required to have degree at most two.

The result is about Boolean functions in the quotient ring \(\mathbb F_2[x_1,\ldots,x_6]/(x_i^2-x_i)\), not formal polynomial computation. It does not establish a separation for bilinear maps or an asymptotically growing gap.

To the best of our knowledge, this is a new counterexample to the general question in the references below. This is a research note, not a peer-reviewed publication.

## References

1. Roland Mirwald and Claus-Peter Schnorr. [The Multiplicative Complexity of Quadratic Boolean Forms](https://www.sciencedirect.com/science/article/pii/0304397592902358). *Theoretical Computer Science* 102(2), 307–328, 1992. See §5.
2. Joan Boyar and Magnus Gausdal Find. [Multiplicative Complexity of Vector Valued Boolean Functions](https://arxiv.org/abs/1407.6169). *Theoretical Computer Science*, 2018. [DOI](https://doi.org/10.1016/j.tcs.2018.02.023). See §4 of the arXiv version.
3. Gregory Morse. [Unrestricted Boolean Multiplicative Complexity of Four-Term Binary Polynomial Multiplication](https://arxiv.org/abs/2608.30238), 2026. Related work on the optimality question for a specific family.

**Keywords:** multiplicative complexity, quadratic Boolean forms, vector-valued Boolean functions, XOR–AND circuits, quadratic circuit optimality, level-one multiplicative complexity, nonlinear feedback, Boolean circuit complexity, alternating forms, Mirwald–Schnorr, Boyar–Find.

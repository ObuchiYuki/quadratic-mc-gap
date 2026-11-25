# Six versus Seven: Proof

## 1. Statement and circuit model

Let $B_n=\mathbb F_2[x_1,\ldots,x_n]/(x_i^2-x_i:1\le i\le n)$ be the Boolean function ring. Every element has a unique square-free algebraic normal form (ANF). Its degree is the degree of that ANF.

An XOR–AND circuit allows free affine operations and binary AND gates. Its multiplicative complexity $\mathrm{MC}$ is the minimum number of AND gates. Write $\mathrm{qMC}$ for the same minimum when the inputs to every AND gate are affine functions of the original inputs. These are level-one, or quadratic $\Sigma\Pi\Sigma$, circuits.

**Theorem.** There is a homogeneous quadratic map $Q:\mathbb F_2^6\to\mathbb F_2^5$ such that

$$
\mathrm{MC}(Q)=6,\qquad \mathrm{qMC}(Q)=7.
$$

The conclusion also holds if quadratic circuits are defined by requiring every intermediate function to have degree at most two (see §6). It therefore answers the general question of Mirwald–Schnorr (1992, §5) and Boyar–Find (2014/2018, §4) in the negative.

## 2. The example and the two upper bounds

Write $x_{ij}=x_ix_j$. The five homogeneous quadratic forms are

$$
\begin{aligned}
q_1&=x_{12}+x_{13}+x_{14},\\
q_2&=x_{13}+x_{14}+x_{34},\\
q_3&=x_{12}+x_{13}+x_{23}+x_{24}+x_{34},\\
q_4&=x_{13}+x_{23}+x_{14}+x_{34}\\
   &\quad+x_{15}+x_{35}+x_{45}+x_{26}+x_{46},\\
q_5&=x_{13}+x_{23}+x_{14}+x_{15}+x_{25}+x_{45}+x_{46}.
\end{aligned}
$$

### Six unrestricted AND gates

Use

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

Direct expansion in $B_6$, with $x_i^2=x_i$, gives

$$
\begin{aligned}
q_1&=g_1+x_2+x_3+x_4,\\
q_2&=g_2+x_4,\\
q_3&=g_3+x_1+x_4,\\
q_4&=g_4+g_5+g_3+x_1+x_2+x_4,\\
q_5&=g_4+g_6+g_1+g_2+g_3+x_1+x_2+x_3+x_4.
\end{aligned}
$$

For clarity, the cubic part shared by $g_4,g_5,g_6$ is

$$
\begin{aligned}
C={}&x_1x_3x_4+x_2x_3x_4+x_1x_2x_5+x_1x_3x_5\\
 &+x_2x_3x_5+x_2x_4x_5+x_3x_4x_5+x_1x_2x_6+x_3x_4x_6.
\end{aligned}
$$

These three gates have degree three, with no quartic terms. Their common cubic part disappears in the output differences. The displayed circuit establishes $\mathrm{MC}(Q)\le6$.

### Seven quadratic AND gates

Let $p_1=g_1$, $p_2=g_2$, $p_3=g_3$ and

$$
\begin{aligned}
p_4&=(x_1+x_2+x_3)x_5,\\
p_5&=(x_2+x_4)(x_1+x_2+x_5+x_6),\\
p_6&=(x_1+x_2)(x_3+x_5),\\
p_7&=x_4(x_1+x_5+x_6).
\end{aligned}
$$

Then

$$
\begin{aligned}
q_1&=p_1+x_2+x_3+x_4,\\
q_2&=p_2+x_4,\\
q_3&=p_3+x_1+x_4,\\
q_4&=p_3+p_4+p_5+x_1+x_2+x_4,\\
q_5&=p_6+p_7.
\end{aligned}
$$

All seven products have linear inputs, establishing $\mathrm{qMC}(Q)\le7$. Both upper-bound circuits use no constant gates.

## 3. Exterior-algebra formulation

Let $V$ be the six-dimensional space of homogeneous linear forms in the input variables. Identify the quadratic parts of Boolean functions with $\Lambda^2 V$, by identifying $x_ix_j$ with $x_i\wedge x_j$ for $i<j$.

Let $R=\{u\wedge v:u,v\in V\}$, including zero. Its nonzero elements are precisely the alternating forms of rank two. Write

$$
W=\langle q_1,q_2,q_3,q_4,q_5\rangle,\qquad
S=\langle q_1,q_2,q_3\rangle.
$$

From now on, quadratic forms in the exterior-algebra argument denote their homogeneous quadratic parts. Since the quadratic part of the product of two affine forms is their linear parts' wedge, the exact level-one cost is

$$
\mathrm{qMC}(Q)=
\min\{t:W\subseteq\langle r_1,\ldots,r_t\rangle,\ r_i\in R\}.
$$

The reverse implication holds because any difference in affine terms can be corrected for free at the outputs.

The space $W$ has dimension five. For example, the coefficient columns $x_{12},x_{34},x_{23},x_{26},x_{25}$ form a lower-triangular $5\times5$ minor with unit diagonal in the displayed output order.

Put $U=\langle x_1,x_2,x_3,x_4\rangle$. Every $z\in W$ has a unique decomposition

$$
z=z_0+x_5\wedge u+x_6\wedge v,\qquad z_0\in\Lambda^2 U,\quad u,v\in U.
$$

In particular, its $x_5\wedge x_6$ coefficient is zero. For the three nonzero cosets of $S$ in $W$, the pairs $(u,v)$ are:

| Coset | $u$ | $v$ |
| :--- | :--- | :--- |
| $q_4+S$ | $x_1+x_3+x_4$ | $x_2+x_4$ |
| $q_5+S$ | $x_1+x_2+x_4$ | $x_4$ |
| $q_4+q_5+S$ | $x_2+x_3$ | $x_2$ |

Each pair is independent. The three planes $P_i=\langle u,v\rangle$ are pairwise disjoint away from zero, as seen by listing their nonzero vectors:

$$
\begin{aligned}
P_1\setminus\{0\}&=\{x_1+x_3+x_4,x_2+x_4,x_1+x_2+x_3\},\\
P_2\setminus\{0\}&=\{x_1+x_2+x_4,x_4,x_1+x_2\},\\
P_3\setminus\{0\}&=\{x_2+x_3,x_2,x_3\}.
\end{aligned}
$$

The alternating matrix of any $z\in W\setminus S$ has block shape

$$
\begin{pmatrix}A&B\\B^{\mathsf T}&0\end{pmatrix},
\qquad B=(u\;\;v).
$$

Since $B$ has rank two, this matrix has rank at least four: a kernel vector $(s,t)$ must satisfy $B^{\mathsf T}s=0$, and $t$ is then uniquely determined by $s$ if it exists. Hence the kernel has dimension at most two.

Consequently, $R\cap W\subseteq S$. Inside $S$, the only nonzero decomposable forms are $q_1,q_2,q_3$: the other four nonzero elements have rank four, as can be checked by the four-variable Pfaffian $c_{12}c_{34}+c_{13}c_{24}+c_{14}c_{23}$. In particular $W$ is not spanned by decomposable forms.

## 4. Six quadratic gates are impossible

We prove this without computer search.

Suppose $W$ is contained in the span of at most six elements of $R$. The span must have dimension six, since the only possible five-dimensional span containing $W$ is $W$ itself, which is not decomposably spanned.

Let this six-dimensional space be $X$. Choose a decomposable $r\in X\setminus W$. Then $X=W+\langle r\rangle$. All decomposable elements of $X$ are either in $R\cap W$ or have the form $r+z\in R$ with $z\in W$.

Project $X$ onto $W/S$ by mapping $w+\epsilon r$ to $w+S$. Because $X$ is spanned by decomposable forms and $R\cap W\subseteq S$, there must be elements $z,z'\in W$ representing two distinct nonzero cosets of $S$ such that

$$
r+z\in R,\qquad r+z'\in R.
$$

We show that no decomposable $r$ has this property.

### Case A: the coefficient of $x_5\wedge x_6$ in $r$ is zero

If $r\in\Lambda^2U$, adding it to any $z\in W\setminus S$ leaves the mixed block $B$ unchanged. The resulting form still has rank at least four.

Otherwise a nonzero decomposable form with zero $x_5\wedge x_6$ coefficient can be written

$$
r=w\wedge(\lambda_5x_5+\lambda_6x_6+\ell),
$$

where $0\ne w\in U$, $\ell\in U$, and $(\lambda_5,\lambda_6)\ne(0,0)$. This follows by projecting the two factors onto $\langle x_5,x_6\rangle$: their projected span is one-dimensional, so one factor can be taken in $U$.

If $r+z$ is decomposable, it also has zero $x_5\wedge x_6$ coefficient. Its mixed block cannot vanish, since the mixed block of $z$ has rank two but that of $r$ has rank one. Write it similarly as $w'\wedge(\mu_5x_5+\mu_6x_6+\ell')$.

Comparing mixed coefficients yields

$$
u=\lambda_5w+\mu_5w',\qquad v=\lambda_6w+\mu_6w'.
$$

Independence of $u,v$ forces $w\in\langle u,v\rangle$. Thus the fixed nonzero $w$ belongs to the plane $P_i$ associated with the coset of $z$. Since the three planes have pairwise trivial intersection, $r$ cannot work for two distinct nonzero cosets.

### Case B: the coefficient of $x_5\wedge x_6$ in $r$ is one

The projection of the two factors onto $\langle x_5,x_6\rangle$ is now invertible. Hence there are unique $a,b\in U$ such that

$$
r=(x_5+a)\wedge(x_6+b).
$$

If $r+z$ is decomposable, its coefficient of $x_5\wedge x_6$ is also one. Comparison of mixed terms forces

$$
r+z=(x_5+a+v)\wedge(x_6+b+u).
$$

Comparing the remaining terms gives

$$
a\wedge u+v\wedge b+v\wedge u=z_0.
$$

For a fixed coset, $z_0$ is fixed modulo $S$. Use the two linear functionals on $\Lambda^2 U$

$$
\begin{aligned}
\phi(\omega)&=c_{12}+c_{13}+c_{23}+c_{34},\\
\psi(\omega)&=c_{13}+c_{14}+c_{23},
\end{aligned}
$$

where $c_{ij}$ are the coefficients of $\omega$. Both vanish on $S$, as follows by substitution of $q_1,q_2,q_3$.

Write $a=\sum_{i=1}^4 a_i x_i$, $b=\sum_{i=1}^4 b_i x_i$, and define

$$
A=a_1+a_4+b_1,\quad
B'=a_2+a_3+a_4+b_1+b_3,\quad
D=a_1+a_2+a_3+b_3=A+B'.
$$

Applying $\phi$ and $\psi$ to the equality above, with the respective $(u,v)$ from §3, gives the following necessary conditions. The first and second columns of conditions come from $\phi$ and $\psi$, respectively.

| Coset | $\phi$ | $\psi$ |
| :--- | :--- | :--- |
| $q_4+S$ | $A=0$ | $B'=1$ |
| $q_5+S$ | $D=0$ | $A=0$ |
| $q_4+q_5+S$ | $B'=0$ | $D=1$ |

For example, in the first row, $u=x_1+x_3+x_4$, $v=x_2+x_4$, and $z_0$ is congruent to $x_{13}+x_{23}+x_{14}+x_{34}$ modulo $S$; expanding both functionals gives the stated equations.

The first row implies $D=1$, contradicting the second row. The first and third rows disagree on $B'$. The second and third rows disagree on $D$. Thus no two rows can hold simultaneously.

Both cases contradict the necessary property of $r$. Therefore $\mathrm{qMC}(Q)\ge7$. Together with the upper bound, this proves $\mathrm{qMC}(Q)=7$.

## 5. Five unrestricted gates are impossible

This bound has a short independent proof that does not require a normal-form theorem for quadratic circuits.

If an unrestricted circuit has at most five AND gates and computes $Q$, its AND outputs must span, modulo affine functions, a space containing the five-dimensional $W$. Thus it has exactly five AND gates, the span is exactly $W$, and every gate has degree at most two. In particular every gate's quadratic part belongs to $W$.

There must be a first gate whose quadratic part belongs to $W\setminus S$. Both inputs to this gate have quadratic parts in $S$, since all earlier gates have that property. They can therefore be written

$$
p=P+\alpha_5x_5+\alpha_6x_6,\qquad
q=T+\beta_5x_5+\beta_6x_6,
$$

where $P,T$ are Boolean functions of $x_1,\ldots,x_4$ of degree at most two, and the Greek coefficients belong to $\mathbb F_2$.

Their product has $x_5x_6$ coefficient $\alpha_5\beta_6+\alpha_6\beta_5$. This must be zero because every element of $W$ has that coefficient zero. Consequently the two vectors $(\alpha_5,\alpha_6)$ and $(\beta_5,\beta_6)$ are linearly dependent.

Let $P_1,T_1$ be the homogeneous linear parts of $P,T$. The mixed quadratic coefficients of $pq$ are

$$
u=\alpha_5T_1+\beta_5P_1,\qquad
v=\alpha_6T_1+\beta_6P_1.
$$

Terms arising from $x_5^2=x_5$ and $x_6^2=x_6$ contribute only affine terms here. Since the two coefficient vectors are dependent, $u,v$ are dependent. This is impossible for a quadratic part in $W\setminus S$, by the coset table in §3.

No such first gate exists. The circuit cannot compute $Q$. Hence $\mathrm{MC}(Q)\ge6$, and the six-gate construction proves equality.

## 6. Equivalence of quadratic complexity conventions

Sometimes a quadratic circuit is described as an XOR–AND circuit in which every intermediate function has degree at most two, rather than as an AND-depth-one circuit. The syntactic classes differ, but their minimum AND counts agree. For completeness, the following lemma gives a direct proof.

**Lemma.** If $p,q,pq\in B_n$ have degree at most two, then

$$
[pq]\in\langle[p],[q]\rangle+R,
$$

where brackets denote homogeneous quadratic parts and $R$ is the set of decomposable bivectors (including zero) in the relevant exterior square.

**Proof.** Put $E=[p]$, $F=[q]$ in $\Lambda^2 V$, now for the $n$-dimensional space $V$. The vanishing degree-four part of $pq$ gives $E\wedge F=0$.

First suppose $E,F$ are dependent. If both are zero the result is immediate. If both are equal and nonzero, use $pq=p(p+q)+p$, reducing to a product of a quadratic function with an affine function. Thus it suffices to consider $F=0$. Let $w$ be the linear part of $q$. The cubic part of $pq$ gives $E\wedge w=0$.

For a rank-at-least-four bivector $E$, the map $w\mapsto E\wedge w$ is injective: in a basis with $E=e_1\wedge f_1+\cdots+e_r\wedge f_r$, $r\ge2$, every coefficient of $w$ is detected by wedging with a disjoint pair. Thus $w=0$ and $q$ is constant. If $E=u\wedge v$ is nonzero decomposable, the equation instead forces $w\in\langle u,v\rangle$. Write $p=uv+\ell$ for an affine $\ell$. The product $uvq$ is a scalar multiple of $uv$ since Boolean variables satisfy $u^2=u$, $v^2=v$. The other contribution $\ell q$ has decomposable quadratic part. This proves the dependent case.

Now suppose $E,F$ are independent. We claim their combined support has dimension at most four. The support of a bivector is the image of its contraction map $V^*\to V$.

If the support of $F$ is not contained in that of $E$, choose a covector $\xi$ vanishing on the support of $E$ with $\iota_\xi F\ne0$. Contracting $E\wedge F=0$ gives $E\wedge\iota_\xi F=0$. By the injectivity just proved, $E$ must have rank two. Write $E=u\wedge v$ and choose a complement to $\langle u,v\rangle$. The wedge equation forces the component of $F$ in the exterior square of that complement to vanish. Hence $F=\lambda u\wedge v+u\wedge s+v\wedge t$, whose combined support with $E$ has dimension at most four. The same reasoning applies with $E,F$ interchanged.

It remains to consider equal support $H$. Suppose $\dim H\ge6$. Both contraction maps $\varphi_E,\varphi_F:H^*\to H$ are invertible. Let $T=\varphi_F\varphi_E^{-1}$. Contracting the wedge equation shows that for every $x\in H$,

$$
x\wedge F=E\wedge T(x).
$$

If $x,T(x)$ are independent, contract this identity with any covector $\eta$ annihilating both. Wedging the result with $T(x)$ yields $\iota_\eta F\in\langle x,T(x)\rangle$. But the annihilator has dimension at least four, and $\varphi_F$ is injective, a contradiction. Thus every nonzero $x$ satisfies $T(x)=x$ over $\mathbb F_2$, implying $E=F$, contrary to independence. The combined-support claim follows.

Choose linear coordinates so that the combined support lies in at most four variables. Any remaining variables occur in $p,q$ only linearly. For each such variable $y$, the mixed cubic coefficient in $pq$ is $\beta_y E+\alpha_y F$, where $\alpha_y,\beta_y$ are its linear coefficients in $p,q$. The coefficient vanishes, so independence gives $\alpha_y=\beta_y=0$. Thus both functions depend on at most four variables; pad with unused variables to obtain four.

On four variables, any quadratic form of rank four has weight six or ten, even after adding any affine function. Indeed, the signed sum of its values in the exponent of $(-1)$ is $\pm4$, by changing to the normal form $x_1x_2+x_3x_4$ plus affine terms and factoring the sum over the two pairs.

If all four quadratic parts of $pq,pq+p,pq+q,pq+p+q$ had rank four, then the four fibers $(p,q)=(1,1),(1,0),(0,1),(0,0)$ would each contain at least six points. The first three functions are the indicators of the first three fibers, and the last function is the complement of the fourth fiber's indicator. The four fiber sizes would sum to at least 24, exceeding the domain size 16. Therefore one of the four quadratic parts has rank at most two and belongs to $R$. This proves the lemma. $\square$

For a circuit with all intermediate degrees at most two, apply the lemma to each AND gate in topological order. Its quadratic part is in the span of the previous quadratic parts plus a single decomposable form. Inductively, the quadratic output space is covered by at most one decomposable form per AND gate. The exterior-algebra characterization in §3 then constructs a level-one circuit of no greater cost. The reverse inequality is immediate.

In particular, the lower bound of §4 applies under either convention.

## 7. Reproducible finite checks

The accompanying verifier provides a separate check of the example and bounds. It checks both upper-bound circuits on all 64 inputs, and exhaustively counts decomposable forms in every possible six-dimensional superspace of $W$.

There are

$$
\frac{(2^6-1)(2^6-2)}{(2^2-1)(2^2-2)}=651
$$

nonzero decomposable bivectors, corresponding to the two-dimensional subspaces of $V$. There are $2^{15-5}-1=1,023$ six-dimensional superspaces of $W$, corresponding to nonzero vectors in $\Lambda^2V/W$.

The resulting dimensions of the spans of decomposable elements are:

| Dimension | Number of superspaces |
| ---: | ---: |
| 3 | 604 |
| 4 | 323 |
| 5 | 96 |
| 6 | 0 |

This independently confirms §4. The verifier also evaluates every product of two elements of the 1,024-element space consisting of affine functions plus $S$, and checks that none has quadratic part in $W\setminus S$ with degree at most two, confirming §5.

## 8. Context and limitations

The question addressed here is whether nonlinear intermediate Boolean computations can strictly reduce multiplicative complexity for a family of quadratic forms. The example answers that question, not the separate question of whether particular asymptotic lower bounds for quadratic circuits persist for unrestricted circuits.

It uses Boolean idempotence $x_i^2=x_i$; the same computation is not an identity of formal polynomials. It does not establish a separation for three or four outputs, minimality in the number of input variables, a separation for bilinear maps, or an unbounded multiplicative gap.

See the [README](README.md#references) for references.
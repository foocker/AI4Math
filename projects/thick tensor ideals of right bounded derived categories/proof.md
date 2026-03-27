# Proof

## Problem Statement

The main goal of this task is to investigate Remark 7.22. other is background. We do not know if it holds for $d \geqslant 3$. just this question.



Example 7.21. Let $R$ be a commutative ring, Let $x \in R$ be a nonzerodivisor. For integers $a, b, c \geqslant 0$, define a complex

$$
X(a, b, c)=\bigoplus_{i \geqslant 0}\left(R / f_i\right)[i]=\left(\cdots \stackrel{0}{\rightarrow} R / f_2 \xrightarrow{0} R / f_1 \xrightarrow{0} R / f_0 \rightarrow 0\right),
$$

where $f_i=x^{a i^2+b i+c} \in R$. Then it holds that thick ${ }^{\otimes}\{X(a, b, c) \mid a, b, c \geqslant 0\}=$ thick $^{\otimes}\{X(1,0,0)\}$.

Remark 7.22. One can consider a general statement of Example 7.21 by defining $f_i=x^{a_0 i^d+a_1 i^{d-1}+\cdots+a_d}$, so that it is nothing but the example for $d=2$. We do not know if it holds for $d \geqslant 3$.

## Proof

We prove that the general statement holds for all integers $d \geqslant 1$. Specifically, for any integer $d \geqslant 1$, any commutative noetherian ring $R$, and any nonzerodivisor $x \in R$, defining

$$X(a_0, a_1, \ldots, a_d) = \bigoplus_{i \geqslant 0} \left(R/x^{a_0 i^d + a_1 i^{d-1} + \cdots + a_d}\right)[i]$$

for non-negative integers $a_0, \ldots, a_d$, we have the equality

$$\mathrm{thick}^{\otimes}\{X(a_0, a_1, \ldots, a_d) \mid a_0, \ldots, a_d \geqslant 0\} = \mathrm{thick}^{\otimes}\{X(1, 0, \ldots, 0)\}.$$

The inclusion $(\supseteq)$ is trivial since $X(1,0,\ldots,0)$ appears on the left-hand side with $a_0 = 1$ and $a_1 = \cdots = a_d = 0$. For the inclusion $(\subseteq)$, we must show that every $X(a_0, \ldots, a_d) \in \mathrm{thick}^{\otimes}\{X(1,0,\ldots,0)\}$. We abbreviate $\mathcal{T} = \mathrm{thick}^{\otimes}\{X(1,0,\ldots,0)\}$ throughout.

Let $e_k$ denote the $(d+1)$-tuple with 1 in position $k$ and 0 elsewhere (for $0 \leqslant k \leqslant d$). By Lemma 7.20 (second part, iterated), the complex $X(a_0, \ldots, a_d)$ whose exponent at index $i$ is $a_0 i^d + a_1 i^{d-1} + \cdots + a_d$ belongs to the thick closure of the complexes $X(e_k)$ for $k = 0, \ldots, d$. Since $\mathrm{thick}^{\otimes}$ is at least as large as the thick closure, it suffices to show $X(e_k) \in \mathcal{T}$ for each $k$.

Now, $X(e_k)$ has exponent sequence $\{i^{d-k}\}_{i \geqslant 0}$. Defining $\mathbf{X}(p) = \bigoplus_{i \geqslant 0} (R/x^{p(i)})[i]$ for any sequence $p(i) \geqslant 0$, our goal reduces to showing that for each $0 \leqslant k \leqslant d$, the complex $\mathbf{X}(i^{d-k})$ belongs to $\mathcal{T} = \mathrm{thick}^{\otimes}\{\mathbf{X}(i^d)\}$. Equivalently: for each $0 \leqslant m \leqslant d$, we must show $\mathbf{X}(i^m) \in \mathcal{T}$.

The proof requires two new ingredients beyond those used in Example 7.21: a coefficient formula for finite differences, and a generalization of Proposition 7.2 / Corollary 7.3 from 2-fold to $p$-fold splitting. We establish these first.

---

### Lemma A (Coefficient Formula for Finite Differences)

**Statement.** For integers $d \geqslant 1$ and $0 \leqslant m \leqslant d$, the $m$-th forward finite difference of $i^d$ has the monomial expansion

$$\Delta^m(i^d) = \sum_{j=0}^{d-m} \binom{d}{j}\, m!\, S(d-j,\, m)\; i^j,$$

where $S(n, r)$ denotes the Stirling number of the second kind. In particular:

(i) Every coefficient $\binom{d}{j}\, m!\, S(d-j, m)$ is a non-negative integer.
(ii) The leading coefficient (at $j = d-m$) equals $\frac{d!}{(d-m)!}$.
(iii) $\Delta^m(i^d) \geqslant 0$ for all $i \geqslant 0$.

**Proof.** The $m$-th forward finite difference is $\Delta^m(i^d) = \sum_{s=0}^{m} (-1)^{m-s} \binom{m}{s} (i+s)^d$. Since the coefficient of $i^j$ in $(i+s)^d$ is $\binom{d}{j} s^{d-j}$, the coefficient of $i^j$ in $\Delta^m(i^d)$ is $\binom{d}{j} \sum_{s=0}^{m} (-1)^{m-s} \binom{m}{s}\, s^{d-j}$.

By the standard identity for Stirling numbers of the second kind, $\sum_{s=0}^{m} (-1)^{m-s} \binom{m}{s}\, s^n = m!\, S(n, m)$ for all $n \geqslant 0$, with the convention $S(0,0) = 1$ and $S(n, m) = 0$ for $n < m$. Therefore the coefficient of $i^j$ is exactly $\binom{d}{j}\, m!\, S(d-j, m)$.

For (i), each factor $\binom{d}{j}$, $m!$, and $S(d-j, m)$ is a non-negative integer.
For (ii), at $j = d - m$, the coefficient is $\binom{d}{d-m}\, m!\, S(m, m) = \frac{d!}{(d-m)!\, m!} \cdot m! \cdot 1 = \frac{d!}{(d-m)!}$. For $j > d - m$, we have $d - j < m$, so $S(d-j, m) = 0$; thus the polynomial has degree exactly $d - m$.
For (iii), since $\Delta^m(i^d) = \sum_{j} \alpha_j\, i^j$ with all $\alpha_j \geqslant 0$, and $i \geqslant 0$, we get $\Delta^m(i^d) \geqslant 0$. $\square$

---

### Lemma B ($p$-fold Splitting — Generalized Corollary 7.3)

**Statement.** Let $p \geqslant 2$ be a positive integer and $X = \bigoplus_{n \geqslant 0} M_n[n]$ a complex in $\mathrm{D}^{-}(R)$ with zero differentials. For $r = 0, 1, \ldots, p-1$, define

$$X^{(r)} = \bigoplus_{i \geqslant 0} M_{pi+r}[i].$$

Then $X \in \mathrm{thick}^{\otimes}\{X^{(0)}, X^{(1)}, \ldots, X^{(p-1)}\}$.

**Proof.** We show that for each $r \in \{0, \ldots, p-1\}$, the complex $Z_r := \bigoplus_{i \geqslant 0} M_{pi+r}[pi+r]$ is in $\mathrm{thick}^{\otimes}\{X^{(r)}\}$. Since $X = Z_0 \oplus Z_1 \oplus \cdots \oplus Z_{p-1}$ as a direct sum decomposition of graded modules with zero differentials, the conclusion will follow.

Fix $r \in \{0, \ldots, p-1\}$. Define the complex $Y_r = \bigoplus_{j \geqslant 0} R[(p-1)j + r]$. Under the convention that $[k]$ places the module in homological degree $k$ (and thus cohomological degree $-k$), $Y_r$ has non-zero components only in cohomological degrees $\leqslant 0$, so $Y_r$ belongs to $\mathrm{D}^{-}(R)$. 

Because $X^{(r)}$ is a complex with zero differentials and $Y_r$ is a complex of free $R$-modules (hence K-flat) with zero differentials, the derived tensor product $X^{(r)} \otimes_R^L Y_r$ equals the ordinary tensor product and has zero differentials. Explicitly:

$$X^{(r)} \otimes_R^L Y_r = \bigoplus_{i, j \geqslant 0} (M_{pi+r} \otimes_R R)[i + (p-1)j + r] = \bigoplus_{i, j \geqslant 0} M_{pi+r}[i + (p-1)j + r].$$

In homological degree $n$, this tensor product has module $\bigoplus_{i + (p-1)j + r = n} M_{pi+r}$. Consider the "diagonal" sub-collection defined by $j = i$. For $j = i$, the degree is $i + (p-1)i + r = pi + r$, and the module contributed is $M_{pi+r}$. Thus, for each $i_0 \geqslant 0$, the module $M_{pi_0+r}$ appears as a direct summand of the degree-$(pi_0+r)$ component of $X^{(r)} \otimes_R^L Y_r$.

Since all differentials are zero, the subcomplex $Z_r = \bigoplus_{i \geqslant 0} M_{pi+r}[pi+r]$ is a direct summand of $X^{(r)} \otimes_R^L Y_r$ in the category of complexes, and hence in $\mathrm{D}^{-}(R)$. Since thick tensor ideals are closed under tensor product with any object of $\mathrm{D}^{-}(R)$, we have $X^{(r)} \otimes_R^L Y_r \in \mathrm{thick}^{\otimes}\{X^{(r)}\}$. Because thick tensor ideals are closed under direct summands, we conclude $Z_r \in \mathrm{thick}^{\otimes}\{X^{(r)}\}$. 

Therefore $X = \bigoplus_{r=0}^{p-1} Z_r \in \mathrm{thick}^{\otimes}\{X^{(0)}, X^{(1)}, \ldots, X^{(p-1)}\}$. $\square$

---

### Lemma C (Subtraction of Exponent Sequences)

**Statement.** If the complexes $\mathbf{X}(a_i + b_i)$ and $\mathbf{X}(b_i)$ both belong to $\mathcal{T}$, and $a_i, b_i \geqslant 0$ for all $i \geqslant 0$, then $\mathbf{X}(a_i)$ also belongs to $\mathcal{T}$.

**Proof.** For each $i \geqslant 0$, we have the short exact sequence of $R$-modules $0 \to R/x^{a_i} \xrightarrow{\;x^{b_i}\;} R/x^{a_i + b_i} \to R/x^{b_i} \to 0$ (the map is well-defined and injective since $x$ is a nonzerodivisor). Taking the direct sum over all $i \geqslant 0$ and placing each term in degree $[i]$, we obtain a short exact sequence of complexes with zero differentials:

$$0 \to \mathbf{X}(a_i) \to \mathbf{X}(a_i + b_i) \to \mathbf{X}(b_i) \to 0.$$

Since $\mathcal{T}$ is a thick subcategory (closed under extensions and cones), and both $\mathbf{X}(a_i + b_i)$ and $\mathbf{X}(b_i)$ are in $\mathcal{T}$, the two-out-of-three property gives $\mathbf{X}(a_i) \in \mathcal{T}$. $\square$

---

### Lemma D (Finite Differences Preserve the Thick Tensor Ideal)

**Statement.** Let $\{a_i\}_{i \geqslant 0}$ be a sequence of non-negative integers such that $a_{i+1} \geqslant a_i$ for all $i \geqslant 0$. If $\mathbf{X}(a_i) \in \mathcal{T}$, then $\mathbf{X}(a_{i+1} - a_i) \in \mathcal{T}$.

**Proof.** For each $i \geqslant 0$, the short exact sequence $0 \to R/x^{a_i} \xrightarrow{x^{a_{i+1}-a_i}} R/x^{a_{i+1}} \to R/x^{a_{i+1}-a_i} \to 0$ yields, upon taking direct sums over $i$, a short exact sequence of complexes with zero differentials: $0 \to \mathbf{X}(a_i) \to \mathbf{X}(a_{i+1}) \to \mathbf{X}(a_{i+1} - a_i) \to 0$. By the two-out-of-three property for thick subcategories, it suffices to show that $\mathbf{X}(a_{i+1}) \in \mathcal{T}$.

By re-indexing $j = i + 1$, we have

$$\mathbf{X}(a_{i+1}) = \bigoplus_{i \geqslant 0}(R/x^{a_{i+1}})[i] = \bigoplus_{j \geqslant 1}(R/x^{a_j})[j-1] = \left(\bigoplus_{j \geqslant 1}(R/x^{a_j})[j]\right)[-1].$$

Since $\mathbf{X}(a_i) = \bigoplus_{j \geqslant 0}(R/x^{a_j})[j]$ is a complex with zero differentials, it decomposes as a direct sum of its graded pieces, so $\bigoplus_{j \geqslant 1}(R/x^{a_j})[j]$ is a direct summand of $\mathbf{X}(a_i) \in \mathcal{T}$, and hence belongs to $\mathcal{T}$. Applying the shift $[-1]$ gives $\mathbf{X}(a_{i+1}) \in \mathcal{T}$. $\square$

**Corollary of Lemma D.** By iterating Lemma D, if $\mathbf{X}(a_i) \in \mathcal{T}$ and the sequence $\{a_i\}$ satisfies $\Delta^l(a_i) \geqslant 0$ for all $i \geqslant 0$ and $l = 1, \ldots, m$, then $\mathbf{X}(\Delta^m(a_i)) \in \mathcal{T}$. In particular, since $\Delta^l(i^d) \geqslant 0$ for all $i \geqslant 0$ and $0 \leqslant l \leqslant d$ (by Lemma A), starting from $\mathbf{X}(i^d) \in \mathcal{T}$ we get $\mathbf{X}(\Delta^m(i^d)) \in \mathcal{T}$ for every $0 \leqslant m \leqslant d$.

---

### Proof of the Main Claim

We prove by induction on $k$ (from $k = 0$ to $k = d$) that $\mathbf{X}(i^k) \in \mathcal{T}$.

**Base case ($k = 0$).** The complex $\mathbf{X}(1)$ has exponent sequence $\{1, 1, 1, \ldots\}$. Since $\mathbf{X}(i^d) = \bigoplus_{i \geqslant 0}(R/x^{i^d})[i]$ has $(R/x^{1^d})[1] = (R/x)[1]$ as a direct summand, the module $R/x$ belongs to $\mathcal{T}$. Then $\mathbf{X}(1) = (R/x) \otimes_R^L \left(\bigoplus_{i \geqslant 0} R[i]\right) \in \mathcal{T}$ since $\bigoplus_{i \geqslant 0} R[i] \in \mathrm{D}^{-}(R)$ and thick tensor ideals are closed under tensor products. $\square$

**Inductive step.** Suppose $k \geqslant 1$ and $\mathbf{X}(i^l) \in \mathcal{T}$ for all $0 \leqslant l < k$. We prove $\mathbf{X}(i^k) \in \mathcal{T}$. Set $m = d - k$. By the Corollary of Lemma D, the complex $\mathbf{X}(Q(i)) \in \mathcal{T}$ where $Q(i) = \Delta^m(i^d)$. By Lemma A, $Q(i) = \sum_{j=0}^{k} \alpha_j\, i^j$ where $\alpha_j = \binom{d}{j}\, m!\, S(d-j, m) \geqslant 0$ for all $j$, and $\alpha_k = \frac{d!}{k!}$. 

Define $c = \alpha_k = \frac{d!}{k!}$ and $q(i) = Q(i) - c\,i^k = \sum_{j=0}^{k-1} \alpha_j\, i^j$.

**Step 1: $\mathbf{X}(q(i)) \in \mathcal{T}$.** Since each $\alpha_j$ is a non-negative integer (by Lemma A) and $\mathbf{X}(i^j) \in \mathcal{T}$ for $j < k$ (by the inductive hypothesis), Lemma 7.20 (scalar multiplication) gives $\mathbf{X}(\alpha_j\, i^j) \in \mathcal{T}$. Summing using Lemma 7.20 (addition), we get $\mathbf{X}(q(i)) \in \mathcal{T}$.

**Step 2: $\mathbf{X}(c\,i^k) \in \mathcal{T}$.** Since $Q(i) = c\,i^k + q(i)$ with $c\,i^k \geqslant 0$ and $q(i) \geqslant 0$, Lemma C applied with $a_i = c\,i^k$ and $b_i = q(i)$ gives $\mathbf{X}(c\,i^k) \in \mathcal{T}$.

**Step 3: $\mathbf{X}(i^k) \in \mathcal{T}$ via $c$-fold splitting.** We apply Lemma B with $p = c$ to the complex $\mathbf{X}(i^k)$. The $c$-fold parts are $\mathbf{X}(i^k)^{(r)} = \mathbf{X}((ci+r)^k)$ for $r = 0, \ldots, c-1$. By Lemma B, $\mathbf{X}(i^k) \in \mathrm{thick}^{\otimes}\{\mathbf{X}((ci+r)^k) \mid r = 0, \ldots, c-1\}$. It remains to show each $\mathbf{X}((ci+r)^k) \in \mathcal{T}$.
By the binomial theorem, $(ci + r)^k = c^k\, i^k + \sum_{j=0}^{k-1} \binom{k}{j} c^j\, r^{k-j}\, i^j$. 
For the lower-order terms, each coefficient $\beta_j = \binom{k}{j} c^j\, r^{k-j}$ is a non-negative integer. By the inductive hypothesis, $\mathbf{X}(i^j) \in \mathcal{T}$, so $\mathbf{X}(\beta_j\, i^j) \in \mathcal{T}$, and their sum is in $\mathcal{T}$. 
For the leading term, from Step 2, $\mathbf{X}(c\,i^k) \in \mathcal{T}$. By Lemma 7.20 (scalar multiplication with factor $c^{k-1}$), $\mathbf{X}(c^k\, i^k) = \mathbf{X}(c^{k-1} \cdot c\,i^k) \in \mathcal{T}$. 
Adding the leading and lower-order terms (Lemma 7.20 addition), we get $\mathbf{X}((ci+r)^k) \in \mathcal{T}$. By Lemma B, $\mathbf{X}(i^k) \in \mathcal{T}$. $\square$

---

### Completing the Proof

By the Main Claim, $\mathbf{X}(i^m) = X(e_{d-m}) \in \mathcal{T}$ for all $0 \leqslant m \leqslant d$. By Lemma 7.20 (second part, iterated), for any tuple $(a_0, \ldots, a_d)$ of non-negative integers, the complex $X(a_0, \ldots, a_d)$ with exponent $\sum_j a_j i^{d-j}$ belongs to the thick closure of $\{X(e_0), X(e_1), \ldots, X(e_d)\}$, which is contained in $\mathcal{T}$. Therefore $\mathrm{thick}^{\otimes}\{X(a_0, \ldots, a_d) \mid a_0, \ldots, a_d \geqslant 0\} \subseteq \mathcal{T} = \mathrm{thick}^{\otimes}\{X(1, 0, \ldots, 0)\}$, proving the general statement. $\blacksquare$

## Key Ideas
1. **$p$-fold splitting (Lemma B).** Generalizes Corollary 7.3 to arbitrary $p \geqslant 2$-fold splitting, enabling "division by $p$" for any $p$. Proved by tensoring with $Y_r = \bigoplus_j R[(p-1)j + r]$ and extracting the diagonal direct summand.
2. **Coefficient formula via Stirling numbers (Lemma A).** The finite difference $\Delta^{d-k}(i^d)$ is a degree-$k$ polynomial where all lower-degree terms have non-negative integer coefficients, enabling subtraction (Lemma C).
3. **Bottom-up induction.** Starting with $\mathbf{X}(i^d) \in \mathcal{T}$, we iterate finite differences to produce lower-degree polynomials, subtract off strictly lower-degree terms (which are in $\mathcal{T}$ by induction), and use $c$-fold splitting to isolate $\mathbf{X}(i^k)$.
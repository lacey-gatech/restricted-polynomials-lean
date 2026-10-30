# Restricted polynomial progressions in $\mathbb{F}_p^n$: a Lean formalization

This is a Lean 4 formalization of the paper *Reasonable bounds for restricted polynomial
progressions in $\mathbb{F}_p^n$* by A. Burgin, A. Fragkos, D. Kruzel, M. Lacey and
A. Stokolosa. The formalization has two `admit`s: the inverse theorem of Bhangale, Khot,
Liu and Minzer on noise stability, which arose in the study of constraint satisfaction problems
(CSPs) in computer science, and Dimitrov's theorem on the Schinzel–Zassenhaus conjecture, which
is used only for the explicit sizes of $M_k$ and $P_k$. Everything else, including the paper's
main new ingredient, is proved.

## The main theorem

Fix $k \ge 2$. There are $M_k = \exp(O(k\log k))$ and $P_k = \exp\exp(O(k^2\log k))$, depending only on $k$, and an integer
$K = k^{O(k)}$, with the following property. For every prime $p \ge P_k$ there are
$C, c > 0$ such that if $n > \exp^{(K)}(1)$ and $A \subseteq \mathbb{F}_p^n$ satisfies

$$\frac{|A|}{p^n} \ge \frac{C}{(\log^{(K)} n)^c},$$

then $A$ contains a restricted progression

$$x,\quad x + P_1(y),\quad \ldots,\quad x + P_{k-1}(y), \qquad P_j(y) = (y_1^j, \ldots, y_n^j),$$

with $y \in \{0, 2, 3, \ldots, M_k\}^n\setminus \{0\}^n$, and its $k$ points are pairwise
distinct. 

In Lean this is `RestrictedPolynomials.main_theorem : MainTheorem`, with `MainTheorem` defined
in [`Statement.lean`](RestrictedPolynomials/Statement.lean):

```lean
def MainTheorem : Prop :=
  ∃ C₁ : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ M P : ℕ,
    (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
    (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
    ∀ p : ℕ, p.Prime → P ≤ p →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, Real.exp^[k ^ (C₁ * k)] 1 < n →
        ∀ A : Finset (Fin n → ZMod p),
          C / (Real.log^[k ^ (C₁ * k)] n) ^ c ≤ (A.card : ℝ) / (p : ℝ) ^ n →
          HasRestrictedProgression p M k (A : Set (Fin n → ZMod p))
```

`HasRestrictedProgression` (in [`Defs.lean`](RestrictedPolynomials/Defs.lean)) asks for
`x` and a nonzero step `y` with coordinates in `{0, 2, …, M}` such that every point of the
progression lies in `A` and the points are pairwise distinct.

## The admitted results

Two statements are unproved. The first is `inverse_theorem` in
[`Statement.lean`](RestrictedPolynomials/Statement.lean), Theorem 1.4 of the paper
([CSP_7, Theorem 1]). Informally: let $\mu$ be a distribution on $\alpha^k$ that admits no
nontrivial abelian embedding. For every $\varepsilon > 0$, once $n$ is large enough, if
1-bounded functions $f_1, \ldots, f_k$ on $\alpha^n$ satisfy
$|\mathbb{E}_{\mu^{\otimes n}} \prod_i f_i(x_i)| \ge \varepsilon$, then
$\mathrm{Stab}_{1-\delta}(f_i) > \delta$ for every $i$, where
$\delta = \exp(-\exp^{(k^{C_0 k})}(\varepsilon^{-b}))$.

The formal statement is slightly weaker than the theorem quoted in the paper. All alphabets are
one finite type, the functions are real-valued, and the exponent `b` and the dimension
threshold may depend on the whole distribution `μ`. The number of iterated exponentials is
`k ^ (C₀ * k)` for one absolute constant `C₀`, which is what the `k^{O(k)}` in the main theorem
relies on. Anyone checking the formalization should compare this statement with CSP_7.

The second is `dimitrov` in [`Dimitrov.lean`](RestrictedPolynomials/Dimitrov.lean), Theorem 5.11
of the paper ([Dim19, Theorem 1]): a monic, irreducible, non-cyclotomic $Q \in \mathbb{Z}[z]$ of
degree $d > 1$ has a root of absolute value at least $2^{1/(4d)}$. It is a published theorem
(the Schinzel–Zassenhaus conjecture) and is used only in Lemma 5.12, which gives the explicit
growth of $M(\ell)$ and $P(\ell)$.

## Building and checking

The toolchain (Lean `v4.34.1`) and Mathlib (tag `v4.34.1`) are pinned in `lean-toolchain` and
`lake-manifest.json`. With [elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get
```

```bash
lake build
```

The first command downloads prebuilt Mathlib, so nothing large is compiled locally. The build
should finish with exactly two `declaration uses 'sorry'` warnings, from `Statement.lean` and
`Dimitrov.lean`.

To confirm that the main theorem depends on nothing else, check a file containing

```lean
import RestrictedPolynomials
#print axioms RestrictedPolynomials.main_theorem
```

which reports `propext`, `Classical.choice`, `Quot.sound` (Lean's standard axioms) and
`sorryAx`, the last coming only from `inverse_theorem` and `dimitrov`.

## Layout

| Paper | File |
|---|---|
| Definitions; Theorem 1.1 and Theorem 1.4 statements | `Defs`, `Statement` |
| §2: expectations, Efron–Stein decomposition, noise, stability | `Expect`, `EfronStein` |
| Lemma 3.7: reduction to cyclic groups of prime order | `CyclicReduction` |
| Lemma 3.4: no embeddings into $\mathbb{F}_p$ | `SameChar` |
| Lemmas 5.2 and 5.4: Kronecker's theorem, the infinite matrix | `Kronecker` |
| Lemma 5.7 (monic minors) and vanishing minors | `Minors` |
| Lemmas 5.5 and 5.6: the ideal of minors | `MinorIdeal` |
| Proposition 5.1: full rank (qualitative proof, §5.2) | `FullRank` |
| Theorem 5.11 (Dimitrov, admitted) | `Dimitrov` |
| §5.3: parameters, Lemma 5.10 (determinant estimate), coefficient and degree bounds | `QuantDefs`, `QuantParams`, `DetEstimate` |
| §5.3: Lemma 5.12 (roots of unity), Lemma 5.13 (prime orders), effective Bézout (5.12) | `RootsOfUnity`, `CyclotomicOrder`, `EffBezout` |
| Proposition 5.1: full rank with $M(\ell) = \exp(O(\ell\log\ell))$, $P(\ell) = \exp\exp(O(\ell^2\log\ell))$ (§5.3) | `QuantFullRank` |
| Lemma 5.9: no embeddings into $\mathbb{F}_q$, $q \ne p$ | `DiffChar` |
| Proposition 3.1: no nontrivial abelian embedding | `NoEmbedding` |
| Lemma 6.1 and Proposition 6.6 (every dimension) | `Stability` |
| Lemma 6.2: random restrictions | `Hoeffding`, `Restriction` |
| Lemmas 6.3 and 6.4: the counting distribution, fibers | `Counting`, `LargeExp` |
| Lemma 6.7: density increment and iteration | `Increment` |
| Parameters, the tower bound, Theorem 1.1 | `Main` |

All files are in [`RestrictedPolynomials/`](RestrictedPolynomials/).

## Differences from the paper

The formalization follows the paper's proofs, with these changes in presentation:

- **Lemma 5.4.** Only the case $|\theta|_v > 1$ is needed, because Mathlib's form of Kronecker's
  theorem only asks every conjugate to lie in the closed unit disk.
- **Lemma 5.8** (exceptional characteristics). The gcd and field-degree argument is replaced
  by a pigeonhole on the Frobenius orbit $\lambda, \lambda^q, \lambda^{q^2}, \ldots$ among the
  roots of the monic minor with rows $2, \ldots, \ell + 1$. The resulting bound on the order of
  $\lambda$ is the same in kind.
- **Roots of the generator $D$.** Handled by adjoining to $\mathbb{Q}$ a root of each
  irreducible factor of $D$, giving a number field in which Lemma 5.4 applies, rather than by
  working in $\mathbb{C}$.
- **Lemma 6.2.** Hoeffding's inequality is derived from Mathlib's Hoeffding lemma applied to a
  two-point measure, giving the paper's bound $16\exp(-n/(2d^2))$.
- **Section 5.3 constants.** The cutoff is $M(\ell) = \ell + 4 d_\ell \ell^2 + 1$ with
  $d_\ell = \sum_{r=1}^{\ell}(r+1)^r$, which satisfies the hypothesis of Lemma 5.12, rather than
  the paper's $N(\ell)$. The Bézout multiplier is bounded using Mathlib's `Matrix.det_le` on the
  Gram matrix of a maximal independent set of columns, giving $B \le (2n)!\,(2n x^2)^{2n}$ with
  $x = 2^\ell \ell!$, instead of Hadamard's inequality; the resulting $P(\ell)$ differs from
  (5.13) but has the same growth $\exp\exp(O(\ell^2\log\ell))$.
- **Proposition 3.1.** It is proved for $M = M(\ell)$ only (Theorem 1.1 needs no other $M$).
- **Constants.** The proof produces $K = k^{(C_0 + 2)k}$,
  $C = (2(2^k - 1) \cdot 3^{1/b})^{1/k}$ and $c = 1/(bk)$, with $b \ge 1$ from the inverse
  theorem.

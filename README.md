# Restricted polynomial progressions in $\mathbb{F}_p^n$: a Lean formalization

This is a Lean 4 formalization of the paper

> A. Burgin, A. Fragkos, D. Kruzel, M. Lacey and A. Stokolosa, *Reasonable bounds for restricted
> polynomial progressions in $\mathbb{F}_p^n$*, [arXiv:2610.12831](https://arxiv.org/abs/2610.12831).

The formalization is complete. Theorem 1.1, and every theorem, proposition and lemma of the paper
used in its proof, is proved with no `sorry`, no `admit` and no custom axiom (a few intermediate
results in a specialised or restated form; see "Differences from the paper"). That includes the two
theorems the paper cites from the literature and does not prove:
- the inverse theorem of Bhangale, Khot, Liu and Minzer on noise stability (Theorem 1.4 of the
  paper), which arose in the study of constraint satisfaction problems (CSPs);
- Dimitrov's theorem on the Schinzel–Zassenhaus conjecture (Theorem 5.11 of the paper).

The main theorem and the two cited theorems depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## The main theorem

Fix $k \ge 2$. There are $M_k = \exp(O(k\log k))$ and $P_k = \exp\exp(O(k^2\log k))$, depending
only on $k$, and an integer $K = k^{O(k)}$, with the following property. For every prime
$p \ge P_k$ there are $C, c > 0$ such that, if $n > \exp^{(K)}(1)$ and $A \subseteq \mathbb{F}_p^n$
satisfies

$$\frac{|A|}{p^n} \ge \frac{C}{(\log^{(K)} n)^c},$$

then $A$ contains a restricted progression

$$x,\quad x + P_1(y),\quad \ldots,\quad x + P_{k-1}(y), \qquad P_j(y) = (y_1^j, \ldots, y_n^j),$$

with $y \in \lbrace 0, 2, 3, \ldots, M_k\rbrace^n\setminus \lbrace 0\rbrace^n$. Moreover, the $k$ points of any such
progression are pairwise distinct.

The statement of record is [`Challenge.lean`](Challenge.lean): it is short, imports only Mathlib,
and is the file a reader should audit. Its theorem is

```lean
theorem main_theorem : MainTheorem := by
  sorry
```

where the `sorry` is the deliberate hole that [Comparator](https://github.com/leanprover/comparator)
fills with the library's proof, and

```lean
def MainTheorem : Prop :=
  ∃ C₁ : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ M P : ℕ,
    (M : ℝ) ≤ Real.exp (7 * k * Real.log k) ∧
    (P : ℝ) ≤ Real.exp (Real.exp (25 * k ^ 2 * Real.log k)) ∧
    ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ (n : ℕ) (x y : Fin n → ZMod p), (∀ i, ∃ t ∈ stepSet M, y i = t) → y ≠ 0 →
        Function.Injective fun j : Fin k => x + polyTerm j y) ∧
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, Real.exp^[k ^ (C₁ * k)] 1 < n →
        ∀ A : Finset (Fin n → ZMod p),
          C / (Real.log^[k ^ (C₁ * k)] n) ^ c ≤ (A.card : ℝ) / (p : ℝ) ^ n →
          HasRestrictedProgression p M k (A : Set (Fin n → ZMod p))
```

Here `stepSet M` is $\lbrace 0, 2, 3, \ldots, M\rbrace$, `polyTerm j y` is $P_j(y)$ (with $P_0(y) = 0$),
and `HasRestrictedProgression p M k A` says that `A` contains a progression as above whose $k$
points are pairwise distinct. The bounds $M_k \le \exp(7k\log k)$ and
$P_k \le \exp\exp(25k^2\log k)$ make the paper's $O(\cdot)$ explicit, and $K = k^{C_1 k}$ with
$C_1$ absolute.

In the library the theorem is `RestrictedPolynomials.main_theorem`, in
[`Frozen/MainTheoremProof.lean`](RestrictedPolynomials/Frozen/MainTheoremProof.lean). The four
definitions are in [`Frozen/`](RestrictedPolynomials/Frozen/), with the same bodies and imports as
in `Challenge.lean`.

## Palomar submission layout

| File | Role |
|---|---|
| [`Challenge.lean`](Challenge.lean) | The statement of Theorem 1.1, with a deliberate `sorry`; Mathlib-only imports |
| [`Frozen/MainTheoremProof.lean`](RestrictedPolynomials/Frozen/MainTheoremProof.lean) | The Solution module: declares and proves `RestrictedPolynomials.main_theorem` |
| [`comparator.json`](comparator.json) | Compares `RestrictedPolynomials.main_theorem`; permitted axioms `propext`, `Quot.sound`, `Classical.choice` |
| [`formalization.yaml`](formalization.yaml) | Structured metadata: sources, authorship, AI use, review, scope |

Every Lean file is a module of at most 10,000 lines.

## Building and checking

Lean `v4.35.0` and Mathlib `v4.35.0` are pinned in `lean-toolchain` and `lake-manifest.json`. With
[elan](https://github.com/leanprover/elan) installed, download the prebuilt Mathlib first, so
that nothing large is compiled locally:

```bash
lake exe cache get
```

Then build the library and the Challenge:

```bash
lake build
```

The only `declaration uses 'sorry'` warning is the deliberate one in `Challenge.lean`. The other
warnings are style lints.

```bash
python3 scripts/check-no-sorry.py
```

checks, with comments masked, that no Lean file other than `Challenge.lean` contains `sorry`,
`admit` or `axiom`, and

```bash
bash scripts/print-axioms.sh
```

prints the axioms of `main_theorem`, `inverse_theorem_bklm` and `dimitrov`. Each reports exactly
`propext`, `Classical.choice` and `Quot.sound`.

To run Comparator as Palomar does (Linux with `bubblewrap` only), use

```bash
./scripts/verify-comparator.sh
```

The CI workflow runs all of these on every push.

## The two cited theorems

**Theorem 1.4** ([BKLM VII, Theorem 1]) is `RestrictedPolynomials.inverse_theorem_bklm`, in
[`Frozen/InverseTheoremBKLM.lean`](RestrictedPolynomials/Frozen/InverseTheoremBKLM.lean). It is
stated in full generality:
- alphabets $\Sigma_1, \ldots, \Sigma_k$;
- a distribution $\mu$ with no nontrivial abelian embedding and every atom of mass at least
  $\gamma$;
- 1-bounded complex-valued $f_i$;
- the conclusion $\mathrm{Stab}_{1-\delta}(f_i) \ge \delta$ with respect to the marginal $\mu_i$,
  where $\delta = \exp(-\exp^{(k^{C_0 k})}(\varepsilon^{-b}))$, with $C_0$ absolute and $b$
  depending only on $k$ and $\gamma$.

The paper prints $> \delta$. The cited theorem proves $\ge \delta$, which is what is stated here.
The special case the paper's proof uses (one alphabet, real-valued functions, strict inequality
for a smaller $\delta$) is `inverse_theorem`, in
[`InverseCorollary.lean`](RestrictedPolynomials/InverseCorollary.lean).

Its proof is in [`TrackB/`](RestrictedPolynomials/TrackB/) ("Track B"; about 100 files and 64,000
lines), assembled in [`TrackB/FinalAssembly.lean`](RestrictedPolynomials/TrackB/FinalAssembly.lean).
It follows the proofs in Bhangale–Khot–Liu–Minzer's papers IV, VI and VII:
- the K7 recursion of [BKLM VII];
- the main theorem of [BKLM VI];
- the maximality induction, stability theory and Appendix B of [BKM IV].

**Theorem 5.11** ([Dim19, Theorem 1]) is `RestrictedPolynomials.dimitrov`, in
[`Frozen/Dimitrov.lean`](RestrictedPolynomials/Frozen/Dimitrov.lean): a monic, irreducible,
non-cyclotomic $Q \in \mathbb{Z}[z]$ of degree $d > 1$ has a root of absolute value at least
$2^{1/(4d)}$. The paper uses it only in Lemma 5.12, for the explicit growth of $M_k$ and $P_k$. Its
proof is in [`Dimitrov/`](RestrictedPolynomials/Dimitrov/) (29 files, about 8,800 lines).

### Repairs of the cited proofs

Where a cited proof leaves a step unargued, or a printed step is wrong, the step was first
repaired in a written supplement. Each supplement was reviewed independently and then
formalized. The written supplements are not part of this repository: the Lean proof is the
complete, checked argument, and the table below records what each one covers. No repair changes the statement of
Theorem 1.1, 1.4 or 5.11. The Lean docstrings refer to the supplements by letter:

| Supplement | Topic |
|---|---|
| A, B, C | Dimitrov's theorem: Kronecker's theorem in the form used, Pólya's theorem, Dubinin's hedgehog theorem |
| D | Constants in the main theorem of [BKLM VI] that are uniform in the distribution |
| E | The maximality induction of [BKM IV], restated on the class $\mathcal{T}$ of patterns it actually uses |
| F | The bounded-product theorem of [BKLM VI] (`thm:boundedprod`) for 1-bounded functions |
| G | General-$H$ master embeddings of [BKM IV] (not on the route to Theorem 1.4) |
| H | [BKLM VII] `lemma:kcsp`, the step "convert to $\mu_1$" |
| I | [BKM IV] Appendix B, `soft_trunc1`, term (I) when the $x$-support is a proper subset |

## Where each result of the paper is proved

All files are in [`RestrictedPolynomials/`](RestrictedPolynomials/). The numbering follows
arXiv:2610.12831v2. A few docstrings still use the numbering of an earlier draft.

| Paper | Lean declaration | File |
|---|---|---|
| Definitions; statements of Theorems 1.1, 1.4, 5.11 | | `FinProb`, `Defs`, `Frozen/*` |
| §2: expectations, Efron–Stein decomposition, noise, stability | | `Expect`, `EfronStein` |
| **Theorem 1.1** | `main_theorem` (proof `main_theorem_proof`) | `Frozen/MainTheoremProof`, `Main` |
| **Theorem 1.4** | `inverse_theorem_bklm`; the form used: `inverse_theorem` | `Frozen/InverseTheoremBKLM`, `TrackB/`, `InverseCorollary` |
| Proposition 3.1 | `exists_M_P` | `NoEmbedding` |
| Lemma 3.4 | `same_char` | `SameChar` |
| Lemma 3.5 | `diff_char` | `DiffChar` |
| Lemma 3.7 | `cyclic_reduction` | `CyclicReduction` |
| Proposition 5.1, qualitative (§5.2) | `full_rank` | `FullRank` |
| Proposition 5.1, quantitative (§5.3) | `full_rank_quant` | `QuantFullRank` |
| Lemmas 5.2, 5.3 | Mathlib: Kronecker's theorem; $\mathbb{Q}[z]$ is a PID | |
| Lemma 5.4 | `pow_eq_one_of_relation` | `Kronecker`, `Minors` |
| Lemmas 5.5–5.7 | `exists_minor_data`, `irreducible_dvd_of_minors` | `MinorIdeal` |
| Lemma 5.8 | `minor_monic` | `Minors` |
| Lemma 5.9 | proved inside `full_rank` | `FullRank` |
| Lemma 5.10 | `det_estimate` | `DetEstimate` (with `QuantDefs`, `QuantParams`) |
| **Theorem 5.11** | `dimitrov` | `Frozen/Dimitrov`, `Dimitrov/` |
| Lemma 5.12 | `root_of_unity_of_gcd` | `RootsOfUnity` |
| Lemma 5.13 | `prime_order_le` | `CyclotomicOrder` |
| Lemma 5.14 | inside `full_rank_quant`, with `effective_bezout` | `QuantFullRank`, `EffBezout` |
| Lemma 6.1 | `stability_lemma` | `Stability` |
| Lemma 6.2 | `restriction_lemma` | `Hoeffding`, `Restriction` |
| Lemma 6.3 | `large_exp` | `Counting`, `LargeExp` |
| Lemma 6.4 | `fiber_noProgression` | `LargeExp` |
| Proposition 6.6 | `inverse_theorem_all_dims` | `InverseAllDims` |
| Lemma 6.7 | `density_increment`, then `iteration` | `Increment` |
| Iterated exponentials, parameters, the tower bound | `tower_bound` | `ExpIterate`, `Main` |

### Directory guide

- `Frozen/`: the statements of Theorems 1.1, 1.4 and 5.11 and the definitions they use. Each was
  fixed and approved by the author before any proof work began, and was not changed afterwards.
  Each theorem's proof body is a single `by exact` of its proof.
- `Providers/`: the proofs of Theorems 1.4 and 5.11 that the frozen statements cite.
- `TrackB/`: the proof of Theorem 1.4.
- `Dimitrov/`: the proof of Theorem 5.11.
- Everything else: the paper's own sections.

In `Frozen/`, the comments `FROZEN_ANCHOR_*` mark the statement and proof regions of each theorem
file. Two modules, `TrackB/ExhaustEmbed` and `TrackB/S9DeltaExtremal`, formalize results of
paper IV that the main proof does not use; they are built with the rest of the library.

## Differences from the paper

The formalization follows the paper's proofs, with these changes in presentation:

- **Lemmas 5.2 and 5.3.** These standard facts (Kronecker's theorem; Hilbert's basis theorem, in
  the form "$\mathbb{Q}[z]$ is a PID") are taken from Mathlib and are not restated.
- **Lemma 5.4.** Only the case $|\theta|_v > 1$ is needed, because Mathlib's form of Kronecker's
  theorem only asks every conjugate to lie in the closed unit disk.
- **Lemmas 5.5–5.7 and 5.9.** They are proved as steps inside the theorems named in the table above,
  not as separately named Lean theorems.
- **Lemma 5.9** (exceptional characteristics). The gcd and field-degree argument is replaced by a
  pigeonhole on the Frobenius orbit $\lambda, \lambda^q, \lambda^{q^2}, \ldots$ among the roots of
  the monic minor with rows $2, \ldots, \ell + 1$. The resulting bound on the order of $\lambda$ is
  the same in kind.
- **Roots of the generator $D$.** These are handled by adjoining to $\mathbb{Q}$ a root of each
  irreducible factor of $D$, which gives a number field in which Lemma 5.4 applies, rather than by
  working in $\mathbb{C}$.
- **Lemma 3.5.** `diff_char` takes the full-rank statement of Proposition 5.1 as a hypothesis. The
  two are combined in `exists_M_P`.
- **Lemma 6.2.** Hoeffding's inequality is derived from Mathlib's Hoeffding lemma applied to a
  two-point measure. This gives the paper's bound $16\exp(-n/(2d^2))$.
- **Section 5.3 constants.**
  - The cutoff is $M(\ell) = \ell + 4 d_\ell \ell^2 + 1$ with $d_\ell = \sum_{r=1}^{\ell}(r+1)^r$,
    which satisfies the hypothesis of Lemma 5.12, rather than the paper's $N(\ell)$.
  - The Bézout multiplier is bounded with Mathlib's `Matrix.det_le` on the Gram matrix of a maximal
    independent set of columns, instead of Hadamard's inequality. This gives
    $B \le (2n)!\,(2n x^2)^{2n}$ with $x = 2^\ell \ell!$.
  - The resulting $P(\ell)$ differs from (5.13) but has the same growth
    $\exp\exp(O(\ell^2\log\ell))$.
- **Proposition 3.1.** It is proved for $M = M(\ell)$ only, which is all Theorem 1.1 needs.
- **Constants.** The proof produces $K = k^{(C_0 + 2)k}$,
  $C = (2(2^k - 1) \cdot 3^{1/b})^{1/k}$ and $c = 1/(bk)$, with $b \ge 1$ from the inverse
  theorem.
- **Theorems 1.4 and 5.11.** These are proved along their published proofs, with the repairs listed
  under "Repairs of the cited proofs" above.

## How this formalization was produced

The Lean code was written by AI agents (Claude Opus and Claude Sonnet models, in Claude Code),
coordinated by an orchestrating agent. A human maintainer fixed and approved the exact Lean
statements of Theorems 1.1, 1.4 and 5.11, and of the definitions they use, before any proof work.
Those statements were then frozen byte for byte. The maintainer also ruled on every repair of a
cited proof. Each frozen statement was audited against its source by an agent independent of the
one that wrote it. The proofs were checked by Lean's kernel through `lake build`, and the axioms
were checked with `#print axioms`. No human has reviewed the Lean proofs line by line. See
[`formalization.yaml`](formalization.yaml) for the structured record.

## Related work

We know of no earlier formalization of these results, but we have not made a systematic search.
The mathematical results are those of the cited papers; this repository claims no new
mathematics.

## References

The Lean docstrings cite the Bhangale–Khot–(Liu–)Minzer papers as `CSP_4`, `CSP_6` and `CSP_7`
("paper IV", "paper VI", "paper VII"), and quote their LaTeX labels in backquotes. Line numbers
in docstrings ("l. 1222", "L404") refer to the LaTeX sources of the arXiv versions
2307.16248v2 (paper IV), 2411.15133v1 (paper VI), 2411.15136v1 (paper VII) and 1912.12545v1
(Dimitrov). Line numbers for the paper itself refer to the authors' LaTeX source.

- [BFKLS] A. Burgin, A. Fragkos, D. Kruzel, M. Lacey, A. Stokolosa, *Reasonable bounds for
  restricted polynomial progressions in $\mathbb{F}_p^n$*, arXiv:2610.12831.
- [BKM IV] A. Bhangale, S. Khot, D. Minzer, *On approximability of satisfiable $k$-CSPs: IV*,
  arXiv:2307.16248; STOC 2024, 1423–1434.
- [BKLM VI] A. Bhangale, S. Khot, Y. P. Liu, D. Minzer, *On approximability of satisfiable
  $k$-CSPs: VI*, arXiv:2411.15133.
- [BKLM VII] A. Bhangale, S. Khot, Y. P. Liu, D. Minzer, *On approximability of satisfiable
  $k$-CSPs: VII*, arXiv:2411.15136.
- [Dim19] V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*,
  arXiv:1912.12545.

## License

Apache-2.0; see [`LICENSE`](LICENSE). The CI scripts in `scripts/` and `test/` are adapted from
the [Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate) (Apache-2.0).

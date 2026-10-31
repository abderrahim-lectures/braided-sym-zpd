# Review of version 8 — novelty, stress tests, statement audit

Scope: the branch `review/v8-corrections` (v8 as corrected), tip `93b3871`. The audit of the
*v7* commit `977d4ab` is `deep-review-v7.md`; this document covers what v8 changed, what stress
testing found, what is genuinely new, and the state of the Lean formalisation.

A parallel adversarial swarm (eight members, computational only, no network) is still running; its
findings are not in this document yet.

---

## 1. Novelty — the framework and the criterion are published

**The paper's framework is Brice–Huang (2015).** D. Brice and H. Huang, *On zero product
determined algebras*, Linear and Multilinear Algebra **63** (2015) 326–342:

* **Definition 2.1**: "A K-algebra is a pair (A, μ) where A is a K-(bi)module and μ : A ⊗_K A → A
  is a K-linear map." That is the paper's "any bilinear map μ on A gives a nonassociative algebra
  (A, μ)".
* **Definition 2.2**: "(A, μ) is called zero product determined if each K-linear map
  φ : A ⊗ A → B satisfying φ(a₁ ⊗ a₂) = 0 whenever μ(a₁ ⊗ a₂) = 0 factors through μ as
  φ = φ̃ ∘ μ." That is the paper's Definition `def:determined`, over a commutative ring rather than
  a field.
* **Theorem 2.3**: "(A, μ) is zero product determined if and only if T_μ = Ker μ", with T_μ the
  span of the elementary tensors in Ker μ. That is the paper's Corollary `cor:criterion`, exactly,
  and in the same generality.

The same statement appears again as Theorem 13 of Brice, *The matrix Lie algebra on a one-step
ladder is zero product determined* (arXiv:1510.05072), which attributes it to Brice–Huang.

**Consequences.**

1. The paper's first "result" (Corollary `cor:criterion`) is a published theorem, not a new one.
   v8 derives it from Brešar's Proposition 1.3, which is legitimate — 1.3(iii) *is* that
   statement, for a nonassociative algebra over a field — but a referee will ask why the reference
   that states it for the pair (A, μ), over a commutative ring, is absent.
2. The sentence in the introduction, "We replace the product by any bilinear map μ and ask the same
   question", presents as the paper's move something Brice and Huang did in 2015.

**What appears to be new.** No prior statement was found for: the class μ(x,y) = f(xy) and the
transfer from zpd (`thm:zpd-fxy`); the codimension-one theorem (`thm:codim`); the dual-numbers
example as an algebra determined but not zpd; the M₂(𝔽₃) computation; and the question on twisted
products. These are the paper's own contribution as far as the literature search reaches.

**Unverifiable.** Adrabi 2026, cited for Definition 3.1 and Remark 3.4 and carrying the paper's
framing, cannot be found anywhere (arXiv, the author's profiles, his 2024 thesis). Nothing in the
paper's mathematics depends on it — the one borrowed statement, that braided-symmetric derivations
are the derivations of (A, ·_σ), is true by definition — but the positioning cannot be checked.

**Action taken** (commit `93b3871`): both are now cited — the introduction says the framework is
Brice–Huang's, and the criterion carries "stated for an arbitrary bilinear μ, over a commutative
ring, by Brice and Huang [Theorem 2.3]".

---

## 2. Stress tests

### 2.1 The paper's example is not an accident of 𝔽₃ and n = 2

`prop:matrix` computes one case: M₂(𝔽₃), α = conjugation by diag(1,−1), claim determined. Recomputed
over other fields, and in the next dimension:

| A | α | dim Z_μ | dim ker μ̄ | determined |
|---|---|---|---|---|
| M₂(𝔽₃) | conj by diag(1,−1) | 12 | 12 | yes |
| M₂(𝔽₅) | conj by diag(1,−1) | 12 | 12 | yes |
| M₂(𝔽₇) | conj by diag(1,−1) | 12 | 12 | yes |
| **M₃(𝔽₃)** | **conj by diag(1,1,−1)** | **72** | **72** | **yes** |

(M₂ was also checked by brute force over all p⁸ pairs for p = 3, 5, 7; M₃ by computing Z_μ from its
equations — the bilinear forms vanishing on every zero pair — over one representative of each
projective point of A, which is exact and much cheaper than enumerating p¹⁸ pairs.)

So the phenomenon survives a change of field and a jump in dimension, with a **non-commutative**
A₀ = M₂ ⊕ K in the n = 3 case (in n = 2, A₀ is the diagonal algebra and commutes, which is what
makes that case easy). Consequence for the paper: `prop:matrix` is a data point of a general
phenomenon, and Question `q:noncomm` reads as much less open than the paper makes it sound — for
matrix algebras every involutive automorphism is inner (Skolem–Noether), so the question reduces to
"for which involutions D is μ_D determined", and the evidence says: always, so far.

This is a remark, not a defect: the paper claims neither that 𝔽₃ is special nor that the question is
hard. But a referee would ask why the computation stops at the smallest case, and a general
statement for M_n(K) would be the paper's strongest result.

### 2.2 Method note, including two errors of my own

Computing dim Z_μ by enumerating p^{n²} pairs is hopeless for n = 3, so I computed Z_μ through its
annihilator: Z_μ^⊥ = {B bilinear : B(x,w) = 0 for every x and every w ∈ ker μ(x,·)}, which is exact
because μ(x,·) is linear in y. Two wrong turns, recorded because they are the kind of thing that
silently gives a plausible number: (i) a rank call with the wrong row length, which reported
dim ker = 13 for a space where it is 12; (ii) the guess that imposing the equations on a *basis* of
A suffices — it does not, since μ(x,·) is a sum and its kernel is *larger* than the intersection of
the kernels of the summands, so the basis conditions are weaker and gave dim Z = 6 instead of 12.
The numbers in the table above come after both were fixed, and the n = 2 row then reproduces the
brute-force enumeration and the Lean guards.

---

## 3. Statement audit: Lean against v8

| Paper | Lean | Status |
|---|---|---|
| Def. `def:determined` | `mapDetermined` | matches, **except** the target ranges over `Type v`, the universe of `B`, while the paper quantifies over every vector space. Inherited from `Research.Zpd.ZeroProductDetermined`; recorded in the docstring |
| Cor. `cor:criterion` | `mapDetermined_iff_injective'` (no surjectivity), `mapDetermined_iff_injective` (with) | matches |
| Thm. `thm:zpd-fxy` | `mapDetermined_comp_mul_of_zpd` | matches, with the unitality that v8 restored |
| Prop. `prop:injective` | `zpd_of_mapDetermined_comp_mul` | matches |
| Cor. `cor:identity` (i), (ii) | `mapDetermined_identityBraiding_of_zpd`, `mapDetermined_identityBraiding_iff_zpd` | matches, including `(2 : k) ≠ 0` |
| Cor. `cor:twisted` | `mapDetermined_twisted_of_comm_zpd` | matches **after** the fix in `8493e8b`: linear α with multiplicativity, not a unital `AlgHom` |
| Cor. `cor:anti` | `mapDetermined_twisted_anti_of_zpd` | matches (α linear, anti-multiplicative) |
| Thm. `thm:codim` | `mapDetermined_comp_mul_of_codim_one` | matches; every binder checked against the paper's hypotheses |
| Ex. `ex:dual` | `Dual` section | **unverifiable**: needs `Research.Zpd.DualNumbers`; `DualNumbers`, `dualFst`, `dualSnd` occur nowhere in Mathlib |
| Prop. `prop:matrix` | `M2F3Check` | **numbers only**: three `#guard`s check 417, rank 12, rank μ̄ 4; nothing links them to `mapDetermined`, so the proposition is not formalised as a proposition |
| Rem. `rem:preserving`, `rem:derivations` | — | not formalised; the first is a re-reading of the definition, the second uses `Definition def:adrabi-bsder` |

Proof status: no `sorry`, no extra axiom, no `native_decide`. `#print axioms` on the author's file was not
run because it cannot be built from the repository (missing modules); the checks above are elaborations
of it with `Research.Zpd.Basic` stubbed. The paper's core, however, is now machine-checked in a file
that needs no unpublished module — see §6.

---

## 5b. The twisted product with an inner α *is* a Jordan product

For α = conjugation by an invertible D, the twisted product is a Jordan product in disguise:

  xy + α(yx) = xy + (Dy)(xD⁻¹) = (xD⁻¹)(Dy) + (Dy)(xD⁻¹) = (xD⁻¹) ∘ (Dy),

so with Φ: x⊗y ↦ xD⁻¹ ⊗ Dy an automorphism of A⊗A, `μ̄_α = ∘̄ ∘ Φ`, hence Z_{μ_α} = Φ⁻¹(Z_∘) and
ker μ̄_α = Φ⁻¹(ker ∘̄). Therefore **determination by the inner twisted product is equivalent to zJpd,
and is independent of D**. Verified on every pair in M₂(𝔽₃) and M₂(𝔽₅), where the twisted and Jordan
spaces have the same dimensions, 12 and 12.

Two consequences, both taken into the paper as `rem:inner`:

1. `prop:matrix` is a **corollary of published theorems**: Mₙ(B) is generated by the idempotents
   (e_ii + be_ij) − e_ii, and an algebra generated by idempotents is zJpd in characteristic ≠ 2
   (An–Li–He, LAA 475 (2015), Theorem 2.1). So Mₙ(K) is determined by μ_α for every inner
   automorphism, in every dimension, in characteristic ≠ 2. What the 𝔽₃ computation adds is that
   μ_α has no form f(xy) — not the determination.
2. **Question `q:noncomm` is answered for matrix algebras**: every automorphism of Mₙ(K) is inner
   (Skolem–Noether), so in characteristic ≠ 2 every involutive automorphism of Mₙ(K) gives a
   determined product. The question is now qualified in the paper to algebras admitting an
   involutive automorphism that is not inner.

Numerical corroboration from the same pass: the twisted and Jordan zero-pair counts coincide exactly
(417 at p = 3, 4705 at p = 5, 23233 at p = 7, 88 at p = 2), as they must.

## 6. The paper's core, machine-checked

`lean/ZpdCore/Zpd.lean` (added in this branch, Mathlib only, **not** part of `lake build`) checks, over
an arbitrary field and an arbitrary bilinear μ:

| Paper | Declaration | Axioms |
|---|---|---|
| `cor:criterion` | `determined_iff` | propext, choice, Quot.sound |
| `thm:zpd-fxy` | `determined_comp_of_right_id` | propext, choice, Quot.sound |
| `prop:injective` | `determined_of_injective_comp` | propext, Quot.sound |
| `cor:identity` (ii), char-2 remark | `identity_iff`, `determined_zero` | propext, choice, Quot.sound |
| `cor:twisted` | `twisted_determined` | propext, choice, Quot.sound |
| `cor:anti` | `anti_braiding` + `anti_twisted_determined` (added by the blind-spot review: as first committed, `anti_braiding` sat inside `section Commutative` and no determination statement was proved — see `results/blind-spot-review-v8.md` §1.5) | propext, choice, Quot.sound |
| `thm:codim` | `codim_determined`, `codim_determined_of_f_one_zero` | propext, choice, Quot.sound |
| lines 292 and 395 | `jordan_forces_comm`, `twisted_forces_comm` | propext, Quot.sound |
| the abstract's sentence | `braidings_commutative` | propext, Quot.sound |

No `sorry`, no added axiom: the `#print axioms` commands report only Lean's three standard
axioms. Two refinements fall out of the formalisation:

* `thm:zpd-fxy` needs only a **right** identity (`∀ b, m b e = b`) and no associativity. The
  counterexample algebra of D8 has no right identity, so this is a genuine refinement, not a conflict.
* In `thm:codim`, `f(1) ≠ 0` is not needed: if `f(1) = 0` then `f(x) = f(x − c(x)1) + c(x)f(1) = 0`,
  so μ ≡ 0, which determines every algebra (and the ideal hypothesis is not even used there).

What is *not* machine-checked: the numerical claims of `prop:matrix` and of the remark after it. Those
rest on the computations in §2 and on the `#guard`s of the author's file.

---

## 4. Elaboration (measurement only, per `lean-elaboration`)

There was no reported slow target, so this is a baseline, not an optimisation. Lean 4.33.1, Mathlib
at `/opt/mathlib`, warm, with `Research.Zpd.Basic` stubbed and the `Dual` section excluded:

| Target | Wall time (3 runs) |
|---|---|
| the file | 1.48, 1.48, 1.49 s |
| its imports only | 0.62, 0.60, 0.62 s |
| own-file elaboration | ≈ 0.87 s |

`mapDetermined_iff_injective` carried `set_option maxHeartbeats 0`, which disables the heartbeat
limit for that theorem. With the option removed the file still elaborates, at the same cost, so the
escape hatch was unnecessary and is now gone (commit `93b3871`). Note the toolchain here is 4.33.1
while the repository pins 4.35.0; the timings are indicative, the conclusion (option unnecessary)
does not depend on them.

---

## 5. The v8 corrections themselves, checked

* `thm:zpd-fxy` with the added unitality: tested against every unital associative algebra of
  dimension ≤ 3 over 𝔽₂ and dimension 2 over 𝔽₃, 𝔽₅, against every linear f — 14,701 pairs, no
  failure; and adversarially, adjoining a unit to the counterexample algebra gives a zpd algebra on
  which the same product *is* determined.
* The abstract's sentence on three braidings: true as now written, including for endomorphisms that
  are **not** unital — α(y)α(x) = α(yx) = α(xy) never uses α(1) = 1.
* Line 292 and line 395: the added one-line arguments are valid (from x = 1 respectively y = 1).

  **But the qualifier "in characteristic other than 2" that v8 inserted at line 292 was
  unnecessary, and that was my regression.** In characteristic 2 the Jordan product is *not*
  identically zero — x∘y = xy + yx with the plus sign — and x = 1 gives f = 2·id = 0, so
  x∘y = 0 for all x, y, which fails as soon as xy ≠ yx. So the Jordan product of a noncommutative
  algebra is not of the form f(xy) in any characteristic, by a two-case argument. Checked on
  M₂(𝔽₂): E₁₂∘E₂₁ = E₁₁ + E₂₂ ≠ 0, and f must be 0. The qualifier is now removed and the two-case
  argument is given in the text.
* Line 413: 13 is right for the braiding xy + yᵀxᵀ (recomputed), and 12 is right for xy + α(yx).
  It is also an instance of an identity, not just of a computation: for the transpose twist
  μ = (id + T)∘m with m surjective, so dim ker μ̄ = n⁴ − n² + dim ker(id + T) — 12 + 1 = 13 for
  n = 2 over an odd field, 72 + 6 = 78 for n = 3 over 𝔽₂, 72 + 3 = 75 for n = 3 over an odd field,
  all confirmed.
* Line 395's use of injectivity is sharp, not incidental: with a multiplicative but non-injective
  endomorphism the conclusion fails. Example: A = M₂(𝔽₃) × 𝔽₃, α(X,c) = (0,c) is multiplicative,
  A is non-commutative, and α(yx) = α(xy) = (0, cd) makes μ = (id + α)(xy) — verified over all
  59 049 pairs, and μ is then a function of xy. So "automorphism", not "endomorphism", is the right
  hypothesis.
* The zpd hypothesis of `cor:twisted` is necessary even for a unital α: the dual numbers with
  α = id give μ = 2xy with dim Z = 1 < 2 = dim ker, so A is not determined.
* Line 326: `§2.2` is the correction of a locator I could not read in the book itself.

---

## 7. Later adversarial findings (all recomputed here)

### 7.1 `thm:codim` is true but far weaker than it needs to be

**Lemma (rank one suffices).** If μ : A × A → A is bilinear with dim(im μ) ≤ 1 then A is determined by
μ — no associativity, no unit, no ideal hypothesis. Verified exhaustively on A = 𝔽₃²: of the 6561
bilinear forms, all 320 of rank 1 (and the single one of rank 0) determine A, while 2400 of the 6240 of
rank 2 do not. Since codim(ker f) = 1 ⟺ rank f = 1, three of `thm:codim`'s four hypotheses are
superfluous: "N a two-sided ideal", "f(1) ≠ 0" and the unitality of A. (Independently found by two
members.)

**Codimension one is nevertheless sharp.** A = K[x]/x³, f(a+bx+cx²) = a+bx: ker f = (x²) is an ideal,
f(1) = 1 ≠ 0, codim 2 — and A is *not* determined, dim Z = 6 < 7 = dim ker μ̄ over 𝔽₃ and 𝔽₅.

**Structure behind it.** If ker f is a two-sided ideal, of any codimension, then A is determined by
f(xy) iff A/ker f is zpd. The example above is consistent: A/ker f is the dual numbers, which is not
zpd.

**Proposal (not applied):** §5 would be sharper with rank f = 1 as the hypothesis, with the codimension-2
example showing sharpness. That restates the author's theorem, so it is theirs to decide.

### 7.2 The paper's two examples are one construction

`ex:dual` is `prop:matrix` restricted to a subalgebra. In M₂(𝔽₃) with α = conjugation by diag(1,−1), the
subalgebra K·I + K·E₁₂ = {[[a,b],[0,a]]} is closed, contains I, is α-invariant, and is isomorphic to
K[ε]/ε² with α acting by ε ↦ −ε; on it μ(x,y) = 2ac·I = f(xy). So the same product, on a nested pair of
algebras, is determining in both cases (12 = 12 on M₂, 3 = 3 on the subalgebra) and zpd only on M₂
(1 versus 2 on the subalgebra). This also illustrates the closure behaviour: zpd passes to products and
quotients but not to subalgebras, unitalisations or degree ≥ 2 field extensions (𝔽₄, 𝔽₉ are not zpd
while M₂(𝔽₄) is).

### 7.3 The numbers of `prop:matrix` are an identity, not a coincidence

The linearisation μ̄ for M₂ with this α has Smith invariants [1,1,1,2] over an odd field, so rank 4 and
dim ker 12 for **every** odd p (this explains the 𝔽₅ and 𝔽₇ agreement without recomputation); for the
transpose twist the invariants are [1,2,2,0], giving 13 = 13 over odd fields and 15 = 15 in
characteristic 2. In characteristic 2 the given α is the identity, the product is 2xy = 0, and everything
is determined vacuously.

### 7.4 Sharpness of `cor:twisted`

Multiplicativity of α is sufficient but not necessary: 48 of the 81 linear α on 𝔽₃ × 𝔽₃ violate
α(y)α(x) = α(xy) and still determine. It cannot be dropped altogether — A = 𝔽₃ × 𝔽₃ with
α(a,b) = (b, −a−b) gives dim Z = 0 and dim ker μ̄ = 2, so not determined (note α(1) = (0,−1), so this is
*not* an example of a unital α failing). And the zpd hypothesis cannot be dropped either: `ex:dual` with
α_τ(ε) = τε is determined exactly when τ = −1, so α = id fails on an algebra that is not zpd.

### 7.5 A third non-unital counterexample, and why unitality is exactly right

Taken from the last adversarial report and recomputed here (my first attempt disagreed only because I
mis-encoded `f`):

* A = 𝔽₂{a,b,c} with a·a = a, a·c = c, b·a = b and all other products zero is associative, not unital,
  and zpd (dim Z = dim ker = 6). With f(a) = a, f(b) = f(c) = b and μ = f(xy): dim Z = 6 < 7 = dim ker μ̄.
  Definition-level witness: β(x,y) = x_b·y_a vanishes on every μ-zero pair, but β(b,a) = 1 while
  β(a,c) = 0 although μ(b,a) = μ(a,c) = b, so no linear ψ factors β. (Verified; two independent methods
  for dim Z agree, and β's vanishing was checked pair by pair.)
* A second codimension-2 example: A = K[x,y]/(x,y)², f(1) = y, f(x) = 0, f(y) = x has ker f = Kx an
  ideal of codimension 2, f(1) ≠ 0, and dim Z = 6 < 7 = dim ker. A/ker f is again the dual numbers,
  which is not zpd — consistent with the structure of §7.1.
* **Lemma** (the best explanation of why unitality is the right hypothesis): for zpd A, A is determined by
  f(xy) iff N ∩ A² is spanned by the products lying in N, where N = ker f. A one-sided identity settles
  this through n = n·1; without one it can fail, and it fails only in dimension ≥ 3.

---

## 8. The adversarial swarm's board (eight members, all accepted)

| Direction | What it contributed |
|---|---|
| line 413, abstract, 292/395 | 12/13 confirmed with the naming load-bearing; the general identity dim ker μ̄ = n⁴ − n² + dim ker(id + T) for the transpose twist; **found that my "in characteristic other than 2" at line 292 was a regression**; injectivity at 395 shown to be sharp |
| criterion, codim, dual numbers, prop:matrix | the inner-automorphism identity of §5b — the pass's most consequential finding; prop:matrix extended to 𝔽₅, 𝔽₇, M₃(𝔽₂), M₃(𝔽₃) |
| primary structures | Smith normal form of μ̄: 12 = 12 for every odd p, 13/15 for the transpose twist; ex:dual with α_τ(ε) = τε determined iff τ = −1; codimension 1 needed |
| thm:codim | **rank μ ≤ 1 determines A**, making three of the theorem's four hypotheses superfluous; codimension 1 sharp; ker f an ideal ⟹ determined ⟺ A/ker f zpd (§7.1) |
| exhaustive small algebras | every unital algebra of dimension ≤ 3 over 𝔽₂ and ≤ 2 over 𝔽₃, 𝔽₅ against every linear f; unitality necessary (𝔽₂³) |
| Lean | **machine check of the core** (12 theorems, no `sorry`, standard axioms only), plus the right-identity and f(1)-irrelevance refinements (§6) |
| kernel reduction, closure | determined by f(xy) depends on f only through ker f, so all subspaces suffice; zpd passes to products and quotients but not to subalgebras; ex:dual = prop:matrix on a subalgebra (§7.2) |
| structural theorems | a third non-unital counterexample; a second codimension-2 example; the lemma of §7.5 |

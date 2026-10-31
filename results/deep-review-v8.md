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

## 6. The paper's core, machine-checked

`lean/ZpdCore/Zpd.lean` (added in this branch, Mathlib only, **not** part of `lake build`) checks, over
an arbitrary field and an arbitrary bilinear μ:

| Paper | Declaration | Axioms |
|---|---|---|
| `cor:criterion` | `determined_iff` | propext, choice, Quot.sound |
| `thm:zpd-fxy` | `determined_comp_of_right_id` | propext, choice, Quot.sound |
| `prop:injective` | `determined_of_injective_comp` | propext, Quot.sound |
| `cor:identity` (ii), char-2 remark | `identity_iff`, `determined_zero` | propext, choice, Quot.sound |
| `cor:twisted`, `cor:anti` | `twisted_determined`, `anti_braiding` | propext, choice, Quot.sound |
| `thm:codim` | `codim_determined`, `codim_determined_of_f_one_zero` | propext, choice, Quot.sound |
| lines 292 and 395 | `jordan_forces_comm`, `twisted_forces_comm` | propext, Quot.sound |
| the abstract's sentence | `braidings_commutative` | propext, Quot.sound |

No `sorry`, no added axiom: the twelve `#print axioms` commands report only Lean's three standard
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

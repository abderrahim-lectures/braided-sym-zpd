# Blind-spot review of v8 — the third full pass

Scope: the branch `review/v8-corrections` at `e4d4deb` (v8 as corrected, plus the stress/novelty
pass `93b3871`–`e4d4deb`). The two earlier passes are `results/deep-review-v7.md` (v7 audit,
eight agents) and `results/deep-review-v8.md` (stress, novelty, statement audit). This pass was
asked to find what **all previous AI passes missed** — including errors in their own work — and it
ran as an eight-member adversarial swarm (`smvwyrz4y`) whose every submitted finding was
re-verified by the coordinating judge before acceptance. One of the pass's own accepted findings
was subsequently **overturned by a later member and corrected** (§1.1): the adversarial structure
did its job on the review itself.

---

## 1. What this pass found

### 1.1 The Introduction's local-derivation sentence: TRUE and exactly cited — and this pass's first verdict on it was wrong (corrected)

> "The same idea shows that every local derivation of a unital zpd associative algebra is a
> derivation \citep[Example 1.10]{Bresar2021}."

**Verdict: OK.** Example 1.10 of Brešar's book is exactly this statement, with proof; the paper
cites it correctly, and "the same idea" is precise: the proof uses only Proposition 1.3(iv) — the
zpd factorisation — plus locality. The book's Example 1.10, read in the public copy of the book
(scribd.com/document/1071982505; confirmed by the judge through the search index of the same
document; the publisher's own pages are paywalled):

> "A linear map d : A → A is called a derivation if d(xy) = d(x)y + xd(y) for all x, y ∈ A. A
> local derivation is a linear map δ : A → A such that, for every x ∈ A, there exists a
> derivation d_x of A such that δ(x) = d_x(x). The standard question is whether every local
> derivation of A is a derivation. Let us show that the answer is positive if A is a unital zpd
> associative algebra. We start the proof by noticing that if x, y, z ∈ A satisfy xy = yz = 0,
> then [x δ(y) z = 0] … From Proposition 1.3 (iv) we thus see that φ₁ in particular satisfies
> φ₁(1, x) − φ₁(x, 1) = 0 … φ₂(y, 1) = φ₂(1, y) … δ(1) = 0, and so δ is a derivation."

The proof (m2, direction d1; every step re-verified by the judge):

* **Lemma 1.** If $xy = yz = 0$ then $x\,\delta(y)\,z = 0$. (Locality at the *middle* element:
  $\delta(y) = d(y)$ for a derivation $d$, and $d(y)z = d(yz) - y\,d(z) = -y\,d(z)$, so
  $x\delta(y)z = -(xy)d(z) = 0$. This is the step every earlier attempt — including the judge's —
  missed.)
* **Lemma 2.** $\delta(1) = 0$ (derivations kill 1; apply locality at 1).
* **Theorem.** For $y'z' = 0$ the bilinear map $\varphi_1(x,y) := x\,\delta(yy')\,z'$ vanishes on
  zero products (if $xy = 0$ then $x(yy') = (yy')z' = 0$, so Lemma 1 applies to the triple
  $(x, yy', z')$); Proposition 1.3(iv) gives $\varphi_1(x,y) = T(xy)$, and evaluating at
  $(1,x)$ and $(x,1)$: $\delta(xy')z' = x\delta(y')z'$ whenever $y'z' = 0$. Then
  $\varphi_2(y,z) := \delta(xy)z - x\delta(y)z$ vanishes on zero products by this identity, so
  $\varphi_2(y,z) = S(yz)$, and $\varphi_2(y,1) = \varphi_2(1,y)$ gives
  $\delta(xy) - x\delta(y) = \delta(x)y$: $\delta$ is a derivation. ∎

This explains the machine evidence gathered before the proof was found: LDer = Der on every zpd
algebra tested (the judge: T₂, M₂, K³, K⁴, T₃, Tri(M₂,F₂²,F₂) over F₂/F₃/F₅; m2 additionally:
every zpd table among all unital associative algebras of dim ≤ 3 over F₂ (16 of 76) and F₃ (144
of 801), dim 2 over F₅, all commutative dim-4 tables over F₂ (56 of 5216), plus T₂–T₄, M₂, Kⁿ,
the Tri algebras and direct products), while local non-derivations exist on non-zpd algebras
($D(x) = 1$, $D(x^2) = 0$ on $F_3[x]/x^3$ — found independently by the judge and by m2). The
zpd hypothesis is genuinely what makes it work, in every characteristic.

**Correction of this pass's own record.** This pass's citation-forensics member first reported
the locator as defective, on structural grounds: local derivations have their own section (§8.2,
"Local Derivations", pp. 139–156, with the operator-algebra literature in its bibliography), and
Chapter 1's deposited bibliography cites no local-derivation paper. The judge verified the
chapter structure — which is correct — and accepted that verdict. **Both were wrong.** A
self-contained ten-line example proved via Proposition 1.3(iv) needs no external references, and
the book contains *both*: the algebraic example in Chapter 1 and the analytic theory in §8.2.
The direct quotation (m2, confirmed by the judge through the search index of the same public
copy) settles it. This is recorded as this review's own corrected error, and as the method
lesson of the pass: **structural inference must yield to direct quotation.**

### 1.2 The body still overstates the twisted braiding (the abstract's old defect, unfixed in one place)

Section 4, line 305:

> "The twisted braiding has the form $f(xy)$ when $A$ is commutative. % claim-ok: shown by the next lines"

False as written: commutativity alone does not make $xy + \alpha(y)\alpha(x)$ a function of $xy$;
$\alpha$ must be multiplicative, which only the *next* sentence supplies. Machine certificate
(m3, direction d7): A = K[ε]/(ε²), α(1) = α(ε) = 1 (linear, not multiplicative), then
μ(ε,ε) = 1 ≠ 0 = f(ε·ε) for any linear f, over F₂, F₃, F₅. This is exactly the defect the v8
abstract fix repaired (v7-review D7); the parallel body sentence never got it. **Fixed in this
pass** (commit `9d71dce`): the sentence now reads "when $A$ is commutative **and $\alpha$ is an
endomorphism**".

**The same overstatement also stood in the Introduction** (m4, direction d6 — the third occurrence
of this defect class, and the one the other passes missed): "The identity braiding has this form,
and so does the twisted braiding **on a commutative algebra** (Corollary cor:twisted)…", where
"this form" = $f(xy)$ and the twisted braiding had been defined for a merely linear α. m4's
certificate is stronger than the §4 one because it lives on a **zpd** algebra, so it cannot be
deflected by "the sentence describes the setting of cor:twisted": A = K×K (commutative, unital,
zpd), α(x,y) = (x+y,0) linear, not multiplicative; the pairs (e₁,e₁) and (e₁,1) have the same
product e₁ = (1,0) but μ = (2,0) ≠ (3,0), so μ is not a function of xy (verified by the judge by
hand and by m4's script over F₂, F₃, F₅, F₇). **Fixed in this pass**: the clause now reads "when
$A$ is commutative and $\alpha$ is an endomorphism".

### 1.3 The v8-added abstract sentence outruns the paper's own definition

The abstract now says the symmetrized products μ_σ ask "when the algebra with that product is zpd,
**and hence when the braided-symmetric derivations of that product can be studied through zero
products**". But `def:adrabi-bsder` (and the Introduction and `rem:derivations`) define a
braided-symmetric derivation only for an **involution** σ of A⊗A, while the paper's "braiding" is
deliberately any linear map (no σ² = id), and none of `cor:twisted`, `cor:anti`, `cor:triangular`
assumes α² = id. The new sentence applies the term outside the scope of the definition that
introduces it. Two repairs are possible; m4's step-by-step audit (direction d6) shows the second is
better:

1. "…and hence, **when σ is an involution,** when the braided-symmetric derivations…" — but this
   weakens the sentence to exclude exactly the twisted braidings the paper cares about
   (`cor:twisted` does not assume α² = id).
2. Add one clause where the notion is introduced: the defining equation makes sense for **every**
   linear σ (the paper itself says these are "the derivations of the nonassociative algebra
   (A,·_σ)", which exists for all σ), and the involution is needed only by the cited Definition 3.1.
   m4's audit confirms `rem:derivations` never uses σ² = id — the mathematics is σ-free; only the
   label's definition is not.

Related, and larger: **the derivation programme is announced and never carried out.** The
abstract's motivation, the Introduction's "Remark rem:derivations takes the first step", and the
title's "Braided-Symmetric" all point at derivations; `rem:derivations` is the *only*
derivation-theoretic statement in the paper, and no theorem, corollary, example or computation in
§§3–5 involves a derivation. A referee will read the abstract as advertising content the paper
does not contain.

**And the "hence" clause itself is falsified by the paper's own example** (m6, direction d8;
witness verified by the judge). On A = K[ε]/(ε²) with α(a+bε) = a−bε — `ex:dual` itself — the
twisted product is μ_α(x,y) = 2ac·1: its **image is the one-dimensional space K·1**, while (A, μ_α)
is determined. Take D(a+bε) = a. Then D satisfies `rem:derivations`' hypothesis exactly
(μ_α(Dx,y) + μ_α(x,Dy) = 2ac + 2ac = 4ac = 0 on every μ-zero pair, i.e. whenever ac = 0 — checked
on all pairs over F₃ and F₅), but D is **not** a braided-symmetric derivation:
D(μ_α(1,1)) = D(2·1) = 2 while μ_α(D1,1) + μ_α(1,D1) = 2 + 2 = 4 ≠ 2. The S furnished by the
remark equals 2·id on the span of the products, which is K·1 — so determination constrains D only
through its value on a one-dimensional space and does not force D to be a derivation. For the
identity and swap braidings the products do span A (unital, char ≠ 2: x∘½ = x); it is the twisted
braiding — the paper's flagship — that breaks the inference. **Minimal repair:** add the span
hypothesis ("…and hence, when the products x·_σ y span A, when the braided-symmetric derivations
of that product can be studied through zero products"), or state the remark's actual conclusion
in the abstract. Author decision.

### 1.4 The novelty position is thinner than the paper presents, in two ways the stress pass did not report

(a) The **criterion and the framework are published** (Brice–Huang 2015, Theorem 2.3 — already
cited in v8 by commit `93b3871`; this pass re-verified the quotation against the published
article and adds a trap warning: the arXiv version (1110.5848) numbers the same statement
**Theorem 2.4**, so any future check against the preprint alone would produce a false defect).

(b) **NEW** (m1, direction d5): Brešar's book has a section none of the earlier passes saw —
§1.2 "Symmetrically zpd Nonassociative Algebras", Definition 1.12 — which states that zpd implies
symmetrically zpd and that **Example 2.23 — the paper's `ex:dual` algebra — shows the converse
fails**. So the paper's headline phenomenon ("determined by the twisted product but not zpd", on
K[ε]/(ε²)) is the same shape of statement, on the same algebra, as a textbook fact: a strictly
weaker determination property holds while zpd fails. The two properties are genuinely different
(the twisted product's zero set is larger), so this is not an error — but the paper cites
Example 2.23 only to identify the algebra and should acknowledge the comparison.
*Provenance caveat:* the book is paywalled; Definition 1.12 was read in a third-party full-text
copy whose contents page matches Springer's record line for line (m7), but not in the
publisher's PDF.

(c) **NEW** (m1): `thm:codim` is a rank-one statement in disguise. Its hypotheses force
$\mu(x,y) = c(x)c(y)f(1)$ — a **rank-one** bilinear map — and every rank-one bilinear map
$\mu(x,y)=\lambda(x)\lambda(y)a$ (indeed $\lambda(x)\eta(y)a$) is determining on an arbitrary
vector space: if $\lambda(x)=0$ then φ(x,·)=0, and $x=\lambda(x)e+x'$ with $x'\in\ker\lambda$
kills every mixed term, so $\varphi(x,y)=\lambda(x)\lambda(y)\varphi(e,e)=\psi(\mu(x,y))$. No
associativity, unit, ideal or codimension is used; the mirror image is Brešar's Expo. Math. 2016
Prop. 2.11 (codimension-1 ideal with $I^2\neq I$ ⟹ **not** zpd), which gives the *opposite*
conclusion for the ordinary product on the same hypotheses. Verified by the judge; machine-checked
by m1 over Q, F₂ (n = 2,3,4), F₃, F₅.

(d) `thm:zpd-fxy` is apparently new, but **not the sharp statement**. The sharp lemma is:

> If (A,μ) is zpd and **every element of A is a single μ-product** (∀b ∃x,y: μ(x,y) = b — a right
> identity for μ = m gives this uniformly), then (A, f∘μ) is zpd for every linear f.

(Proof: b ∈ ker f, write b = μ(x,y): ψ(b) = φ(x,y) = 0 since f(μ(x,y)) = 0.) This is what the
machine-checked `lean/ZpdCore/determined_comp_of_right_id` captures (right identity, no
associativity). Note the tempting stronger form with "μ̄ onto" in place of "single product" is
**false**: onto gives b as a *sum* of products and the argument breaks — refuted by the v7-review
D1 algebra (associative, zpd, A² = A so m̄ is onto, no unit; f(ae₀+be₁+ce₂) = ae₀+ce₂ makes
(A, f∘m) undetermined: dim ker = 7 > 6 = dim Z_μ; re-verified by the judge this pass).

### 1.4b New mathematical observations (m6, direction d8 — the general-braiding question)

The paper answers three specific braidings; nobody had asked when zpd of (A, m) forces zpd of
(A, m∘(1+σ)) in general. m6's exact computations (a third independent algorithm, cross-checked
against brute force) and hand proofs:

* **`cor:twisted`'s multiplicativity is sharp for determination itself**, not merely for the
  f(xy) form (the v7 review had only the latter): on the zpd algebra K³ with the *unital*,
  non-multiplicative α(e₁) = e₂, α(e₂) = e₁+e₂, the twisted product is undetermined over
  F₂, F₃, F₅, F₇ (determined over F₁₁) — with explicit certificates. So the hypothesis v8 added
  to the abstract is a genuine hypothesis, not an artefact of the proof. (It is also not
  necessary in general: on F₃², 57 of the 81 linear α give a determined twisted product while
  only 9 are multiplicative — the paper claims sufficiency only, so no defect.)
* **The second braiding (swap / Jordan product): an open question the paper skirts.** The paper
  hands x∘y to Brešar's §3.3 as separate theory. m6 proves a partial theorem — zpd + [A,A] ⊆ W
  ⟹ zJpd, where W = span{xy : x∘y = 0}, via a neat lemma ([e,x] ∈ W for every idempotent e) —
  and finds no counterexample to "unital zpd ⟹ determined by xy+yx" in 25+ algebras of dimension
  up to 16 over F₂/F₃/F₅ (T₄, M₃, M₂(dual numbers), ladders, random idempotent-generated
  subalgebras of M₃(F₃), …). The judge adds the literature connection the member could not see:
  **Alaminos–Brešar–Extremera–Villena 2020, Theorem 4.5** (surfaced by m1's novelty pass) states
  that a unital algebra over a field of characteristic ≠ 2 is zJpd if generated by idempotents —
  so *finite-dimensional* unital zpd ⟹ zJpd in char ≠ 2 follows from Theorem 2.27 + ABEV 4.5.
  m6's char-2 evidence (zJpd holds in every tested zpd algebra over F₂, where ABEV does not
  apply) suggests the characteristic hypothesis may be droppable. Worth a remark in the paper:
  the first and second braidings may be covered by one hypothesis after all.
* **`q:noncomm` looks much narrower than the paper suggests**: new positive cases M₂×M₂ (α = the
  swap automorphism), T₂×T₂, M₂×K, M₂(dual numbers) with both conjugation and swap — together
  with `prop:matrix` and the stress table's M₂(F₅/F₇), M₃(F₃), every noncommutative case ever
  tested is determined. Still no theorem.
* **Determination is not a property of A alone** (single-field observation, honestly labeled):
  on the zpd algebra F₂², 30 of the 316 linear involutions σ of A⊗A give a non-determined product
  m∘(1+σ); no second-field reproduction with integral σ was found, so this stays an F₂
  phenomenon. The paper's restriction to three structured braidings is thus a restriction of its
  theorems, not of its definition.

### 1.5 Defects in the review artifacts themselves (the previous passes' blind spots)


* **`lean/ZpdCore` (commit `e4d4deb`) did not machine-check `cor:anti`, although its README, its
  module docstring, its commit message and `results/deep-review-v8.md` §6 all said it does** (m5,
  direction d4; confirmed by the judge's own reading). What the file contained was (i) `anti_braiding`
  — only the identity $xy + \alpha(y)\alpha(x) = (\mathrm{id}+\alpha)(xy)$, **not** a determination
  statement — and (ii) it sat inside `section Commutative`, so it carried `[CommRing A]` while its
  own docstring said "No commutativity"; commutativity is exactly what `cor:anti` (the transpose on
  M_n!) is there to avoid. **Fixed in this pass** (commit `9d71dce`): `anti_braiding` now lives in a
  `[Ring A]` section and the full statement `anti_twisted_determined` (determination by the twisted
  product, no commutativity) is proved from `determined_comp_of_right_id`; the file elaborates with
  thirteen axiom-clean `#print axioms` lines.
* **m1's first report (direction d5) contained a false lemma** — the "general transfer lemma" of
  §1.4(d) above — caught by the judge's verification before acceptance, with the D1 refutation
  re-run from the original exact-arithmetic scripts; the member then retracted it and produced the
  corrected single-product lemma with an exact refutation of the onto-form over F₂, F₃, F₅, F₇
  (including the witness detail that e₁ is not a single product in the D1 algebra — precisely the
  gap between "μ̄ onto" and "every element a single product").
* The stress table of `results/deep-review-v8.md` §2.1 (M₂(F₃/F₅/F₇) 12 = 12, M₃(F₃) 72 = 72) is
  **confirmed** by this pass's independent implementation (a different method: evaluation-functional
  rank instead of the annihilator method); so are the transpose-product identities 78 = 78 (F₂) and
  75 = 75 (F₃) predicted there.
* The `aaa9d4a` characteristic-2 rewrite of the Jordan-product sentence is correct (two-case
  argument; verified, and machine-checked in ZpdCore as `jordan_forces_comm`, char-free).

### 1.6 Document-level defects in v8 at HEAD (`aaa9d4a`)

All but the last three were **fixed in this pass** (commit `9d71dce`); the remaining ones are
author decisions.

| Where | Defect | Status |
|---|---|---|
| `paper/braided-sym-zpd.tex` header | the v8 changelog ended "No claim changes except the abstract and Theorem thm:zpd-fxy" — false at HEAD: `93b3871` added the Brice–Huang attribution (a claim-level change) and `aaa9d4a` strengthened the Jordan sentence to all characteristics | fixed: the header now records the later commits |
| §3, the Brice–Huang sentence | "…by Brice and Huang [2, Theorem 2.3]; for μ the product it is Proposition 2.3" — two different results both numbered 2.3 in one sentence | fixed: "Proposition 1.3 of Brešar, recalled as Proposition 2.3" |
| `README.md` l. 30 | "Only the commits for v3 to v7 are in this repository's history" — falsified by the commits that introduced it | fixed: v3 to v8 |
| `README.md` References | omitted Brice–Huang 2015, which v8 added and cites twice, and which carries the paper's framework | fixed |
| `README.md` abstract paragraph | three inline formulas still stripped ("when f is injective", "over F_3", "no form f(xy)") while `results/fixes-applied.md` recorded the fix as done | fixed |
| Horn–Johnson citation | `[0.2.5]` rendered like a numbered result instead of a section | fixed: `§0.2.5` |
| Lean file docstrings | "**Corollary 3.5**" (line 382 — v8 numbers it `cor:anti` = Corollary 4.5; 3.5 is the pre-v6 numbering), lettered "Theorem A/B/D/E" labels (lines 228/272/299/311 — v8 has no lettered theorems), "μ = LinearMap.mul' k B" (line 66 — in this Mathlib `mul'` is the tensor map, the curried product is `LinearMap.mul`), and the `cor:twisted` docstring that made the Lean theorem look weaker than the paper when it is stronger | fixed: real numbers, `mul`, corrected docstring |
| `results/fixes-applied.md` | described a working tree that no longer exists ("nothing is committed… the author should cut a v8") | fixed: historical note added |
| Introduction | "studied since Banach and Lamperti [§7.1]" — the book's §7.1 itself credits **Kadison** and Lamperti; "Banach–Lamperti" is standard usage, so this is a naming nit, left to the author | open |
| abstract / §1.3 above | the scope and programme issues | open (author decisions) |

### 1.7 Adrabi 2026 remains unfindable (now with a complete query trail)

The paper's foundational reference — A. Adrabi, *Braided-symmetric derivations of algebras*,
preprint, 2026, cited for Definition 3.1, Remark 3.4, Section 1, Section 4 — leaves no
bibliographic trace (m7): arXiv API `au:Adrabi` → **0 results** (re-run by the judge: `totalResults = 0`);
Crossref → 5 records by the author, none matching; OpenAlex (author A5021260944) → 7 works, none
matching (the author does deposit preprints — a 2026 ResearchGate item with a DataCite DOI exists);
HAL → 0; title searches → nothing. The author is real and publishes (Comm. Algebra, Filomat,
Georgian Math. J.); the cited preprint is not discoverable by any of the five channels a referee
would use. The paper's distinctive terminology and its key structural claim (Remark 3.4) rest on
it. Recommendation: deposit it (arXiv/HAL) with a DOI, or inline Definition 3.1 and Remark 3.4
and drop the dependence — both statements are self-contained (the second is true by definition).

---

## 2. What was re-verified as correct (no defect)

* **All numbers**, for the fifth and sixth time, by three independent implementations (m3's, m5's,
  the judge's — each a different method): 417 zero pairs, rank μ̄_α = 4, dim ker = 12, tensors span
  12 (M₂(F₃), α = conjugation by diag(1,−1)); 12 = 12 ordinary product; 13 = 13 transpose braiding
  product xy + yᵀxᵀ; 12 = 12 for xy + (yx)ᵀ; and the control that makes the v8 wording
  load-bearing: the *other* transpose reading gives 12, not 13.
* **The artifact chain**: `pdf/braided-sym-zpd-v8.pdf` is character-for-character the build of the
  committed source (pdftotext diff empty; judge's forced rebuild: 274 583 bytes, same count, 0
  undefined references); the Lean file elaborates with the two unpublished modules stubbed
  (exit 0, 2.0 s), the three `M2F3Check` guards hold and are live (418 fails), and `#print axioms`
  on every paper-facing theorem reports only Lean's three standard axioms — with the single
  expected exception (`not_zeroProductDetermined_dualNumbers`, the axiom imported from the
  unpublished module).
* **`thm:bresar-idempotents`** (Brešar Theorem 2.27, the one recalled theorem the paper *uses* in a
  proof): exhaustively confirmed — all unital associative algebras of dim ≤ 3 over F₂ (76) and
  dim ≤ 2 over F₃ (9): zpd ⟺ generated by idempotents, no mismatch (m3).
* **All 18 proof steps of §§2–5, audited line by line** (m4, direction d6): no gap, no step that
  silently assumes more than its statement — an independent confirmation at HEAD of what the v7
  pass concluded for v7. This includes the two new one-line proofs and the `aaa9d4a` char-2 rewrite.
* **The Introduction's local-derivation sentence** — true and exactly cited, Example 1.10 read
  verbatim in the public copy of the book, with the proof (§1.1 above).
* **`thm:bresar-zpp`'s "Moreover" part**: proved in finite dimensions (m4 supplies the argument the
  paper only cites) and stress-tested by m7 and m4 over F₂/F₃ (m4: all 65 536 linear maps
  M₂(F₂)→M₂(F₂), 6 with an invertible in range, 0 counterexamples).
* **Theorem 2.3 of Brice–Huang 2015 exists as cited** (published version; the arXiv version
  renumbers it — see §1.4(a)).
* **Horn–Johnson §0.2.5** exists and is the transpose subsection; formatting nit: v8 writes
  `[0.2.5]` without `\S`, so it renders like a numbered result.
* The stress extensions of `prop:matrix` (M₂ over F₅, F₇; M₃(F₃) at 72 = 72) — confirmed
  independently this pass.
* The two refinements recorded in `results/deep-review-v8.md` §6 — `thm:zpd-fxy` needs only a right
  identity, and `thm:codim` does not need `f(1) ≠ 0` — are correct (judge's reading of the
  machine-checked proofs).

---

## 3. Still open (GAP)

* The exact text of the book's Definition 3.14, Theorem 2.27, Corollary 2.17 (the paper's quoted
  form), Example 2.23, and Theorem 7.2 (the book is paywalled; every locator is consistent with
  the chapter structure and the deposited bibliographies, but the item texts could not be read
  in the publisher's PDF). Two numberings are now additionally confirmed by papers citing the
  book with the same numbers: Corollary 2.17(a) and Example 2.19 (arXiv:2209.13194 quotes both),
  and Proposition 1.3 / Definition 1.1 are verbatim in the public copy, as is Example 1.10 (§1.1).
* Adrabi 2026 (see §1.7).

---

*Swarm `smvwyrz4y`, eight members, directions d1–d8; reports under `.ultramath/smvwyrz4y/m*/report.md`.
Every accepted finding above was re-verified by the judge (elaboration, re-execution, or
independent recomputation) before it entered this document.*

# Audit of `paper/braided-sym-zpd.tex` (v8) against its primary sources

Member **m6**, swarm `smvxd25ff`. Direction: citation fidelity against the Brešar 2021 monograph,
extended to the other two sources where a locator is checkable.

Every source quotation below was read out of the local PDFs (no network). Line numbers are lines of
`paper/braided-sym-zpd.tex`; labels are the paper's own `\label`s.

---

## 0. Method, pagination, artefacts

| source | extraction | page correspondence |
|---|---|---|
| `2-Zero Product Determined Algebras … (Brešar).pdf`, 186 pp | `.scratch/audit/m6/bresar.txt` (`pdftotext -layout`) | **printed page = PDF page − 8** (PDF 11 is printed 3, the chapter-1 opener; verified on PDF 12→4, 29→21, 56→48, 117→114, 129→126). Preface is printed p. v (PDF 6). |
| `1-Braided-symmetric derivations of algebras (Adrabi 2026).pdf`, 11 pp | `.scratch/audit/m6/adrabi.txt` | PDF page = printed page. |
| `3-Matrix Analysis (Horn & Johnson 2013).pdf` | `.scratch/audit/m6/hj.txt` | **printed page = PDF page − 20** (PDF 22 is printed 2). |

Both page numbers are given for every quotation: `p. 19 = PDF 27`.

Scripts (all run, all green):

* `results/audit-scripts/m6-f3-check.py` — the F_3 computation of `prop:matrix`, the "12 = 12" and the
  "13 = 13" claims.
* `results/audit-scripts/m6-inner-check.py` — `rem:inner`'s Phi-argument, numerically, for three different
  invertible `D` over F_3 and F_5.
* `results/audit-scripts/m6-quaternion.py` — the counterexample to `q:noncomm`.
* `results/audit-scripts/m6-xref.py` — the label/`\ref` graph of the `.tex` against the compiled `.aux`.

---

## 1. Brešar 2021 — every citation site

Verdicts here are about **locator + statement**. All 28 sites are listed, including the ones that are
fine, because silence is not a result.

| line | locator used | source page | what the source says (quoted) | verdict |
|---|---|---|---|---|
| 111 | Preface | p. v | "many properties of A are determined by pairs of elements whose product is zero" | FINE |
| 112 | Definition 1.1 | p. 4 | see 1.1 below | FINE |
| 113 | Preface | p. v | "The concept of a zpd algebra arose from two unrelated papers, [53] and [4]. The first one … studies commutativity preserving linear maps …; the second one … studies local derivations" | FINE |
| 114 | Preface | p. v | "the results on certain linear maps were derived from the consideration of bilinear maps that vanish on pairs of elements whose product is zero" | FINE |
| 116 | §7.1 | pp. 113–114 | "The study of zero product preserving maps has a long history. We can start by mentioning that in his classical book [28], Banach studied … His work was later completed by Lamperti [117]." | FINE |
| 117 | Theorem 7.2 | p. 114 | first sentence of Thm 7.2 | FINE |
| 118 | Theorem 7.2 | p. 114 | "c = T (1) is invertible in B and there exists a homomorphism Φ … T (x) = cΦ(x) = Φ(x)c" | FINE |
| 119 | Example 1.10 | p. 8 | "Let us show that the answer is positive if A is a unital zpd associative algebra." | FINE |
| 120 | §7.3 | p. 126 | "We saw above that Jordan homomorphisms appear naturally in the study of linear maps preserving zero products or commutativity." | FINE |
| 121 | Definition 3.14 | p. 48 | see 1.3 | FINE |
| 124 | Definition 1.1 | p. 4 | "A **nonassociative** algebra A over a field F" | FINE |
| 138 | Example 1.10 | p. 8 | as line 119 | FINE |
| 168 | Definition 1.1 | p. 4 | verbatim | FINE |
| 172 | Definition 1.1 | p. 4 / p. 5 | the abbreviation is announced in the paragraph *after* Def. 1.1, not inside it | IMPRECISE (cosmetic) |
| 174 | Definition 3.14 | p. 48 | see 1.3 | FINE |
| 182 | Proposition 1.3 | pp. 4–6 | see 1.2 | FINE |
| 199 | §7.1 | p. 113 | "Throughout, it goes without saying that the algebras A and B are associative." | FINE |
| 201 | Definition 7.1 | p. 113 | see 1.4 | FINE |
| 207 | Theorem 7.2 | p. 114 | see 1.5 | FINE |
| 219 | Proposition 1.3(iv) | p. 4 | "for every vector space X over F and every bilinear map ϕ …" | FINE |
| 253 | Proposition 1.3 | pp. 4–6 | for μ the product, the criterion *is* Prop. 1.3(i)⇔(iii) | FINE |
| 314 | Section 3.3 | pp. 48–58 | §3.3 is titled "zJpd Algebras" | FINE |
| **343** | **§2.2** | **p. 19 is §2.1** | the notation `Tri` is **defined in §2.1**, not §2.2 | **ERROR** |
| 345 | Corollary 2.17 | p. 25 | see 1.6 | FINE |
| 368 | Example 2.19 | p. 25 | "The algebra Tn (F ) of all upper triangular n × n matrices over a field F is easily seen to be of type (b)." | FINE |
| 398, 400 | Theorem 2.27 | p. 30 | see 1.7 | FINE |
| 407 | Example 2.23 | p. 26 | see 1.8 | FINE (with a caveat on the source, 1.8) |

### 1.1 Definition 1.1 — FINE, and both of the paper's assertions about it hold

Line 124 asserts "Brešar defines zpd for nonassociative algebras (Definition 1.1)". The source,
p. 4 = PDF 12:

> **Definition 1.1** A nonassociative algebra A over a field F is said to be zero product determined if,
> for every bilinear functional ϕ : A × A → F satisfying ϕ(x, y) = 0 whenever x, y ∈ A are such that
> xy = 0, there exists a linear functional τ on A such that ϕ(x, y) = τ (xy) for all x, y ∈ A.

and §1.1 opens (p. 3 = PDF 11): "Throughout the chapter, A stands for a nonassociative algebra over a
field F. This does not mean that the product in A is not associative, but it is not necessarily
associative. … We are also not assuming that A is commutative and neither that A has a unity 1."
So: yes, nonassociative, yes, over a field, and no unit. The paper's `def:bresar-zpd` (line 168) is a
verbatim copy. FINE.

### 1.2 Proposition 1.3 — FINE, including (iv) with an arbitrary vector space

p. 4 = PDF 12 (statement runs to p. 6 for (iii)):

> **Proposition 1.3** Let A be a nonassociative algebra over a field F. The following conditions are
> equivalent: (i) A is zpd. (ii) If a bilinear functional ϕ : A × A → F has the property that
> ϕ(x, y) = 0 whenever x, y ∈ A are such that xy = 0, then Σᵢ ϕ(xᵢ , yᵢ ) = 0 whenever xᵢ , yᵢ ∈ A are
> such that Σᵢ xᵢ yᵢ = 0. (iii) If zᵢ , wᵢ ∈ A are such that Σᵢ zᵢ wᵢ = 0, then the element Σᵢ zᵢ ⊗ wᵢ
> from A ⊗ A lies in span {x ⊗ y ∈ A ⊗ A | xy = 0}. (iv) **For every vector space X over F** and every
> bilinear map ϕ : A × A → X satisfying ϕ(x, y) = 0 whenever x, y ∈ A are such that xy = 0, there exists
> a linear map T : A → X such that ϕ(x, y) = T (xy) for all x, y ∈ A.

The paper's `prop:bresar-zpd` (line 182) reproduces all four with no change of hypothesis or of
quantifier; `def:determined` (line 219) is exactly (iv) with `X = V`, so the "if and only if" it asserts
is legitimate. FINE.

### 1.3 Definition 3.14 — FINE

p. 48 = PDF 56: "**Definition 3.14** An associative algebra A is zero Jordan product determined if the
Jordan algebra A+ is zero product determined." The paper's `def:bresar-zjpd` (line 174) is verbatim, and
its gloss "Here A+ has the Jordan product x ∘ y = xy + yx" matches the source's definition of A+ on
p. 36 = PDF 44: "Every associative algebra A becomes a Jordan algebra, denoted A+ , if we replace the
original product by the Jordan product x ◦ y = xy + yx." FINE.

### 1.4 Definition 7.1 — FINE

p. 113 = PDF 116: "**Definition 7.1** A linear map T from an algebra A to an algebra B is said to be zero
product preserving if, for all x, y ∈ A, xy = 0 ⇒ T (x)T (y) = 0." Followed by: "Throughout, it goes
without saying that the algebras A and B are associative." The paper's line 199 ("In them, algebras are
associative (Bresar2021, §7.1)") is exactly this sentence. FINE.

### 1.5 Theorem 7.2 — FINE, including the "Moreover" clause

p. 114 = PDF 117:

> **Theorem 7.2** Let A and B be algebras, and let T : A → B be a zero product preserving linear map. If
> A is zpd, then there exists a linear map S : A → B such that S(xy) = T (x)T (y) (x, y ∈ A). Moreover,
> if both A and B are unital and the range of T contains an invertible element of B (in particular, if T
> is surjective), then c = T (1) is invertible in B and there exists a homomorphism Φ : A → B such that
> T (x) = cΦ(x) = Φ(x)c (x ∈ A).

`thm:bresar-zpp` (line 207) reproduces this word for word, including "c = T(1)", both orders
`cΦ(x) = Φ(x)c`, and the "in particular, if T is surjective". FINE.

(For the record, the theorem is correct, and the paper only quotes it. A reader filling in the source's
proof should note that `c = T(1)` invertible uses two identities, `cT(a²) = T(a)²` (written) and
`T(a²)c = T(a)²` (not written); each gives a one-sided inverse of c. Nothing in the paper depends on this.)

### 1.6 Corollary 2.17 — FINE, exact hypotheses

p. 25 = PDF 33:

> **Corollary 2.17** The following algebras are zpd: (a) The algebra Mn (B), where n ≥ 2 and B is any
> unital algebra. (b) The algebra Tri(A1 , M, A2 ), where A1 and A2 are unital algebras generated by
> idempotents and M is a unital (A1 , A2 )-bimodule.

`cor:bresar-matrix` (line 345) copies both clauses unchanged, including "n ≥ 2", "any unital algebra",
"unital algebras generated by idempotents" and "unital (A1 , A2 )-bimodule". FINE.

### 1.7 Theorem 2.27 — FINE

p. 30 = PDF 38: "**Theorem 2.27** A finite-dimensional unital algebra A is zpd if and only if it is
generated by idempotents." `thm:bresar-idempotents` (line 400) is verbatim (it drops the letter "A").
"Finite-dimensional" and "unital" are both kept, which matters: the source itself notes on p. 31 that
the infinite-dimensional question is open. FINE.

### 1.8 Example 2.23 — FINE for the paper, but the source's own justification there is defective

p. 26 = PDF 34:

> **Example 2.23** Another natural candidate may be the algebra obtained by adjoining a unity to a zpd
> algebra A without unity that is not generated by idempotents. However, Proposition 1.19 tells us that
> such an algebra is not zpd under a rather mild assumption that A2 = A. Nevertheless, let us look more
> closely at the simplest case where A has trivial multiplication. Then A# , the algebra obtained by
> adjoining a unity to A, is a commutative unital algebra. … Thus, ϕ is of the desired form, meaning that
> A# is indeed an example of a symmetrically zpd algebra that is not zpd (**by Proposition 1.19**).

The paper's `ex:dual` (line 407) says only "an algebra of the form studied in … Example 2.23, where a
unity is adjoined to an algebra with trivial multiplication; here that algebra is Kε" — that is exactly
what the source studies, so the recall is **FINE**. Two observations a referee should record:

1. The source's parenthetical justification is not available: Proposition 1.19 (p. 15 = PDF 23) reads
   "Let A be a nonassociative algebra **such that A² = A**. Then A# … is not zpd", and a trivially
   multiplied A has A² = 0 ≠ A. The paper is right to reprove non-zpdness independently, by Theorem 2.27
   (line 413).
2. The source's claim is false in characteristic 2 (there `1 + x` is an idempotent for every `x ∈ A`, so
   `A#` *is* generated by idempotents). The paper's `\operatorname{char} K \neq 2` at line 407 is
   therefore necessary and correctly stated — it is needed for its own proof as well (`f(1) = 2 ≠ 0`).

---

## 2. Adrabi 2026 — all five sites

| line | locator | source page | verdict |
|---|---|---|---|
| 127 | Section 1 | p. 2 | FINE |
| 129 | Definition 3.1 | p. 5 | FINE |
| 134 | Section 4 | p. 9 | IMPRECISE (hypothesis on α dropped) |
| 136 | Definition 3.1 | p. 5 | FINE |
| 137 | Remark 3.4 | p. 6 | FINE |

### 2.1 Definition 3.1 and the sigma² = id question — the paper's claim is CORRECT

p. 5: "**Definition 3.1.** Let A be a K-algebra and let σ be a **K-linear involution of A ⊗ A**. A
braided-symmetric derivation for σ is a K-linear map D : A → A that satisfies identity (1), that is,
D(x ·σ y) = D(x) ·σ y + x ·σ D(y) for all x, y ∈ A."

So the source requires σ² = id (an involution), and line 129's "we do not require σ² = id, which differs
from (Adrabi 2026, Definition 3.1)" is exactly right. `def:adrabi-bsder` (line 193) is a faithful copy,
including "σ a K-linear involution of A ⊗ A". FINE.

### 2.2 Remark 3.4 — FINE

p. 6: "**Remark 3.4.** Let A be a K-algebra and let σ be an involution of A ⊗ A. Identity (1) for σ is
the Leibniz rule for the product ·σ . So BSDerσ (A) is the set of derivations of the nonassociative
algebra (A, ·σ ), in the sense of Jacobson [14, Part I]." Line 137 says precisely this. FINE.

### 2.3 Section 1 — FINE

p. 2: "Let A be an algebra over K with product µ. Let σ : A ⊗ A → A ⊗ A be a K-linear map with σ 2 = id,
for instance the swap τ (x ⊗ y) = y ⊗ x. It gives a symmetrized product
x ·σ y = µ(x ⊗ y) + µ(σ(x ⊗ y))." The paper's line 127 ("the symmetrized products of Adrabi (2026,
Section 1)") and line 130 (`x ·_σ y = μ_σ(x,y) = m(x⊗y + σ(x⊗y))`) agree with this. FINE.

### 2.4 Section 4 / line 134 — IMPRECISE: the source twists by an *involutive* α

p. 9 opens: "**4. Twisted involutions and the Leibniz defect** … This section twists the swap by an
involution α of A", and then:

> We need α2 = id for the following reason. Applying σα below twice gives x ⊗ y ↦ α2 (x) ⊗ α2 (y), so σα
> is an involution of A ⊗ A exactly when α is involutive. … Let α be involutive, of either kind. Then
> σα (x ⊗ y) = α(y) ⊗ α(x) is a K-linear involution of A ⊗ A. … The product it defines is
> x ·σα y = xy + α(y)α(x). (2)

The paper's line 134 defines "the **twisted** swap x ⊗ y ↦ α(y) ⊗ α(x), **for a linear map**
α : A → A, which twists the swap (Adrabi 2026, Section 4)". The formula and the name are the source's,
but the source's object is only defined for involutive α (automorphism or anti-automorphism). Because the
paper has already announced (line 129) that it drops σ² = id, the wider definition is the paper's own
business; attributing *that generality* to Section 4 is not. **Minimal repair:** "…which is Adrabi's
twisted swap (2026, Section 4) for an involutive α; we allow any linear α, as announced above."

---

## 3. Horn & Johnson — the transpose

Line 352: "The transpose reverses products (HornJohnson2013, § 0.2.5)."

* §0.2.5 exists and is headed "**0.2.5 The transpose, conjugate transpose, and trace**", p. 6 = PDF 26:
  "If A = [ai j ] ∈ Mm,n (F), the transpose of A, denoted by AT , is the matrix in Mn,m (F) whose i, j
  entry is a ji ; that is, rows are exchanged for columns and vice versa."
* The claimed property is on the facing page, p. 7 = PDF 27: "Both the transpose and the conjugate
  transpose obey the reverse-order law: (AB)∗ = B ∗ A∗ and **(AB)T = B T A T**."

Section number and page are both right. **FINE.**

---

## 4. Cited results that are NOT in the folder — what stays unverified

1. **`AnLiHe2015`, "Theorem 2.1"** (line 450, used for "an algebra generated by idempotents is zJpd in
   characteristic other than 2"). The paper is not in the folder, so *the number "2.1" and the exact
   wording of its hypotheses cannot be checked*. What can be checked, and is, is the content: Brešar
   p. 49 = PDF 57, "The following theorem was obtained in [24] (and partially in [85]). **Theorem 3.15**
   Let A be an (associative) unital algebra over a field F of characteristic not 2. If A is generated by
   idempotents, then A is zJpd." — and Brešar's [24] (p. 173) is "G. An, J. Li, J. He, Zero Jordan
   product determined algebras. Linear Algebra Appl. 475, 90–93 (2015)", i.e. exactly the paper's
   reference. Brešar also gives the matrix case directly, p. 52 = PDF 60: "**Corollary 3.17** The
   following algebras over a field of characteristic not 2 are zJpd: (a) The algebra Mn (B), where n ≥ 2
   and B is any unital algebra." **Verdict: IMPRECISE** — the claim is true and is verifiable from a
   source that *is* in the folder; only the locator is not. Repair: cite "An–Li–He 2015, Theorem 2.1 =
   Brešar 2021, Theorem 3.15; for M_n(B) also Corollary 3.17(a)".
2. **`BriceHuang2015`, "Theorem 2.3"** (line 253, and the attribution at line 124), including the priority claim that the criterion
   "is stated for an arbitrary bilinear μ, over a commutative ring". The paper is not in the folder and
   Brešar never states the criterion for an arbitrary μ — the nearest things are Prop. 1.3 (p. 4) and the
   ring version Prop. 2.7 (p. 21: "1 ⊗ w − w ⊗ 1 ∈ span {x ⊗ y ∈ A ⊗ A | xy = 0}"), both for the
   product only; Brešar's only pointer is p. 16: "A more detailed analysis of the topic of this section is
   given in [61]" (= Brice–Huang). **Verdict: UNVERIFIABLE.** The bibliographic data are right: Brešar's
   [61] reads "D. Brice, H. Huang, On zero product determined algebras. Linear Multilinear Algebra 63,
   326–342 (2015)", identical to the paper's entry. What remains open is only whether Theorem 2.3 of
   that paper is the μ-version over a commutative ring; a referee cannot check a priority claim on the
   strength of the folder.

---

## 5. Mathematical correctness of the paper's own claims

### 5.1 ERROR — line 448 (`rem:inner`): `(e_ii + b e_ij) − e_ii` are not idempotents

Paper: "for a matrix algebra, $M_n(B)$ is generated by the idempotents
$(e_{ii} + be_{ij}) - e_{ii}$ for $i \ne j$ with $b \in B$".

But `(e_ii + b e_ij) − e_ii = b e_ij`, and `(b e_ij)² = b (e_ij e_ij) b = 0` because `e_ij e_ij = 0`
for `i ≠ j`. So each generator named is a **square-zero** element, hence an idempotent only when
`b = 0`. The claim as written is false. The source gets it right — Brešar, proof of Corollary 2.4,
p. 19 = PDF 27:

> If i = j [the printed text reads "If i = j"; it means i ≠ j], then eii + seij is an idempotent, so
> seij = (eii + seij ) − eii is a difference of two idempotents. From seii = seij · ej i , where j = i,
> it thus follows that seii also lies in the subring generated by idempotents.

**Minimal repair:** "M_n(B) is generated by the idempotents `e_ii + b e_ij` (i ≠ j, b ∈ B, including
`e_ii` at b = 0), since `b e_ij = (e_ii + b e_ij) − e_ii` is a difference of two of them." (The rest of
`rem:inner` — the Jordan-product identity and the Phi-argument — is correct; see 5.5.)

### 5.2 ERROR — line 458 (`q:noncomm`): "affirmative … whenever α is inner" is false

Paper: "By Remark~\ref{rem:inner} the answer is affirmative, in characteristic other than $2$, whenever
$\alpha$ is inner, and every automorphism of a matrix algebra is inner; the question is therefore about
algebras admitting an involutive automorphism that is not inner."

`rem:inner` proves an **equivalence** (determined by μ_α ⇔ determined by the Jordan product) and then
answers the Jordan half only for algebras generated by idempotents. The equivalence does not by itself
give an affirmative answer for an arbitrary algebra with inner α, and the assertion is false:

> **Counterexample.** A = H, the real quaternions — associative, unital, noncommutative, char 0. Let
> α = id: an involutive automorphism, inner with D = 1. Then
> μ_α(x,y) = xy + α(yx) = xy + yx = x ∘ y, so "A is determined by μ_α" is literally zJpd. H is not zJpd
> by Brešar Example 3.19, pp. 53–54 = PDF 61–62: φ((a,x),(b,y)) = ab vanishes on anticommuting pairs,
> yet (1,0) ∘ (1,0) + (0,i) ∘ (0,i) = 0 while φ((1,0),(1,0)) + φ((0,i),(0,i)) = 1, so condition (ii) of
> Proposition 1.3 fails. Hence H is **not** determined by its twisted product, although α is inner.

Verified symbolically in `results/audit-scripts/m6-quaternion.py` (the 2×2 complex representation is
checked against the multiplication formula on all 16 basis pairs; `1∘1 = (2,0,0,0)`,
`i∘i = (−2,0,0,0)`, sum 0, φ-sum 1). **Minimal repair:** "…the answer is affirmative, in characteristic
other than 2, whenever α is inner **and A is generated by idempotents** (in particular for A = M_n(B))."

### 5.3 IMPRECISE — lines 452–453 (`rem:inner`): "not the determination itself"

Paper: "Proposition~\ref{prop:matrix} is the case $n = 2$ and $D = \operatorname{diag}(1,-1)$: what that
computation establishes is that $\mu_\alpha$ has no form $f(xy)$, not the determination itself."

`prop:matrix` states exactly "Then $A$ is determined by $\mu_\alpha$", and the computation of lines
427–432 establishes exactly that (Z_{μ_α} = ker μ̄_α, both of dimension 12 — re-verified, 5.5). Read
literally the clause denies the proposition it comments on. **Minimal repair:** "…the computation
establishes both; what no general theorem of this paper gives is the second, namely that μ_α has no form
f(xy)."

### 5.4 FINE, but worth recording — Brešar's own Example 2.23 has the defect the paper avoids

See 1.8 above. The paper's independent proof of "the dual numbers are not zpd" (Theorem 2.27) is
correct, and its `char K ≠ 2` is necessary.

### 5.5 VERIFIED numerics (no discrepancy)

`results/audit-scripts/m6-f3-check.py`, exact Gaussian elimination over F_3, A = M_2(F_3),
α = conjugation by diag(1,−1), μ_α(x,y) = xy + α(yx) = xy + α(y)α(x):

| claim in the paper | value found | verdict |
|---|---|---|
| line 427: "A ⊗ A has dimension 16 over F_3" | 16 | FINE |
| line 429: "rank 4 over F_3, so dim ker μ̄_α = 12" | rank 4, dim ker 12 | FINE |
| line 430: "Among the 81 · 81 pairs, exactly 417 satisfy μ_α(x,y) = 0" | 417 | FINE |
| line 431: "the 417 tensors span a subspace of dimension 12" | 12 | FINE |
| line 435: "dim Z = dim ker = 12 for the ordinary product" | rank 4, ker 12, 417 zero pairs, span 12 | FINE |
| line 435: "13 = 13 for the twist by the transpose" (μ = xy + (xy)ᵀ) | rank 3, ker 13, 513 zero pairs, span 13 | FINE |

(That the twisted and the Jordan shapes coincide — 417 zero pairs and dim 12 for both, at p = 3 and
p = 5, for three different invertible D, including a non-diagonal one — is `rem:inner`'s Phi-argument
confirmed independently: `results/audit-scripts/m6-inner-check.py`.)

### 5.6 Other claims checked and found correct (with the reason)

* `cor:criterion` (3.4) and its proof: (i)⇔(iii) of Prop. 1.3 applied to (A,μ) gives
  ker μ̄ ⊆ Z_μ, and Z_μ ⊆ ker μ̄ always. Correct.
* `thm:zpd-fxy` (4.1): the only use of unitality is `μ(b,1) = f(b) = 0` for `b ∈ ker f`, which needs
  `1`; the rest is Prop. 1.3(iv) plus the factorisation of ψ₀ through A/ker f ≅ im f. Correct.
* `prop:injective` (4.2): f injective ⇔ (μ(x,y) = 0 ⇔ xy = 0); then ψ∘f is the required functional.
  Correct, and no unitality needed.
* `cor:identity` (4.3) and line 309: in char 2, μ ≡ 0 forces every admissible φ to vanish, so every
  algebra is determined — correct.
* Jordan paragraph (lines 311–314): for char K ≠ 2, `x ∘ ½ = x` so `∘̄` is onto — correct; the
  "indeed" for "not of the form f(xy)" is correct (x = 1 gives f = 2id, hence yx = xy).
* `cor:twisted` (4.4): commutativity gives α(y)α(x) = α(yx) = α(xy), so μ_α = (id+α)(xy). Correct.
* `cor:anti` (4.5): α(xy) = α(y)α(x) gives the same; unitality (now assumed) is exactly what
  `thm:zpd-fxy` needs. Correct.
* `cor:triangular` (4.7): Tri(A1,M,A2) with M unital is unital (diag(1,1)), so `thm:zpd-fxy` applies;
  the second sentence is `cor:anti`. Correct.
* `thm:codim` (5.1): N = ker f a two-sided ideal, 1 ∉ N, A = N ⊕ K·1; every φ with φ = 0 on pairs with
  μ = 0 vanishes on N × A and A × N, hence φ(x,y) = c(x)c(y)φ(1,1), and f(xy) = c(x)c(y)f(1) with
  f(1) ≠ 0 admitting a left inverse g; ψ(z) = g(z)φ(1,1) works. Correct (weaker than necessary, which is
  an author decision, not an error).
* `ex:dual` (5.3): f = id+α, f(a+bε) = 2a, N = Kε an ideal, f(1) = 2 ≠ 0, c(a+bε) = a — all correct;
  the idempotents of K[ε]/(ε²) are 0 and 1 when char ≠ 2, so Theorem 2.27 gives non-zpd. Correct.
* line 417's "indeed": α an automorphism ⇒ α bijective, so α(yx) = α(xy) ⇒ yx = xy; x = 1 forces
  f = id+α. Correct.
* lines 370–371: for involutive α and char ≠ 2, id+α = 2·(projection onto the fixed space), injective iff
  the (−1)-eigenspace is 0 iff α = id. Correct.
* `rem:preserving` (3.2), `rem:derivations` (3.3): direct applications of `def:determined` to
  (x,y) ↦ T(x)T(y) and to (x,y) ↦ D(x)·_σ y + x·_σ D(y); the "if and only if S = D on the span of the
  products" is right because S is only tested there. Correct.
* `rem:inner`'s identity: xy + α(yx) = xy + (Dy)(xD⁻¹) = (xD⁻¹)(Dy) + (Dy)(xD⁻¹) = (xD⁻¹)∘(Dy) — correct;
  Φ(x⊗y) = xD⁻¹⊗Dy is a linear automorphism carrying pure tensors to pure tensors, so
  Φ(Z_{μ_α}) = Z_∘ and Φ(ker μ̄_α) = ker ∘̄. Correct, and independent of D.

---

## 6. Internal consistency (Task C)

* **No undefined or duplicate references.** `paper/build/braided-sym-zpd-v8.aux` records every
  `\newlabel` exactly once (2.1–2.6, 3.1–3.4, 4.1–4.7, 5.1–5.6) and the `.log` has no "undefined
  reference" warning. All 27 labels are distinct and each of the 24 distinct `\ref` targets exists and
  points where the prose says (the three never referenced — `def:bresar-zpd`, `def:bresar-zpp`,
  `cor:identity` — are harmless). For example:
  `cor:bresar-matrix`(a) at line 351 and (b) at lines 358/365, `cor:criterion` in the criterion proof and
  in `prop:matrix`, `thm:zpd-fxy` in `cor:identity`/`cor:twisted`/`cor:anti`/`cor:triangular`. Each of the
  recalled results carries the source's number, not the paper's, which is why there is no clash between
  "Proposition 1.3" (Brešar) and "Proposition 2.3" (`prop:bresar-zpd`). **FINE.**
* **Markup matches the mathematics.** "13 = 13" (line 435) now names its product,
  `xy + yᵀxᵀ = xy + (xy)ᵀ`, and the numbers are right (5.5). "12 = 12" likewise. "f(xy)" in the section
  title is wrapped in `\texorpdfstring`, so the PDF bookmark is `f(xy)`. The one reconstruction that is
  still odd is the `(e_ii + be_ij) − e_ii` parenthesis of line 448 (5.1), and the "not the determination
  itself" clause of line 453 (5.3).
* **Abstract / Introduction.** Every sentence is supported: criterion → `cor:criterion`; "every unital
  zpd algebra is determined by every such μ" → `thm:zpd-fxy`; "the converse holds when f is injective" →
  `prop:injective`; identity braiding → `cor:identity`; twisted braiding with α an endomorphism →
  `cor:twisted`; "the same holds on any algebra when the twist reverses products" → `cor:anti`; "the
  converse fails … dual numbers" → `ex:dual`; "a computation over F_3 … no form f(xy)" → `prop:matrix`
  plus line 417. The one overreach is `q:noncomm` (5.2), and the one imprecision is line 453 (5.3).
  The Introduction's remaining "claims" are of the form "Corollary X gives Y", and they do.

---

## 7. What I did not do

* I did not re-derive the items the brief calls established (`cor:anti` unitality; the endomorphism
  hypothesis in the abstract/Introduction; the char ≠ 2 removal in the Jordan paragraph; Brešar Prop.
  1.3). I checked them only as part of the tables above; nothing I found contradicts them.
* I did not audit the `lean/` development or the build.
* Brice–Huang 2015 and An–Li–He 2015 are absent from the folder; only their *content-as-cited-by-Brešar*
  and their bibliographic data could be checked (4).

---

## 8. Summary table

| locator | verdict | one-line repair |
|---|---|---|
| line 343, `\citep[\S2.2]{Bresar2021}` | **ERROR** | the notation is defined in **§2.1, p. 19** ("We denote it by Tri(R1,M,R2)"), not §2.2; change `\S2.2` → `\S2.1` (v8 changed it the wrong way) |
| line 448, `rem:inner` | **ERROR** | `(e_ii + b e_ij) − e_ii = b e_ij` is square-zero, not an idempotent; the idempotents are `e_ii + b e_ij`, and `b e_ij` is their difference |
| line 458, `q:noncomm` | **ERROR** | "affirmative whenever α is inner" fails for A = H (quaternions), α = id (μ_α = Jordan product, H not zJpd, Brešar Ex. 3.19, p. 53); add "and A is generated by idempotents" |
| lines 452–453, `rem:inner` | IMPRECISE | "not the determination itself" contradicts `prop:matrix`; say the computation gives both, and that the *form* is what no theorem gives |
| line 450, An–Li–He "Theorem 2.1" | IMPRECISE | content is Brešar Thm 3.15 (p. 49) and Cor. 3.17(a) (p. 52); cite those too, since An–Li–He is not checkable from the folder |
| line 134, `\citep[Section 4]{Adrabi2026}` | IMPRECISE | Adrabi's twisted swap is defined only for **involutive** α ("We need α2 = id …"); say the linear-α version is the paper's own extension |
| line 172, "as Brešar (2021, Definition 1.1) does" | IMPRECISE | the abbreviation "zpd" is announced in the paragraph after Def. 1.1, not in it; cite without the number, or say "§1.1" |
| line 253, Brice–Huang "Theorem 2.3" | UNVERIFIABLE | the paper is not in the folder and Brešar never states the μ-version; a referee cannot check the priority claim — supply the reference or weaken it |
| lines 111–121, 124, 138, 168, 174, 182, 199, 201, 207, 219, 314, 345, 368, 398, 400, 407 (Brešar) | FINE | — |
| line 352, Horn & Johnson §0.2.5 | FINE | §0.2.5 exists; `(AB)T = BT AT` is on p. 7 |
| lines 127, 129, 136, 137 (Adrabi) | FINE | — |
| lines 427–435, `prop:matrix` and the "12 = 12", "13 = 13" remarks | FINE | all six numbers reproduced exactly over F_3 (rank 4 / ker 12 / 417 / span 12; rank 3 / ker 13 / span 13) |
| `cor:criterion`, `thm:zpd-fxy`, `prop:injective`, `cor:identity`, `cor:twisted`, `cor:anti`, `cor:triangular`, `thm:codim`, `ex:dual`, `rem:preserving`, `rem:derivations`, `rem:inner`'s identity | FINE | proofs check out; see 5.6 |
| all `\ref` / numbering / abstract–Introduction support | FINE | no undefined or duplicate labels; one overreach (`q:noncomm`) and one imprecise clause (line 453) |

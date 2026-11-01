# Referee report on *Algebras Determined by a Braided-Symmetric Product*

Member m7, swarm `smvxd25ff`. My direction was a novelty/attribution audit plus consolidation.
To consolidate I checked the whole of Task A, B and C myself; this report is the result and is
self-contained — every verdict rests on a quotation from one of the three PDFs in
`.scratch/refs/`, or on a computation whose script is named.

## 0. What was audited, and how to read the line numbers

* **Paper**: `paper/braided-sym-zpd.tex`, snapshot sha256
  `9bb33779b98447e6074c29a788c0e4e9c98a2ca37983a8f7d3b5d410012f176e`, 496 lines, frozen at
  `.scratch/audit/m7/paper-snapshot-final.tex`. **Line numbers are this snapshot's.** The file was
  revised four times while this audit ran (05:09, 05:10, 05:14, 05:15), each time repairing
  something I had found; §6 verifies those repairs and quotes the text they replaced, rather than
  re-reporting the defects. Because the file is a moving target, every finding also quotes the
  sentence it is about, so it can be located by search even if the line numbers move.
* **Sources** (local, `pdftotext -layout`): Brešar 2021 (printed page numbers are in the running
  heads, so `printed = PDF − 8`); Adrabi 2026 (no printed numbers: PDF pages); Horn & Johnson,
  *Matrix Analysis* 2nd ed. (printed = PDF − 20). Texts: `.scratch/audit/m7/{bresar,adrabi,hj}.txt`.
* **Scripts** (`results/audit-scripts/`): `m7-pages.py` (phrase → PDF page and printed page),
  `m7-texrefs.py` (label/ref graph and the numbers LaTeX will print), `m7-f3-check.py` (all of
  `prop:matrix` over F₃ from the definitions), `m7-dual-check.py` (all of `ex:dual` over F₅).
* **Verdicts**: **ERROR** false or misattributed; **IMPRECISE** true but misleading or incomplete;
  **FINE** checked and correct; **UNVERIFIABLE** the cited work is not in the folder and nothing in
  the folder settles it.

Citation inventory of this snapshot: 30 Brešar sites, 6 Adrabi sites, 1 Horn–Johnson site,
2 Brice–Huang sites plus one uncited prose mention of Brice–Huang (F-C6), 1 An–Li–He site.

## 1. Headline

1. **No open mathematical ERROR remains in this snapshot.** The one I found — `q:noncomm`'s
   assertion that an inner α always makes the answer affirmative — was true of the 05:09 text and
   was repaired at 05:10; §6.6 re-verifies the replacement (correct) and records my own
   counterexample to the old sentence as an independent check.
2. **Citation fidelity**: every locator that can be checked is correct. The `Tri` locator, which
   read `\S2.2` when I started — an ERROR, the definition is in §2.1 on p. 19 — now reads `\S2.1`
   (§6.1). One item remains **UNVERIFIABLE**: Brice–Huang 2015 "Theorem 2.3" (lines 139, 158, 268).
   The An–Li–He locator (line 466) is now paired with Brešar's Theorem 3.15, which makes the claim
   checkable from the folder (§6.8).
3. **All numbers of `prop:matrix` reproduce exactly**: rank 4, `dim ker = 12`, **417** zero pairs
   out of 81·81, the 417 tensors **span 12**; `12 = 12` for the ordinary product and `13 = 13` for
   the transpose twist. `ex:dual` is confirmed independently through the criterion over F₅.
4. **Task C is structurally clean**: 63 `\ref` commands over 25 distinct labels, all resolving;
   27 labels defined, none duplicated; no hard-coded cross-reference number anywhere in the prose.
   What remains is wording (§4): the title's key term is never defined in the body, and
   `cor:identity` is the one numbered result no `\ref` points at.
5. **Novelty**: Adrabi 2026 contains no zero-product material (full-text search), so no result here
   restates the author's own preprint; Brešar 2021 contains no analogue of `thm:zpd-fxy`. But
   `cor:criterion` is Brešar's Proposition 1.3 transported, and `prop:matrix`'s determination is a
   consequence of `rem:inner` + Brešar Corollary 3.17(a) (§5).

## 2. Task A — citation fidelity

Quotes: `pdftotext -layout`, line breaks and ligatures normalised, `…` = my ellipsis.

### 2.1 Brešar 2021: every locator, with the page it really is

| # | snapshot line | paper's locator | printed page | verdict |
|---|---|---|---|---|
| A1 | 126, 128, 129 | Preface (×3) | v | FINE |
| A2 | 127, 139, 183, 188 | Definition 1.1 | 4 | FINE |
| A3 | 197 | Proposition 1.3, all four clauses | 4 | FINE |
| A4 | 234 | Proposition 1.3(iv) | 4 | FINE |
| A5 | 134, 153 | Example 1.10 (×2) | 8–9 | FINE |
| A6 | 131 | §7.1 (Banach, Lamperti) | 113–114 | FINE |
| A7 | 132, 133, 222 | Theorem 7.2 incl. "Moreover" | 114 | FINE |
| A8 | 135 | §7.3 | 126 | FINE |
| A9 | 136, 189 | Definition 3.14 | 48 | FINE |
| A10 | 329 | §3.3 | 48 | FINE |
| A11 | 188 | §1.1 (abbreviation "zpd") | 3–10 | FINE (added at 05:15) |
| A12 | 358 | `\S2.1` (Tri) | 19 | FINE now; read `\S2.2` (ERROR) until 05:09 — §6.1 |
| A13 | 360 | Corollary 2.17 (a)(b) | 25 | FINE |
| A14 | 383 | Example 2.19 | 25 | FINE |
| A15 | 413, 415 | Theorem 2.27 | 30 | FINE |
| A16 | 422 | Example 2.23 | 26 | IMPRECISE (F-A1) |
| A17 | 214 | §7.1 ("algebras are associative") | 113 | FINE |
| A18 | 466 | Theorem 3.15 (+ An–Li–He 2.1) | 49 | FINE (§6.8) |
| A19 | 477 | Corollary 3.17 (zJpd of M_n(B), Tri) | 52 | FINE (added at 05:15) |
| A20 | 474 | Example 3.19 (quaternions not zJpd) | 53–54 | FINE (§6.6) |

The quotes that carry the verdicts:

* **A2 — Definition 1.1, p. 4** (settles the paper's meta-claim at line 139, "Brešar defines zpd for
  nonassociative algebras … so any bilinear map μ on A gives a nonassociative algebra (A,μ)"):
  "*Definition 1.1* A nonassociative algebra A over a field F is said to be zero product determined
  if, for every bilinear functional ϕ : A × A → F satisfying ϕ(x, y) = 0 whenever x, y ∈ A are such
  that xy = 0, there exists a linear functional τ on A such that ϕ(x, y) = τ(xy) for all x, y ∈ A."
  Nonassociative, over a field, and the paper's Definition 2.1 (183–185) is this verbatim.
* **A3 — Proposition 1.3, p. 4**: "(iv) For every vector space X over F and every bilinear map
  ϕ : A × A → X satisfying ϕ(x, y) = 0 whenever x, y ∈ A are such that xy = 0, there exists a
  linear map T : A → X such that ϕ(x, y) = T(xy) for all x, y ∈ A." Unrestricted in X, and the
  paper keeps it so (line 203). Clauses (i)–(iii) (lines 200–202) match character for character,
  including `span{x ⊗ y ∈ A ⊗ A | xy = 0}`.
* **A5 — Example 1.10, pp. 8–9**: "A local derivation is a linear map δ : A → A such that, for every
  x ∈ A, there exists a derivation d_x of A such that δ(x) = d_x(x). … Let us show that the answer
  is positive if A is a unital zpd associative algebra." Line 134 states exactly this.
* **A6 — p. 114**: "The study of zero product preserving maps has a long history. We can start by
  mentioning that in his classical book [28], Banach studied the form of isometries of L_p([0,1]) …
  His work was later completed by Lamperti [117]." Matches line 131.
* **A7 — Theorem 7.2, p. 114**: "Moreover, if both A and B are unital and the range of T contains
  an invertible element of B (in particular, if T is surjective), then c = T(1) is invertible in B
  and there exists a homomorphism Φ : A → B such that T(x) = cΦ(x) = Φ(x)c (x ∈ A)." Theorem 2.6
  (222–225) reproduces the whole statement including this clause.
* **A13 — Corollary 2.17, p. 25**: "(a) The algebra Mn(B), where n ≥ 2 and B is any unital algebra.
  (b) The algebra Tri(A1, M, A2), where A1 and A2 are unital algebras generated by idempotents and M
  is a unital (A1, A2)-bimodule." Corollary 4.6 (360–364) keeps every hypothesis.
* **A14 — Example 2.19, p. 25**: "The algebra Tn(F) of all upper triangular n × n matrices over a
  field F is easily seen to be of type (b)." Matches line 383.
* **A15 — Theorem 2.27, p. 30**: "A finite-dimensional unital algebra A is zpd if and only if it is
  generated by idempotents." Matches Theorem 5.2 (line 416) exactly.
* **A9 — Definition 3.14, p. 48**: "An associative algebra A is zero Jordan product determined if
  the Jordan algebra A+ is zero product determined." Matches Definition 2.2 (189–191); line 193
  ("Here A+ has the Jordan product x ∘ y = xy + yx in place of xy") matches p. 36: "Every associative
  algebra A becomes a Jordan algebra, denoted A+, if we replace the original product by the Jordan
  product x ◦ y = xy + yx."
* **A11 — §1.1, pp. 3–10**: after Definition 1.1 the book says (p. 4) "Throughout the book, we will
  use zpd as an abbreviation for 'zero product determined.'" — which is what line 188 attributes to
  §1.1. Correct.
* **A17 — p. 113**: "Throughout, it goes without saying that the algebras A and B are associative."
  Line 214 ("In them, algebras are associative") is exactly this, and in the right place, since
  Definition 1.1 is not restricted to associative algebras.
* **A19 — Corollary 3.17, p. 52**: "The following algebras over a field of characteristic not 2 are
  zJpd: (a) The algebra Mn(B), where n ≥ 2 and B is any unital algebra. (b) The algebra
  Tri(A1, M, A2), where A1 and A2 are unital algebras generated by idempotents and M is a unital
  (A1, A2)-bimodule." Exactly what line 477 needs.
* **A20 — Example 3.19, pp. 53–54**: Brešar computes that ϕ((α,x),(β,y)) = αβ vanishes on every pair
  of anticommuting quaternions but fails condition (ii) of Proposition 1.3, and concludes
  "Therefore, H is not zJpd." This supports the new `q:noncomm` (§6.6).

**F-A1 (IMPRECISE, line 422, `ex:dual`).** Paper: "an algebra of the form studied in \citep[Example
2.23]{Bresar2021}, where a unity is adjoined to an algebra with trivial multiplication; here that
algebra is Kε". Source, p. 26: "Then A#, the algebra obtained by adjoining a unity to A, is a
commutative unital algebra. We claim that A# is symmetrically zpd." The identification with (Kε)# is
right, so nothing false is said — but the sentence invites the reader to think Example 2.23 proves
something about the dual numbers, whereas what it proves is that they are **symmetrically** zpd
(Definition 1.12) and hence, by Proposition 1.19, *not* zpd. **Repair**: "an algebra of the form
studied in [Bresar2021, Example 2.23] (there shown to be symmetrically zpd, and not zpd)".

### 2.2 The one item that cannot be verified: Brice–Huang 2015

**F-A2 (UNVERIFIABLE; lines 139, 158, 268).** Three claims rest on a paper that is not in the
folder:
* line 139: "zpd for such a pair, with μ an arbitrary bilinear map, is the setting of Brice and
  Huang \citep{BriceHuang2015}";
* line 158: "Our first result is a criterion, which is Proposition 1.3 of Brešar for the algebra
  (A,μ), and Theorem 2.3 of Brice and Huang for an arbitrary bilinear μ over a commutative ring" —
  a specific theorem is named with **no `\cite` key at all** (F-C6);
* line 268: "The criterion is stated for an arbitrary bilinear μ, over a commutative ring, by Brice
  and Huang \citep[Theorem 2.3]{BriceHuang2015}".

Brice–Huang, *On zero product determined algebras*, Linear Multilinear Algebra **63** (2015)
326–342, is absent. Its only trace in the folder is Brešar p. 25: "Among more interesting examples,
we mention the algebra of strictly upper triangular matrices over a field. This was shown in [61]
where one can find further examples.", with [61] = Brice–Huang (References, p. 177). **What remains
unverifiable, exactly**: the theorem number 2.3; "over a commutative ring"; and whether the
criterion there is stated for an arbitrary bilinear μ or only for a product. **Repairs**: add
`\citep{BriceHuang2015}` at line 158; and either quote the theorem or weaken to "cf. Brice–Huang,
where strictly upper triangular matrices are shown to be zpd (Brešar, p. 25)". Consequence worth
noting: if Brice–Huang really state it over a commutative ring, then Corollary 3.4 (a field) is
strictly weaker than the theorem cited for it.

### 2.3 Adrabi 2026: all six sites correct

| # | line | locator | Adrabi PDF page | verdict |
|---|---|---|---|---|
| A21 | 142 | Section 1 (symmetrized products) | 2 | FINE |
| A22 | 144, 151, 208 | Definition 3.1 (×3) | 5 | FINE |
| A23 | 149 | Section 4 (twisted swap) | 10 | FINE |
| A24 | 152 | Remark 3.4 | 6 | FINE |

* **p. 2**: "Let A be an algebra over K with product µ. Let σ : A ⊗ A → A ⊗ A be a K-linear map with
  σ² = id, for instance the swap τ(x ⊗ y) = y ⊗ x. It gives a symmetrized product x ·σ y =
  µ(x ⊗ y) + µ(σ(x ⊗ y))." Line 145 is this, with `m` for `µ`, the notation of Definition 2.4.
* **p. 5**: "Definition 3.1. Let A be a K-algebra and let σ be a K-linear involution of A ⊗ A. A
  braided-symmetric derivation for σ is a K-linear map D : A → A that satisfies identity (1), that
  is, D(x ·σ y) = D(x) ·σ y + x ·σ D(y) for all x, y ∈ A." Definition 2.4 (208–211) is this verbatim
  but for "that is, identity (1)". **The paper's meta-claim at line 144 is correct**: "we do not
  require σ² = id, which differs from \citep[Definition 3.1]{Adrabi2026}". Adrabi says so, p. 10:
  "We need α² = id for the following reason. Applying σα below twice gives x ⊗ y ↦ α²(x) ⊗ α²(y),
  so σα is an involution of A ⊗ A exactly when α is involutive."
* **p. 10**: "Let α be involutive, of either kind. Then σα(x ⊗ y) = α(y) ⊗ α(x) is a K-linear
  involution of A ⊗ A. So σα defines a symmetrized product as in Section 2. The product it defines
  is x ·σα y = xy + α(y)α(x). (2) … If α is an automorphism, then α(y)α(x) = α(yx). If α is an
  anti-automorphism, then α(y)α(x) = α(xy)." Lines 149–150 are right, and the sentence added at
  05:15 ("Brešar takes α involutive, and we do not" — read: Adrabi) closes the one gap I would have
  flagged here.
* **p. 6**: "Identity (1) for σ is the Leibniz rule for the product ·σ. So BSDerσ(A) is the set of
  derivations of the nonassociative algebra (A, ·σ), in the sense of Jacobson [14, Part I]."
  Matches line 152 exactly.

### 2.4 Horn & Johnson

**F-A3 (FINE, cosmetic; line 367).** Paper: "The transpose reverses products \citep[\S 0.2.5]
{HornJohnson2013}." §0.2.5 is "The transpose, conjugate transpose, and trace", printed **pp. 6–7**;
the sentence is on p. 7: "Both the transpose and the conjugate transpose obey the reverse-order law:
(AB)* = B*A* and (AB)^T = B^T A^T." That is precisely α(xy) = α(y)α(x) for α = transpose, i.e.
`cor:anti`'s hypothesis. Section and page right. Cosmetic: `\S 0.2.5` should be `\S0.2.5` (the
paper writes `\S7.1`, `\S2.1`, `\S1.1` elsewhere).

## 3. Task B — the paper's own mathematics

### 3.1 Verified correct (no finding)

Line-by-line reading of every definition and proof, plus computation.

* `def:determined` (232–235): the equivalence with Brešar's (iv) is exact; no gap.
* `rem:preserving` (241–246): (x,y) ↦ T(x)T(y) is bilinear into the vector space B, so
  Definition 3.1 applies verbatim; the promised special case is the first part of Theorem 2.6.
* `rem:derivations` (250–255): (x,y) ↦ D(x)·σ y + x·σ D(y) is bilinear, so the criterion yields S
  with D(x)·σ y + x·σ D(y) = S(x·σ y); D is a braided-symmetric derivation iff D = S on the span of
  the products. Correct.
* `cor:criterion` (262–273): (i)⇔(iii) of Proposition 2.3 applied to (A,μ) gives ker μ̄ ⊆ Z_μ; the
  reverse inclusion is the elementary line 260. Correct.
* `thm:zpd-fxy` (279–293): correct; unitality is used exactly once, at line 289 (μ(b,1) = f(b)),
  and the statement carries "unital".
* `prop:injective` (297–307): correct (f injective ⟺ the same zero pairs).
* `cor:identity` (311–317): true; (i) is Theorem 4.1 with f = 2·id, (ii) is Proposition 4.2; the
  characteristic-2 remark at line 324 is right (μ ≡ 0 forces every admissible φ to vanish).
* `cor:twisted` (335–338), `cor:anti` (346–349): correct; the hypotheses are used at 333 and 352.
* `cor:triangular` (372–381): correct; Tri(A₁,M,A₂) with unital A₁, A₂ has the unit diag(1,1), as
  line 379 says.
* `thm:codim` (393–408): **correct**; every step checked (the splitting x = (x − c(x)1) + c(x)1, the
  bilinearity computation, f(xy) = c(x)c(y)f(1), and the left inverse of a ↦ a·f(1), which exists
  because f(1) ≠ 0). It is much weaker than the true criterion — a referee would say so — but by the
  brief that is an author's decision, not an error.
* `ex:dual` (421–429): correct, independently confirmed (§3.3).
* `prop:matrix` (436–448): correct, every number confirmed (§3.3).
* the three "indeed" parentheticals (329, 432, 464–465): all true. 329: x = 1 forces f = 2·id, then
  yx = xy in char ≠ 2 resp. xy + yx = 0 in char 2, so a noncommutative algebra admits no such f.
  432: y = 1 forces f = id + α, then α(xy) = α(yx) and injectivity gives commutativity.
  464–465: b e_ij = (e_ii + b e_ij) − e_ii and b e_ii = (b e_ij)e_ji.

### 3.2 The numerics, confirmed

`m7-f3-check.py` (exact F₃) and `m7-dual-check.py` (F₅) recompute everything from the definitions.

**`prop:matrix`, A = M₂(F₃), α = conjugation by diag(1,−1), μ_α(x,y) = xy + α(yx):**

| quantity | paper (line) | computed |
|---|---|---|
| α involutive automorphism | 437 | yes (all 81·81 pairs) |
| rank μ̄_α (dim A⊗A = 16) | 4 (444) | **4** |
| dim ker μ̄_α | 12 (444) | **12** |
| #{(x,y) : μ_α(x,y) = 0} out of 81·81 = 6561 | 417 (445) | **417** |
| dim span of those 417 tensors x⊗y | 12 (446) | **12** |
| Z_{μ_α} = ker μ̄_α | asserted (447) | **true** |
| μ_α is not of the form f(xy) with f linear | 432 | **true**: ker m ⊄ ker μ̄_α |
| μ_α is not even a function of xy | — | **true**: 5520 pairs (x,y),(x′,y′) with xy = x′y′, μ_α(x,y) ≠ μ_α(x′,y′) |

**Line 450's two sentences:**

| product | paper | rank μ̄ | dim ker | zero pairs | dim span | criterion |
|---|---|---|---|---|---|---|
| ordinary xy | "dim Z = dim ker = 12" | 4 | **12** | 417 | **12** | true |
| transpose twist xy + (xy)^T | "dim Z = dim ker = 13" | 3 | **13** | 513 | **13** | true |

So "12 = 12" and "13 = 13" are correct. (The ordinary product also has exactly 417 zero pairs — the
paper does not claim it; it is a coincidence of this example.)

**`ex:dual` over F₅** (D = F₅[ε]/ε², α(a+bε) = a−bε, μ_α = f(xy), f(a+bε) = 2a):

| quantity | paper (line) | computed |
|---|---|---|
| α involutive automorphism and μ_α = f(xy), f = id+α | 424 | yes |
| f(1) = 2 ≠ 0, ker f = Kε a two-sided ideal of codim 1 | 425 | yes |
| Z_{μ_α} = ker μ̄_α, i.e. A *is* determined by μ_α | 426 | **true**: rank 1, dim ker 3, 225 zero pairs, span 3 |
| idempotents of A are exactly 0, 1 | 427 | yes |
| A is not zpd | 428 | **true**: rank of the product is 2, dim ker 2, but the tensors x⊗y with xy = 0 span only **1** |

The last row confirms "the dual numbers are not zpd" *through the criterion*, independently of
Brešar's Theorem 2.27; the two agree.

### 3.3 F-B1 (IMPRECISE, lines 327–328): the Jordan-criterion sentence

Paper: "When char K ≠ 2 the linear map ∘̄ : A ⊗ A → A with x ⊗ y ↦ x ∘ y is onto, because
x ∘ ½ = x. So Corollary 3.4 recovers the usual form of the zJpd criterion."
Both sentences are true, but the second does not follow from the first, and nothing later uses
surjectivity of ∘̄: Corollary 3.4 is the criterion for μ = ∘, with no hypothesis on μ. What
surjectivity gives is A² = A, the hypothesis of Brešar's *other* characterisations (Remark 1.2,
Proposition 1.13), not of the criterion quoted. **Repair**: "… is onto (x ∘ ½ = x), i.e. A² = A;
with this, Corollary 3.4 is the tensorial form of Brešar's criterion for zJpd algebras (Remark 1.2,
Proposition 1.3)" — or delete.

### 3.4 F-B2 (IMPRECISE, line 386): "injective only for α = id"

Paper: "When α is an involution and char K ≠ 2, the map id + α is twice the projection onto the
fixed points of α. It is injective only for α = id, so Proposition 4.2 gives no converse."
The first sentence is right (id + α = 2·proj_{A⁺} for A = A⁺ ⊕ A⁻). But α = id is exactly the case
in which Proposition 4.2 *does* give a converse — that is `cor:identity`(ii) with f = 2·id — so the
inference is wrong for the case it names. **Repair**: "For α ≠ id it is not injective, so
Proposition 4.2 gives no converse; for α = id it is 2·id, and the converse is Corollary 4.3(ii)."

### 3.5 F-B3 (IMPRECISE, line 110): characteristic 2 in the abstract

Paper: "The converse fails for the twisted braiding, because the dual numbers are determined by
their twisted product but are not zero product determined."
`ex:dual` assumes char K ≠ 2 (line 422), and the determination is proved by `thm:codim`, whose
hypothesis f(1) = 2 ≠ 0 fails in characteristic 2. The abstract's sentence is still true in
characteristic 2, but for a different and trivial reason (the twisted product is the zero map) that
the paper never states. **Repair**: add "in characteristic other than 2", or add a clause to
`ex:dual` covering characteristic 2.

## 4. Task C — internal consistency

`m7-texrefs.py` rebuilds the label/ref graph and recomputes the numbers the preamble will print
(all eight theorem-like environments share one counter, numbered within the section).

* **63 `\ref` commands** over **25 distinct labels** — **all resolve**; no dangling reference.
* **27 labels defined**, none duplicated. Printed numbers: Definition 2.1, 2.2; Proposition 2.3;
  Definition 2.4, 2.5; Theorem 2.6; Definition 3.1; Remarks 3.2, 3.3; Corollary 3.4; Theorem 4.1;
  Proposition 4.2; Corollaries 4.3–4.7; Theorems 5.1, 5.2; Example 5.3; Proposition 5.4;
  Remark 5.5; Question 5.6.
* Every `\ref` lands on the environment that states the thing named (checked individually).
* **No stale hard-coded cross-reference**: every "Theorem n.m"/"Definition n.m"/"§n.m" left in the
  prose is a source locator (inside `\citep[...]`) or an explicit "Proposition 1.3 of Brešar".
* `12 = 12`, `13 = 13`: mathematically right (§3.2); the second is now written "dim Z = dim ker
  = 13".

**F-C1 (IMPRECISE, line 90).** Title: "Algebras Determined by a Braided-Symmetric Product". The
phrase *braided-symmetric product* never occurs in the body, which defines a *braiding* σ, the
*symmetrized product* μ_σ, and *braided-symmetric derivations*. **Repair**: define the title's term
in the Introduction, or retitle ("Algebras Determined by a Symmetrized Product").

**F-C2 (IMPRECISE, line 311).** `cor:identity` is the only numbered result that no `\ref` points at
(only `def:bresar-zpd` and it are never referenced, and that one is a definition). The abstract's
"The converse holds when f is injective, so the identity braiding gives nothing new in characteristic
other than 2" (line 109) therefore has no pointer into the body. **Repair**: add "(Corollary 4.3)"
at line 156.

**F-C3 (IMPRECISE, line 158).** "Theorem 2.3 of Brice and Huang" is named with no `\cite` key, unlike
every other source in the paper. **Repair**: add `\citep{BriceHuang2015}` (and see F-A2: the theorem
number itself cannot be checked here).

**No findings** in Task C for: dangling or duplicate labels (none), references to non-existent
sections (none), prose numbers disagreeing with the printed counters (none), labels attached to the
wrong environment (none). The §2 introduction and the sentence after `cor:criterion`, both of which
were inaccurate at the start of the audit (a miscount of the definitions, and a phrase that made
Brice–Huang's Theorem 2.3 and this paper's Proposition 2.3 look like the same object), were
rewritten at 05:15 and are now correct (§6.10, §6.12).

## 5. Novelty and attribution (my direction)

**F-N1 (FINE).** Adrabi 2026 has no zero-product content: a full-text search for "zero product",
"zpd" and "determined" returns only unrelated phrases. Its material is braided-symmetric
derivations, the Leibniz defect, inner derivations, reduced commutative algebras and the
antisymmetrised product. No result in the paper restates the author's own preprint, and all six
citations of it are confined to definitions — appropriately and accurately (§2.3).

**F-N2 (FINE).** Brešar 2021 has no analogue of `thm:zpd-fxy`: no statement of the form
"μ(x,y) = f(xy)" occurs in the book, and "inner automorphism" does not occur at all. So
`thm:zpd-fxy`, `cor:twisted`, `cor:anti`, `cor:triangular` are new relative to the cited sources.
The one result that is not new is `cor:criterion`.

**F-N3 (IMPRECISE, line 158).** "Our first result is a criterion, which is Proposition 1.3 of Brešar
for the algebra (A,μ), and Theorem 2.3 of Brice and Huang for an arbitrary bilinear μ over a
commutative ring." The provenance is now stated (an improvement made during the audit), but the
sentence still calls "our first result" a criterion that is Brešar's (i)⇔(iii) applied to (A,μ) — as
the paper's own proof says: "Apply the equivalence of (i) and (iii) in Proposition 2.3 to the
nonassociative algebra (A,μ)". If Brice–Huang's version works over a commutative ring, this one is
also strictly weaker than the theorem cited for it. **Repair**: "Our first ingredient is Brešar's
criterion, transported to (A,μ)".

**F-N4 (IMPRECISE, line 111).** "A computation over F₃ shows that the algebra of 2×2 matrices is
determined by a twisted product that has no form f(xy)." Two mismatches with the body. (i) The
"no form f(xy)" half is not shown by the computation but by the general argument at line 432.
(ii) The determination itself does not need the computation: `rem:inner` (461–462) plus Brešar's
Corollary 3.17(a) gives it — and `rem:inner` now says exactly that ("its computation checks the
criterion of Corollary 3.4 directly in a small case, and μ_α has no form f(xy) by the argument
above"). So the abstract is now the only place that still says the computation shows determination.
**Repair**: reword the abstract along the lines of the repaired remark.

**F-N5 (note).** `ex:dual` is closely related to Brešar's Example 2.23 (dual numbers: symmetrically
zpd, not zpd). The paper's twisted product on the dual numbers is (x,y) ↦ 2·(constant term of xy), a
different product; one sentence relating the two would prevent a reader from thinking `ex:dual` is a
renaming of Example 2.23 (see also F-A1).

**F-N6 (note).** `rem:inner`'s identity is in neither source (no "inner automorphism" in Brešar; no
such identity in Adrabi §4, whose Remark 4.3 only treats derivations commuting with α). It is the
agent-authored layer the author must accept or drop. The identity is correct; every error that
occurred in its use has been repaired (§6.2, §6.6, §6.11, §6.13).

## 6. Repairs made while this audit ran — all verified

The file was revised four times during the audit (hashes `80b6866…` 05:09, `9e64ab2…` 05:10,
`9bb3377…` 05:15, with an intermediate 05:14 state). The defects below were present in the text I
first read and are now repaired. Each repair is correct; the quotations let the reader check the
replacement.

**6.1 F-X1 (was ERROR; now line 358).** `\citep[\S2.2]{Bresar2021}` → `\citep[\S2.1]{Bresar2021}`
for the definition of Tri(A₁,M,A₂). Correct: the definition is on printed p. 19, whose running head
reads "2.1 zpd Rings 19": "For any rings R1, R2 and an (R1, R2)-bimodule M, the set of all matrices
of the form [r1 m; 0 r2] … forms a ring under the usual matrix operations. We denote it by
Tri(R1, M, R2) and call a triangular ring." §2.2 begins on p. 20 and only uses Tri (Corollary
2.17(b), Example 2.19, both p. 25).

**6.2 F-X2 (was ERROR; now lines 463–466).** Old text: "M_n(B) is generated by the idempotents
(e_ii + b e_ij) − e_ii for i ≠ j with b ∈ B, and an algebra generated by idempotents is zJpd…". The
displayed elements are not idempotents (they equal b e_ij, square 0) but *differences* of the
idempotents e_ii + b e_ij and e_ii; and n ≥ 2 (and B unital) were missing. As written the sentence
did not establish the hypothesis ("generated by idempotents") of the theorem it cites. Brešar's own
proof, p. 19: "If i = j [read i ≠ j], then e_ii + s e_ij is an idempotent, so se_ij = (e_ii + s e_ij)
− e_ii is a difference of two idempotents." New text: "for a unital algebra B and n ≥ 2 the matrix
algebra M_n(B) is generated by the idempotents e_ii and e_ii + be_ij for i ≠ j with b ∈ B (indeed
be_ij = (e_ii + be_ij) − e_ii and be_ii = (be_ij)e_ji)". Correct: e_ii and e_ii + b e_ij are
idempotents ((e_ii + b e_ij)² = e_ii + b e_ij because e_ii·b e_ij = b e_ij, b e_ij·e_ii = 0,
(b e_ij)² = 0), and they generate every b e_ij and every b e_ii, hence M_n(B).

**6.3 F-X3 (was IMPRECISE; now line 230).** "Throughout, A is a unital associative algebra…" had no
scope; after the v8 edits made Theorem 4.1 and Corollary 4.5 say "unital", it was unclear whether
`cor:twisted` and `cor:identity`(i) inherited it — and both prove themselves by applying Theorem
4.1, which needs it. Now: "Throughout Sections 3 to 5, A is a unital …". Correct; the explicit
"unital" in Theorem 4.1 and Corollary 4.5 is now redundant but harmless.

**6.4 F-X4 (was IMPRECISE; now line 458).** "Let Φ be the automorphism x ⊗ y ↦ xD⁻¹ ⊗ Dy of A ⊗ A"
→ "the *linear* automorphism". Correct: x ↦ xD⁻¹ is not an algebra endomorphism unless D is central,
so Φ is an automorphism of the vector space A ⊗ A only. The proof already used only linearity.

**6.5 F-X5 (was IMPRECISE; now line 450).** "13 = 13" → "dim Z = dim ker = 13". Correct, and
verified: rank 3, dim ker 13, dim span of the 513 tensors 13.

**6.6 F-X6 (was ERROR; now lines 473–477).** Old `q:noncomm`: "By Remark 5.5 the answer is
affirmative, in characteristic other than 2, whenever α is inner, and every automorphism of a matrix
algebra is inner; the question is therefore about algebras admitting an involutive automorphism that
is not inner." The first clause is false: `rem:inner` gives only the *equivalence* of determination
by μ_α with zJpd, not zJpd itself. My counterexample to the old sentence: K any field with char ≠ 2,
A = M₂(K) × K[ε]/(ε²), α = (conj by diag(1,−1)) × id — noncommutative, unital, α involutive and
inner (D₀ = (diag(1,−1),1)); A is not zJpd because the projection A → K[ε]/(ε²) is a surjective
homomorphism of unital Jordan algebras and the dual numbers are not zJpd (Brešar Corollary 1.15,
p. 13: "If A is a unital zpd nonassociative algebra, then so is any homomorphic image of A";
char ≠ 2 + commutative: zJpd ⇔ zpd, p. 49; not zpd by Theorem 2.27, p. 30). Hence A is not
determined by μ_α.

New text: "By Remark 5.5 an inner α makes the twisted product a Jordan product in disguise, so the
answer is affirmative exactly for the zJpd algebras: it is affirmative for M_n(B) and for the
triangular algebras of Corollary 4.6(b), in characteristic other than 2, since these are zJpd
[Corollary 3.17], and negative for the real quaternions with α = id, which are not zJpd
[Example 3.19]. Every automorphism of M_n(K), for a field K and n ≥ 2, is inner (Skolem–Noether), so
in characteristic other than 2 the matrix algebras over a field are settled; the question is about
algebras admitting an involutive automorphism that is not inner." **This is correct.** Verified
point by point: `rem:inner` gives the equivalence; M_n(B) (n ≥ 2) and Tri(A₁,M,A₂) with A₁, A₂
generated by idempotents are zJpd in characteristic not 2 (Brešar Corollary 3.17, p. 52); and
Brešar's Example 3.19 ends "Therefore, H is not zJpd", so α = id on the real quaternions (an inner
involutive automorphism) is a negative case. One residual nit: the last clause turns a question
about which *pairs* (A, α) are determined into a question about *existence* of a non-inner
automorphism; "the question is which pairs (A, α) with α non-inner are determined" would be exact.

**6.7 F-X7 (was IMPRECISE; now line 477).** "every automorphism of a matrix algebra is inner" →
"Every automorphism of M_n(K), for a field K and n ≥ 2, is inner (Skolem–Noether)". Correct. The old
sentence was false for M_n(B) with B not a field: for B = K × K the entrywise swap of the two
factors is an automorphism of M_n(B) acting nontrivially on Z(M_n(B)) = Z(B) = K × K, hence not
inner.

**6.8 F-X8 (was UNVERIFIABLE in substance; now line 466).** "a unital algebra generated by
idempotents is zJpd in characteristic other than 2 \citep[Theorem 3.15]{Bresar2021}, originally
\citep[Theorem 2.1]{AnLiHe2015}". Correct: Brešar p. 49, "Theorem 3.15 Let A be an (associative)
unital algebra over a field F of characteristic not 2. If A is generated by idempotents, then A is
zJpd", preceded by "The following theorem was obtained in [24] (and partially in [85])", [24] =
An–Li–He (References, p. 177). The claim is now checkable from the folder. Suggested wording: "see
[Bresar2021, Theorem 3.15], where it is attributed to [AnLiHe2015, Theorem 2.1]" — "originally" is
vague between a citation and a priority claim.

**6.9 F-X9 (improvement; line 158 and the note after `cor:criterion`).** The Introduction now credits
the criterion to Brice–Huang as well as to Brešar, and the note after the corollary now says
explicitly that Proposition 2.3 is the statement for a product and Corollary 3.4 is that statement
applied to (A,μ). Both changes are accurate; the remaining problems with those sentences are F-N3,
F-C3 and F-A2.

**6.10 F-X10 (was IMPRECISE; now lines 173, 180–181).** §2's opening used to say "This section
recalls the notions of Brešar that we need" and "We recall two definitions and then the equivalent
forms of the first", although the section contains four definitions (2.1, 2.2, 2.5 Brešar; 2.4
Adrabi) plus Proposition 2.3 and Theorem 2.6. Now: "the notions of Brešar and of Adrabi 2026 that we
need … We recall the two basic definitions of Brešar and the equivalent forms of the first, then
Definition 2.4 of Adrabi, and finally Definition 2.5 and Theorem 2.6 of Brešar." Correct.

**6.11 F-X11 (was a gap; now line 149).** The Introduction's sentence on the twisted swap now adds
"; Brešar takes α involutive, and we do not" — a slip for *Adrabi* takes α involutive, which is what
Adrabi does (§2.3, p. 10). The mathematical content is right (the paper indeed allows any linear α);
"Adrabi" should be the name.

**6.12 F-X12 (was IMPRECISE; now line 268).** The note after `cor:criterion` used to read "for μ the
product it is Proposition 1.3 of Brešar, recalled as Proposition 2.3", which put Brice–Huang's
"Theorem 2.3" and this paper's "Proposition 2.3" side by side as if they were the same object. Now it
distinguishes them ("is the same statement for the product of a nonassociative algebra, and
Corollary 3.4 is that statement applied to (A,μ)"). Correct.

**6.13 F-X13 (was IMPRECISE; now lines 467–469).** The last sentence of `rem:inner` used to be "what
that computation establishes is that μ_α has no form f(xy), not the determination itself", which
contradicted `prop:matrix`'s own statement (the determination) and attributed to the computation
something proved at line 432. Now: "its computation checks the criterion of Corollary 3.4 directly in
a small case, and μ_α has no form f(xy) by the argument above." Correct, and it is the repair I would
have proposed.

**6.14 F-X14 (was a missing hypothesis; now line 463).** "In particular, for a unital algebra B and
n ≥ 2 the matrix algebra M_n(B) is generated by the idempotents…": "B unital" is needed (it is
Brešar's hypothesis in Corollary 2.17(a) and Corollary 3.17(a)) and is now stated.

## 7. Coverage matrix for the brief

| brief item | answered in | verdict |
|---|---|---|
| Brešar Preface | §2.1 A1 | FINE |
| Def 1.1 — nonassociative? over a field? | §2.1 A2 | FINE: both yes; the paper's meta-claim is true |
| Prop 1.3, four clauses, (iv) with arbitrary X | §2.1 A3, A4 | FINE |
| Def 3.14 | §2.1 A9 | FINE |
| Cor 2.17(a)(b), exact hypotheses | §2.1 A13 | FINE |
| Ex 1.10 (local derivations) | §2.1 A5 | FINE |
| Ex 2.19 | §2.1 A14 | FINE |
| Ex 2.23 | §2.1 F-A1 | IMPRECISE |
| Thm 2.27 | §2.1 A15 | FINE |
| Def 7.1; Thm 7.2 incl. "Moreover" | §2.1 A7, A17 | FINE |
| §§2.2, 7.1, 7.3 | §2.1 A12, A6, A8 | §2.2 was an ERROR, now FINE (§2.1); others FINE |
| Adrabi Def 3.1 / σ² = id? | §2.3 A22 | FINE; "differs from Adrabi Def 3.1" is true |
| Adrabi Remark 3.4; §1; §4 | §2.3 A24, A21, A23 | FINE |
| Horn–Johnson §0.2.5 (section and page) | §2.4 F-A3 | FINE (pp. 6–7); spacing nit |
| "Brešar defines zpd for nonassociative algebras" | §2.1 A2 | TRUE |
| "we do not require σ² = id, differs from Adrabi" | §2.3 A22 | TRUE |
| An–Li–He 2015 Thm 2.1 (absent) | §6.8 | was unverifiable; now corroborated in the folder via Brešar Thm 3.15 |
| Brice–Huang 2015 Thm 2.3 (absent) | §2.2 F-A2 | UNVERIFIABLE — the one open citation problem |
| def:determined, rem:preserving, rem:derivations | §3.1 | FINE |
| cor:criterion (proof) | §3.1 | FINE |
| thm:zpd-fxy | §3.1 | FINE |
| prop:injective | §3.1 | FINE |
| cor:identity | §3.1, F-C2 | FINE (statement); never referred to |
| Jordan-product paragraph (§4) | §3.3 | IMPRECISE (surjectivity sentence) |
| cor:twisted, cor:anti | §3.1 | FINE |
| cor:triangular | §3.1 | FINE |
| thm:codim | §3.1 | FINE (true; weaker than the true criterion — author's decision) |
| ex:dual | §3.1, §3.2 | FINE; independently confirmed over F₅ |
| prop:matrix + all its numbers | §3.2 | every number reproduces exactly |
| "12 = 12", "13 = 13" | §3.2 | TRUE |
| rem:inner (identity, Φ, idempotents, An–Li–He) | §3.1, §6.2, §6.4, §6.13, §6.14, F-N6 | identity FINE; defects repaired and verified |
| q:noncomm | §6.6, §6.7 | was ERROR; repaired and verified |
| abstract / Introduction | §3.5, F-N3, F-N4 | two IMPRECISE (F-N4, F-N3), one minor (F-B3) |
| every "indeed" parenthetical | §3.1 | all three TRUE |
| every `\ref` resolves; no duplicated numbering; markup | §4 | clean: 63 refs, 27 labels, 0 dangling |
| abstract/Introduction claims backed by later results | §4, §5 | yes, apart from the missing pointer for `cor:identity` |

## 8. Final table

| locator | verdict | one-line repair |
|---|---|---|
| 139, 158, 268 Brice–Huang "Thm 2.3" | UNVERIFIABLE | add `\citep{BriceHuang2015}` at 158 and quote the theorem, or cite Brice–Huang only for triangular matrices |
| 158 "Our first result is a criterion" | IMPRECISE | "Brešar's criterion, transported to (A,μ)" |
| 422 Brešar Ex 2.23 | IMPRECISE | say what that example proves (symmetrically zpd, not zpd) |
| 328 "∘̄ is onto … recovers the usual form" | IMPRECISE | use surjectivity only for A² = A, or delete |
| 386 "injective only for α = id, so no converse" | IMPRECISE | "for α ≠ id it is not injective"; α = id is Cor 4.3(ii) |
| 110 abstract, dual numbers | IMPRECISE | add "in characteristic other than 2", or treat char 2 in ex:dual |
| 111 abstract, F₃ computation | IMPRECISE | mirror the repaired rem:inner: the computation checks the criterion; no-f(xy) is proved at 432 |
| 90 title "Braided-Symmetric Product" | IMPRECISE | define the term in the Introduction, or retitle |
| 311 `cor:identity` | IMPRECISE | add "(Corollary 4.3)" at line 156 |
| 367 `\S 0.2.5` | FINE | write `\S0.2.5` |
| 477 last clause of `q:noncomm` | IMPRECISE | "which pairs (A, α) with α non-inner are determined" |
| 149 "Brešar takes α involutive" | IMPRECISE | "Adrabi takes α involutive" |
| 329, 432, 464–465 the three "indeed"s | FINE | none |
| 436–450 `prop:matrix` and its numbers | FINE | verified exactly (`m7-f3-check.py`) |
| 421–429 `ex:dual` | FINE | verified independently over F₅ (`m7-dual-check.py`) |
| 393–408 `thm:codim` | FINE | true (and weak; author's decision) |
| 279–307, 335–381 `thm:zpd-fxy`, `prop:injective`, `cor:twisted`, `cor:anti`, `cor:triangular` | FINE | none |
| 232–273 `def:determined`, `rem:preserving`, `rem:derivations`, `cor:criterion` | FINE | none |
| 358 `Tri` `\S2.1` | FINE | (read `\S2.2` — an ERROR — at the start of the audit; corrected) |
| 463–466 idempotents of M_n(B) | FINE | (was an ERROR: differences of idempotents, n ≥ 2 and B unital missing; corrected) |
| 230 "Throughout Sections 3 to 5" | FINE | (scope was undefined; corrected) |
| 458 "linear automorphism Φ" | FINE | (was "automorphism of A ⊗ A"; corrected) |
| 450 "dim Z = dim ker = 13" | FINE | (was "13 = 13"; corrected) |
| 466 An–Li–He "Thm 2.1" | FINE | reword "originally" as "see [Bresar2021, Theorem 3.15], attributed there to …" |
| 473–477 `q:noncomm` | FINE | (was an ERROR; corrected, and verified against Brešar Cor 3.17 and Ex 3.19) |
| all 63 `\ref` / 27 labels | FINE | none — no dangling, no duplicate, no stale number |

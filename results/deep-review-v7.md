# Deep correctness review — *Algebras Determined by a Braided-Symmetric Product*, v7

Reviewer pass over the whole repository at commit `977d4ab` (`braided-sym-zpd v7`): the LaTeX source
`paper/braided-sym-zpd.tex`, the shipped PDF, `README.md`, and `lean/Research/BraidedSymZpd/BraidedSymZpd.lean`.

## Headline

**The mathematics holds up with one exception, and the exception is real.** As printed in v7,
`thm:zpd-fxy` is *false* without the unitality hypothesis its proof uses: a counterexample is given
under D8, and it is the one place in the paper where a stated result fails. Everywhere else I found no
false statement and no real proof gap — in the criterion, the injective converse, the codim‑1 theorem
and the matrix proposition — and I re-derived or recomputed every claim that can be checked
independently, including the `F_3` computation, the paper's only genuinely new "computed" statement.

**The defects are in the artifacts around the paper**, not in its theorems: a stale version string
visible in the published PDF, a symbol left dangling by the v7 edit, an abstract still advertising the
v6 formulation, a README that lost all its inline mathematics, a promise of git tags that do not exist,
build instructions for a Lean file that has never elaborated, one wrong citation locator, and one
abstract sentence that is stronger than the theorem behind it.

Severity at a glance: D8 is a false statement in v7 as printed and comes first in importance;
D1–D5 are visible in the published artifacts and should be fixed before the next release.

---

## 1. Checked mechanically

| Claim | Method | Result |
|---|---|---|
| Paper compiles | `latexmk -pdf` | OK, 7 pp., no undefined references, no overfull-box errors |
| Shipped `pdf/braided-sym-zpd-v7.pdf` is the build of the shipped source | `pdftotext` diff | identical apart from the `\today` compile date — **in sync** |
| `prop:matrix`: 417 zero pairs among 81·81 | independent Python over F₃ | **417** ✓ |
| `prop:matrix`: `rank μ̄_α = 4`, so `dim ker = 12` | Python elimination + analytic argument (image contains E₁₂, E₂₁, E₁₁+E₂₂, 2E₁₁) | **4 / 12** ✓ |
| `prop:matrix`: the 417 tensors span dimension 12 | Python, left-to-right *and* right-to-left pivoting; rank of the transposed matrix; sympy over GF(3) | **12** ✓ |
| `prop:matrix`: conclusion `Z_μ = ker μ̄` | *not* just dimensions: explicit 12-vector kernel basis, each vector checked to lie in span(Z); with Z ⊆ ker always, this gives equality | **Z = ker** ✓ |
| "12 = 12 for the ordinary product" | same pipeline | **417 / 12 / 12 / Z = ker** ✓ |
| "13 = 13 for the twist by the transpose" | same pipeline, α = transpose as a braiding (`xy + yᵀxᵀ`) | **513 / 13 / 13 / Z = ker** ✓ |
| Twisted product "has no form f(xy)" | found a pair with `xy = 0 ≠ μ(x,y)` | ✓ true (`x = E₁₂, y = E₁₁`) |
| 417 is not an artefact of the twisted product | counted the pairs with `uv + vu = 0` (Jordan product) in M₂(F₃) | also **417** ✓ |
| `ex:dual` (dual numbers) | same criterion over F₅: twisted product rank μ̄ = 1, dim ker = 3, span(Z) = 3 → determined; associative product rank 2, dim ker 2, span(Z) = 1 → **not** zpd | ✓ both halves hold without invoking Brešar Thm 2.27 |
| Lean `M2F3Check` block (66 lines, core Lean only) | `lean` on the extracted namespace | **compiles; all three `#guard`s pass** (417, rank 12, rank μ̄ 4) |
| Lean file *as a whole* | `lake build`; then with both missing modules stubbed | **does not elaborate even then**: two errors at 124:6 and 233:6 (D5) |
| Lean file free of `sorry`/`axiom`/`native_decide`/`unsafe` | grep | none ✓ |
| Lean encoding faithful | read `mul`, `alpha`, `mu` | `alpha` = conjugation by diag(1,−1) (negates off-diagonals) ✓, `mu x y = xy + α(yx)` ✓ — matches the paper |

The Lean `#guard`s give exactly the numbers I computed independently, which is good evidence that
the Lean computation is not decorative.

## 2. The mathematics, claim by claim

- **Def. `def:determined`, Prop. `prop:bresar-zpd`, Cor. `cor:criterion`.** The equivalence
  "A determined by μ ⟺ Z_μ = ker μ̄" is applied correctly: condition (iii) of Brešar's Proposition 1.3
  specialised to (A, μ) says exactly `ker μ̄ ⊆ Z_μ`, and `Z_μ ⊆ ker μ̄` is automatic. No
  finite-dimensionality or surjectivity is needed. **Correct.**
- **Thm. `thm:zpd-fxy`** (A zpd ⟹ A determined by `f(xy)`). The one non-obvious step is
  `ker f ⊆ ker ψ₀`, obtained from `μ(b,1) = f(b) = 0`; then ψ₀ factors through `A/ker f ≅ im f` and is
  extended to A. This is right and complete — but it **uses the unit** (`x·1`), which the statement
  does not mention (D8).
- **Prop. `prop:injective`.** `f` injective ⟹ `μ(x,y)=0 ⟺ xy=0`; then `φ(x,y) = (ψ∘f)(xy)`. **Correct.**
- **Cor. `cor:identity`.** (i) is the theorem with `f = 2·id`; (ii) is the proposition, `2·id`
  injective iff char ≠ 2. The char‑2 remark (μ ≡ 0 ⟹ every φ is 0 ⟹ every algebra is determined) is
  also correct. **Correct.**
- **Cor. `cor:twisted`, Cor. `cor:anti`, Cor. `cor:triangular`.** In all three the identity
  `α(y)α(x) = α(xy)` is exactly what is needed, and it holds for an endomorphism (commutative case)
  and for an anti-endomorphism alike; α need not be unital or injective. **Correct.**
- **Thm. `thm:codim`.** The splitting `x = (x − c(x)1) + c(x)1` gives `φ(x,y) = c(x)c(y)φ(1,1)` and
  `f(xy) = c(x)c(y)f(1)`; `f(1) ≠ 0` supplies a left inverse `g` of `a ↦ a f(1)`. Every hypothesis is
  used and only assumed ones are used. (Consistency check: the hypotheses force `c(1) = 1`, so they
  are not contradictory.) **Correct.**
- **Ex. `ex:dual`.** `f = id+α` has kernel `Kε`, a codim‑1 ideal, `f(1) = 2 ≠ 0`; the only idempotents
  of `K[ε]/(ε²)` are 0 and 1 (from `a² = a`, `2ab = b`), so it is not generated by idempotents, and
  Brešar's Theorem 2.27 gives "not zpd". **Correct; I checked the idempotent claim independently.**
  The "not zpd" half moreover admits a direct proof that avoids Theorem 2.27: φ(x,y) = ad for
  x = a+bε, y = c+dε vanishes on every zero product (if a = 0 trivially; if a ≠ 0 then c = 0, and then
  d = 0), while φ(1,ε) = 1 ≠ 0 = φ(ε,1) although 1·ε = ε·1, so it does not factor through the product.
- **Prop. `prop:matrix`.** Verified, see §1. The proof as written faithfully describes a computation
  that does what it says.
- **Remark `rem:derivations`.** "D is a braided-symmetric derivation iff S = D on span of products"
  follows correctly from the definition of "determined".
- **Framing claims** (abstract/intro): the three symmetrized products are `2xy`, `xy+yx`,
  `xy+α(y)α(x)` — correct; "the twisted product describes algebras the zpd theory does not reach" —
  correct (dual numbers).

Beyond these hand checks, the following were established exhaustively by independent reviewers and
reproduced here: the criterion Z_μ = ker μ̄ against the *definition* for all bilinear μ on 2-dimensional
spaces over F₂ (256) and F₃ (6561) and 3000 random μ on 3-dimensional spaces, no mismatch; `thm:zpd-fxy`
and `prop:injective` for every unital algebra of dimension ≤ 3 over F₂ and ≤ 2 over F₃, F₅ against every
linear f (about 55 000 pairs, no failure); `thm:codim` on 165 (algebra, f) cases including a
noncommutative instance in Tri(M₂(F_p)) where Z_μ = N⊗A + A⊗N = ker μ̄ holds with dimension 8 = 8; the
recalled Theorems 2.27 and 7.2 on the small unital algebras; and the content of Cor 2.17(b), which can be
proved outright: [[1,m],[0,0]] is idempotent because m·1 = m, and [[0,m],[0,0]] is its difference with
[[1,0],[0,0]], so M lies in the span of the idempotents.

## 3. Defects

### D1. The published PDF says "Preprint version 2", everything else says v7 — *visible artifact bug*
`\newcommand{\paperversion}{2}` (`paper/braided-sym-zpd.tex:53`) prints "Preprint version 2, compiled
2026/10/17" on the title page of `pdf/braided-sym-zpd-v7.pdf`, whose file name, README and commit all
say v7. The counter has not been touched since v2.
**Fix:** `\paperversion{7}`, or drop the macro and rely on the tag.

### D2. `q_\circ` is undefined — a regression introduced by the v7 edit
`paper/braided-sym-zpd.tex:290`: "When char K ≠ 2 the map $q_\circ$ is onto…". In v6 the companion
`q_μ : (A⊗A)/Z_μ → A` was defined (`git show HEAD~1:paper/braided-sym-zpd.tex`, line 157) and used
throughout the proof of the criterion. v7 replaced that proof by the citation of Brešar Prop. 1.3 and
deleted the defining sentence, but left this one use. With Brešar's Proposition 1.3 doing the work,
the sentence is also redundant: the criterion no longer needs any surjectivity.
**Fix:** delete the sentence, or define `q_∘ : A⊗A → A, x⊗y ↦ x∘y` first.

### D3. `README.md` has lost all inline mathematics
The file contains **zero `$` characters**. Three visible damages in the summary paragraph (line 8):
"…on a commutative algebra, **has the form** f(xy)" (the subject μ is gone), "determined by every
such **.**" (μ gone), "the algebra of **2 2** matrices" (the × is gone).
**Fix:** restore the three expressions.

### D4. README promises git tags that do not exist
"A version is also a tag of this repository" — `git tag` is empty, and the history begins at v3
(seven commits; v1/v2 absent). Either create the tags or reword.

### D5. `cd lean && lake build` does not work, and the file does not elaborate even when it can start
Four independent reasons:
1. the file imports `Research.Zpd.Basic` and `Research.Zpd.DualNumbers`; those modules are **not in
   the repository** (479 of the 545 lines depend on them, including
   `Research.Zpd.ZeroProductDetermined` and `not_zeroProductDetermined_dualNumbers`). The README's
   description "Lean 4 files that check computations and lemmas of the paper (mathlib only)" (line 24)
   is false as well;
2. **even with both modules stubbed, the file does not elaborate.** It fails at 124:6 and 233:6 with
   *Alternative `zero` has not been provided*: the two `induction` blocks over $B\otimes_k B$ in
   `mapDetermined_iff_injective` and `mapDetermined_iff_injective'` omit the `zero` branch. Reproduced
   against the installed Mathlib (Lean 4.33.1): a minimal `induction s with | tmul … | add …` on a
   tensor fails with exactly that message and compiles once `| zero =>` is added. The artifact has
   therefore never been elaborated, and its failure is not only the missing dependency;
3. `lakefile.toml` pins mathlib to `rev = "master"` — not a reproducible pin — and current master
   demands `lean4:v4.36.0-rc2`, while `lean-toolchain` pins `v4.35.0`. Running `lake build` therefore
   **rewrites the tracked `lean-toolchain`** (I triggered this and restored it) and pulls 625 MB;
4. no `lake-manifest.json` is committed.
**Fix:** vendor the two `Research/Zpd/*.lean` modules, add the `zero` branches, pin mathlib to a
tag/commit, commit the manifest, and align `lean-toolchain`.

### D6. Citation locator: `Tri(A₁,M,A₂)` is cited to §2.1, which is "zpd Rings"
`paper/braided-sym-zpd.tex:321` cites `[§2.1]` **twice in a row** for the notation `Tri(A_1,M,A_2)`.
The book's §2.1 is "zpd Rings"; the construction is an example of a zpd algebra, i.e. §2.2
("Examples and Non-examples of zpd Algebras"), which Corollary 2.17(b) then uses.
**Fix:** `[§2.2]`, once.

### D7. The abstract (and README) is stronger than Cor. `cor:twisted`
"For the symmetrized products of three braidings on a commutative algebra, μ has the form f(xy)"
is **false for a merely linear α**, which is what §1 allows when it defines the twisted swap. Take
`A = K[ε]/(ε²)` (commutative), `α(1) = 1`, `α(ε) = 1`: then `μ(ε,ε) = α(ε)α(ε) = 1 ≠ 0 = f(0)`, so μ
is not `f(xy)`. §4 states the result correctly, with "α an algebra endomorphism".
The repair is exactly sharp: if moreover α(1)=1 then μ_α is of the form f(xy) **iff** α is
multiplicative (put x=1 to get f(y)=y+α(y) and compare), so "endomorphism" is not merely sufficient
but the exact missing hypothesis.
**Fix:** add "for α an endomorphism" to the abstract and README sentences.

### D8. `thm:zpd-fxy` is false as stated: the unit is needed
"Let A be zpd, let f : A → A be linear" — the proof uses `μ(b,1) = f(b)` for b ∈ ker f. Because §3's
preamble assumes A unital, and the abstract and the introduction both say "unital", I first recorded this
as statement hygiene only, remarking that the hypothesis could be dropped rather than added (ψ₀ vanishes
on A² ∩ ker f, so extend ψ₀ from A² to A killing ker f). **That reasoning is wrong, and the theorem is
false without unitality.** From b = Σ xᵢyᵢ and f(b) = Σ μ(xᵢ,yᵢ) = 0 one cannot conclude Σ φ(xᵢ,yᵢ) = 0,
and applying Brešar's condition (ii) to μ would assume what is being proved.

*Counterexample* (found by a reviewer; recomputed here over F₂, F₃, F₅, F₇). Let A = ⟨e₀,e₁,e₂⟩ with
e₀² = e₀, e₀e₁ = e₀e₂ = e₂, e₁e₀ = e₁ − e₂, all other products zero. Then A is associative, A² = A, has
no unit, and **is** zpd: dim Z_m = dim ker m̄ = 6. Take f(a,b,c) = (a,0,c), so ker f = ⟨e₁⟩, and
μ(x,y) = f(xy). Then dim Z_μ = 6 but dim ker μ̄ = 7, so A is *not* determined by μ. Explicitly,
φ(x,y) = x₀(y₁+y₂) kills every μ-zero pair, while φ(e₀,e₁) = 1 and φ(e₁, −e₀+e₂) = 0 although
μ(e₀,e₁) = μ(e₁,−e₀+e₂) = e₂.
**Fix (applied):** the statement now says "Let A be a unital zpd algebra". The hypothesis must be *added*,
not dropped.

### D9. Two change logs for v7 that describe different changes
The `.tex` header says v7 = intro reworked around Brešar Thm 7.2 + `rem:preserving` + `prop:matrix` +
"claims added: `cor:triangular`, `prop:matrix`". The README's v7 entry says v7 = retitling to
`braided-sym-deriv` + criterion now cited from Prop. 1.3 + `rem:derivations`, and does not mention
the two new claims. Both edits are in the commit; each log describes half of it.

### D10. Stale or incorrect statements in the Lean file
- line 45: "The noncommutative case (for example, M₂(F₃) with the transpose) is open" — but the same
  file then checks M₂(F₃), and the **transpose** case is settled affirmatively by `cor:anti`, since the
  transpose reverses products. Wrong twice.
- the module docstring advertises `symProdLinear` and `mapDetermined_symProd_std_iff_zJpd` as the file's
  main definitions and results; **neither is defined anywhere in it** (both occur only in the docstring,
  lines 26, 35 and 102).
- `cor:twisted` is formalised as `mapDetermined_twisted_of_comm_zpd` for `α : B →ₐ[k] B`, i.e. a
  **unital** endomorphism, whereas the paper's corollary only needs α multiplicative (no theorem of the
  paper assumes α(1) = 1). The formal statement is strictly weaker than the published one.
- lines 153 and 172 refer to `BraidedSymmetric.lean`, and line 45 to `formalization-debt.md`; neither
  file is in this repository.

### D11. Ambiguity in "the twist by the transpose" (`paper/braided-sym-zpd.tex:413`)
The paper writes the twisted product both as `xy + α(y)α(x)` (the braiding) and as `xy + α(yx)`
(`prop:matrix`); these agree for automorphisms but not for anti-automorphisms. For α = transpose the
two readings give **13 = 13** (braiding, as printed ✓) and **12 = 12** (`xy + α(yx)`, also determined,
which I computed). The printed number is right for the intended reading; the notation should say
which product is meant.

### D12. The abstract advertises a "quotient criterion" that the v7 body no longer states
`paper/braided-sym-zpd.tex:72`: "The answer is a quotient criterion that needs no surjectivity
hypothesis." In v7 the criterion is the kernel equality `Z_μ = ker μ̄`; the words "quotient" and
"surjectivity" occur nowhere else in the body except inside the recalled Theorem 7.2. Same root cause
as D2: v6 stated the criterion as "`q_μ` is injective" (with a left inverse replacing an inverse, and no
surjectivity assumed), and v7 deleted that formulation without touching the abstract. Low severity —
the kernel equality is of course equivalent to injectivity on `(A⊗A)/Z_μ` — but the abstract currently
describes a presentation the paper does not give.

### D13. The abstract names an object that does not exist
`paper/braided-sym-zpd.tex:71`: "For the symmetrized products of braided-symmetric derivations, this
asks when the algebra with that product is zero product determined." A symmetrized product is attached
to a *braiding*; a braided-symmetric derivation is a *derivation of* `(A, ·_σ)`. There is no
"symmetrized product of a derivation" anywhere in the paper. Related: the title and the keywords say
"braided-symmetric product", a term that occurs in no line of the body (the body says "symmetrized
product" and "braided-symmetric derivation"). Added in v7.

### D14. §2 restates the symmetrized product with `μ` for the algebra product
`paper/braided-sym-zpd.tex:173`: "the symmetrized product `x ·_σ y = μ(x⊗y) + μ(σ(x⊗y))`, where `μ` is the
product of `A`". But `μ` is the arbitrary bilinear map of §§3–5 (line 199), the product is `m` (line 108),
and `μ` is defined on `A×A`, not on `A⊗A`. The formula also disagrees *in notation* with the
Introduction's `x·_σ y = m(x⊗y + σ(x⊗y))` (line 117) — the two agree mathematically, so this is a
notational clash, not an error, but it sits immediately before `def:adrabi-bsder`, which therefore has
two incompatible definitions of `·_σ` around it.

### D15. The v7 header comment misattributes one change and omits others
`paper/braided-sym-zpd.tex:1` says "Acknowledgments removed" as a v7 change, but the section was deleted
one commit earlier, in v6 (`git diff 81395eb e56e0a7`). The header also omits two real v7 edits: the
abstract clause "as the transpose does on matrices" was deleted, and "`M_n(K)` is determined by
`xy + yᵀxᵀ`" was replaced by the more general "Corollary `cor:anti` applies to `M_n(K)` and to the
transpose, and to every linear `α` that reverses products".

### D16. README changelog order
It announces "newest first" but lists **v1** (2026-09-25) before **v2** (2026-09-27); and neither v1 nor
v2 exists anywhere in the repository history (see D4).

### D17. Cosmetic
- duplicate citation of one locator (`[§2.1] … [Section 2.1]`, line 321);
- three labels are never `\ref`'d (`cor:identity`, `def:bresar-zpd`, `def:bresar-zpp`) — harmless.

### D18. The Introduction credits matrix algebras to Cor. `cor:triangular`
Line 129: "So the zpd algebras of Brešar, such as matrix algebras and triangular algebras [Corollary
2.17], are determined by all these products (Corollary `cor:triangular`)." But `cor:triangular` covers
only `Tri(A₁,M,A₂)`; $M_n(B)$ is not of that form and is reached by `thm:zpd-fxy` together with
Corollary 2.17(a). As written the sentence reads as a claim about both families.
**Fix:** cite `thm:zpd-fxy` (and Cor. 2.17) for matrix algebras, `cor:triangular` for the triangular ones.

### D19. Two unproved assertions (both true, one line each)
Line 395: "When α is an automorphism of a noncommutative algebra, the twisted product $xy+\alpha(yx)$ is
not of the form $f(xy)$, and Theorems `thm:zpd-fxy` and `thm:codim` do not apply"; and line 292: the
Jordan product "is not of the form $f(xy)$ on a noncommutative algebra". Both are true — $y=1$ forces
$f=\mathrm{id}+\alpha$ resp. $f=2\,\mathrm{id}$, and then $\alpha(yx)=\alpha(xy)$ resp. $xy+yx=2xy$
gives $yx=xy$, contradicting noncommutativity in characteristic ≠ 2 — but the text gives no argument for
either, and neither sentence carries a `claim-ok` marker.
**Fix:** one line of proof, or a parenthetical.

## 4. Verified against the primary source (Brešar 2021)

| Locator in the paper | Status |
|---|---|
| Definition 1.1 (zpd, nonassociative) | **verbatim match** ✓ |
| Proposition 1.3 (i)–(iv) | **verbatim match** ✓ (other authors cite it as `[3, Proposition 1.3]` for the tensor form) |
| Corollary 2.17(a) (Mₙ(B) zpd) | ✓ (cited as `[3, Corollary 2.17 (a)]` elsewhere) |
| Theorem 2.27 (finite-dim. unital zpd ⟺ generated by idempotents) | ✓ — and not a slip for Theorem 3.7: 3.7 is the numbering in Brešar's Expo. Math. 34 (2016) paper, of which the book's Thm 2.27 is the book version (Jia–Xiao cite the book as `[5, Theorem 2.27]`, the paper as `[6, Theorem 3.7]`) |
| §2.1 for `Tri(A₁,M,A₂)` | ✗ §2.1 is "zpd Rings" — should be §2.2 (D6) |
| Example 2.19 (Tₙ(F)), Example 2.23 (adjoin a unity) | **content confirmed** against the published *Expo. Math.* 34 (2016) paper, where the same two items are Example 2.19 (Tₙ(F) is zpd) and the propositions saying that adjoining a unity to an algebra with trivial multiplication is not zpd; the book's own locator numbers are **not confirmed** |
| Def. 3.14 (zJpd), Def. 7.1/Thm. 7.2, Ex. 1.10 | plausible and consistent with the book's section layout and with the parallel numbering of the *Expo. Math.* paper, but **not confirmed** against the book itself |
| Horn–Johnson 0.2.5 ("the transpose reverses products") | statement true; **locator not confirmed** |

## 5. Not verifiable here

**Access, reference by reference.** Brešar's book (Birkhäuser 2021) was *not* directly accessible: the
publisher's chapter pages redirect to an institutional login, which was not worked around. What was used
instead is (a) the text of Chapter 1 — Definition 1.1 and Proposition 1.3 (i)–(iv) — as reproduced
verbatim by a third-party mirror surfaced by search, (b) the book's table of contents for the section
structure (which is how the §2.1 error of D6 was found), and (c) for the remaining locators, only the way
other papers cite the book. Brešar's *Expo. Math.* 34 (2016) paper, which contains the article versions
of Theorem 2.27 and Corollary 2.17, was available in full from the author's page
(<https://users.fmf.uni-lj.si/bresar/documents/zpdidemp.pdf>) and was used to confirm the *content* of
Examples 2.19 and 2.23 and of Theorem 3.7/2.27. Horn–Johnson was available only as the publisher's free
front matter, whose contents list sections but not subsections, so the locator §0.2.5 stays unconfirmed
(the statement it supports, that the transpose reverses products, is standard). Adrabi's 2026 preprint is
available nowhere: searches of arXiv, the author's public profiles, and his 2024 doctoral thesis found no
trace of the title, so the paper's framing cannot be checked against it at all.

- **Adrabi 2026 (the author's own preprint)** — Definition 3.1 (braided-symmetric derivations),
  Remark 3.4, Section 1, Section 4 are cited for the paper's entire framing, but the preprint is not in
  this repository and not publicly reachable. A referee cannot check these. Consider making it
  available, or restating the two facts: they are one-line computations (`D(x·_σ y) = D(x)·_σ y + x·_σ D(y)`
  is literally the definition of a derivation of `(A, ·_σ)`).
- The Lean file's 479 non-computational lines: unverifiable until D5 is fixed. What I can say is that
  the statements they claim to prove are the paper's theorems, and that I verified those by hand.

## 6. Substantive remarks (not defects)

1. **Prop. `prop:matrix` may be a shadow of a general theorem.** With α = conjugation by `D`, `D² = 1`,
   the algebra splits by D-parity and, on homogeneous parts, `μ(x,y) = xy + (−1)^{|x|+|y|} yx`. That
   suggests the F₃/n = 2 computation could become a statement for every n and every field of
   characteristic ≠ 2 — which would also sharpen Question `q:noncomm`. As it stands the proposition is
   a single data point over the smallest field.
2. **`thm:codim` and `cor:twisted` overlap**: on a commutative algebra, `μ_α = f(xy)` with `f = id+α`
   and `ker f = ker c` for the augmentation `c`, so the dual-numbers instance is `thm:codim` applied to
   the twisted product. Fine, but worth a linking sentence.
3. The paper is candid that the criterion is Brešar's Proposition 1.3 re-read; the genuinely new
   content is the `f(xy)` class, the two "beyond zpd" classes, and the computation. That is a coherent
   but modest contribution — appropriate for a short note, and the abstract should not oversell it (D7).

## 7. Reproduction

```bash
cd paper && latexmk -pdf braided-sym-zpd.tex            # 7 pp.
sed -n '/^namespace M2F3Check/,/^end M2F3Check/p' \
  ../lean/Research/BraidedSymZpd/BraidedSymZpd.lean > M2F3Check.lean && lean M2F3Check.lean
cd ../lean && lake build                                 # FAILS: Research.Zpd.Basic, Research.Zpd.DualNumbers
git tag                                                  # empty (README claims tags)
grep -n "paperversion" ../paper/braided-sym-zpd.tex      # 2, not 7
```

The independent F₃ verification (zero-pair counts, ranks, and the kernel-basis-in-span argument) is in
`results/m2-verify.py`.

*Note on method.* The proofs and the computational claims were checked directly. Seven directions
were carried out by independent reviewers — version history, the Lean artifact, the document-level
audit, Section 2, Sections 3 and 5, the primary-source audit, and an exhaustive test-bench over small
algebras — and every finding included here was re-checked against the repository or recomputed. Four reviewer claims were not adopted as stated: a characterisation of the v7 edit as weakening
a claim about $M_n(K)$ (it generalises it), a non-unital counterexample to line 292 (the Jordan product
on strictly upper triangular 3×3 matrices is *not* a function of xy, so the example refutes nothing), a
claim that the unit of `thm:zpd-fxy` is dispensable (false, and I had endorsed it myself in an earlier
draft — see D8), and an understated reading of D8 as statement hygiene, which a reviewer's
counterexample corrected.

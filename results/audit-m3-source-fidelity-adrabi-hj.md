# Audit m3 — source fidelity: Adrabi (2026), Horn & Johnson (2013), and the two sources that are not in the folder

Member m3, swarm `smvxd25ff`. Paper audited: `paper/braided-sym-zpd.tex` (v7/v8 working copy, 480 lines; not modified).
All quotations below were located mechanically by
`results/audit-scripts/m3-locators.py` (run from the repository root; it prints, for every anchor,
the PDF page and the running head/foot that carries the printed page number).
The two computational witnesses are produced by `results/audit-scripts/m3-twisted-involution.py`.

**Page conventions.** "printed p. N" is the number printed in the running head/foot of the book.
Adrabi: PDF p. = printed p. for pp. 2–19 (p. 1 is the unnumbered title page). Brešar: printed p. = PDF p. − 8.
Horn & Johnson: printed p. = PDF p. − 20.

**Division of labour.** The paper has 37 citation commands: 27 to Brešar 2021, 6 to Adrabi 2026,
2 to Brice–Huang 2015, 1 to An–Li–He 2015, 1 to Horn–Johnson 2013.
The Brešar locator list (Preface, Def 1.1, Prop. 1.3, Def. 3.14, Cor. 2.17, Ex. 1.10, Ex. 2.19, Ex. 2.23,
Thm. 2.27, Def. 7.1, Thm. 7.2, §§2.2/7.1/7.3) is audited by d1 (m6); the §4 mathematics, `rem:inner`
and the F₃ numerics by d2 (m5). This report covers the **Adrabi** and **Horn–Johnson** citations in full,
the two citations whose sources are **absent from the folder**, and those of the paper's own sentences
that make a claim *about a source*. Where a finding of mine needed a Brešar fragment I verified that
fragment and say so.

---

## 1. Adrabi 2026 — "Braided-Symmetric Derivations of Algebras", preprint version 46, compiled 2026/10/16 (19 pp.)

The paper cites Adrabi in exactly six places: l.127, l.129, l.134, l.136, l.137, l.193.
All six locators (**Section 1**, **Definition 3.1** ×2, **Remark 3.4**, **Section 4**, **Definition 3.1**)
exist and are about what the paper says they are about. No wrong number and no non-existent locator.
Two of the six widen the source; four are faithful, two of them verbatim.

### F1 — l.127, Introduction: "the symmetrized products of `\citet[Section 1]{Adrabi2026}`" — **FINE**

Paper: "The maps $\mu$ that interest us are the symmetrized products of Adrabi (2026, Section 1)."
Source, printed p. 3 (sentence opens on p. 2, formula on p. 3):

> "Let A be an algebra over K with product µ. Let σ : A ⊗ A → A ⊗ A be a K-linear map with σ² = id,
> for instance the swap τ(x ⊗ y) = y ⊗ x. It gives a symmetrized **product**
> x ·σ y = µ(x ⊗ y) + µ(σ(x ⊗ y))."

and again in §2, printed p. 5:

> "Let σ : A ⊗ A → A ⊗ A be a K-linear map with σ² = id. We write x ·σ y = xy + µ(σ(x ⊗ y))."

The section number is right (§1 is the Introduction, and the product is defined there), and the paper's own
formula at l.130, $m(x\otimes y + \sigma(x\otimes y))$, is the same expression for linear $m$.
Minimal repair: none.

### F2 — l.129: "we do not require $\sigma^2=\mathrm{id}$, which differs from `\citep[Definition 3.1]{Adrabi2026}`" — **FINE** (claim about the source is correct)

Paper: "In this paper a *braiding* is a linear map $\sigma$ of $A\otimes A$, and we do not require
$\sigma^2=\mathrm{id}$, which differs from Adrabi (2026, Definition 3.1)."
Source, printed p. 5:

> "**Definition 3.1.** Let A be a K-algebra and let σ be a K-linear **involution** of A ⊗ A."

That "involution" is exactly $\sigma^2=\mathrm{id}$ in Adrabi's usage is proved by two further passages:

> (p. 2) "Let σ : A ⊗ A → A ⊗ A be a K-linear map with σ² = id."
> (p. 10) "We need α² = id for the following reason. Applying σα below twice gives
> x ⊗ y ↦ α²(x) ⊗ α²(y), so σα is an involution of A ⊗ A exactly when α is involutive."

and by p. 5: "We use three involutions of A ⊗ A: the identity, the swap τ …, and the α-twisted map σα".
So the paper's statement about the source is accurate: Adrabi's braiding is an involution, the paper's is not.
Minimal repair: none. (This settles the "does Adrabi require σ²=id?" question raised in the brief: yes.)

### F3 — l.136 and l.193 (`def:adrabi-bsder`): recall of Adrabi Definition 3.1 — **FINE**

Paper, l.136: "For an involution $\sigma$, a *braided-symmetric derivation* is a linear map $D$ with
$D(x\cdot_\sigma y) = D(x)\cdot_\sigma y + x\cdot_\sigma D(y)$ (Adrabi, Definition 3.1)"; l.193–196 repeats it
as `def:adrabi-bsder`: "let $\sigma$ be a $K$-linear involution of $A\otimes A$ … for all $x,y\in A$."
Source, printed p. 5:

> "Definition 3.1. Let A be a K-algebra and let σ be a K-linear involution of A ⊗ A. A braided-symmetric
> derivation for σ is a K-linear map D : A → A that satisfies identity (1), that is,
> D(x ·σ y) = D(x) ·σ y + x ·σ D(y) for all x, y ∈ A. We write BSDerσ(A) for the set of braided-symmetric
> derivations for σ. This set is a K-subspace of End_K(A), since the condition is linear in D. For an
> automorphism α of A, we write BSDerσ(A)α for the subset of maps D with Dα = αD."

The recall is verbatim. It does drop the last sentence of Def. 3.1 (the subspace BSDerσ(A)α of maps
commuting with an automorphism α); the paper never uses it, so this is a narrowing of the *recalled*
definition, not an error. Minimal repair: none, or add "(and BSDer$_\sigma(A)_\alpha$ for the maps with
$D\alpha=\alpha D$)" if the recall is meant to be complete.

### F4 — l.137: "These maps are the derivations of the nonassociative algebra $(A,\cdot_\sigma)$ (`\citep[Remark 3.4]`)" — **FINE**

Source, printed p. 6:

> "Remark 3.4. Let A be a K-algebra and let σ be an involution of A ⊗ A. Identity (1) for σ is the Leibniz
> rule for the product ·σ. So BSDerσ(A) is the set of derivations of the nonassociative algebra (A, ·σ),
> in the sense of Jacobson [14, Part I]."

Word for word. Minimal repair: none.

### F5 — l.134: the third braiding is attributed to Adrabi §4, but Adrabi's α is an *involutive automorphism or anti-automorphism* — **IMPRECISE**

Paper:

> "The third is the *twisted* swap $x\otimes y \mapsto \alpha(y)\otimes\alpha(x)$, **for a linear map
> $\alpha\colon A\to A$**, which twists the swap (Adrabi, Section 4)."

Source, printed p. 10 (§4):

> "An automorphism of A is a bijective K-linear map α : A → A with α(xy) = α(x)α(y) and α(1) = 1.
> An anti-automorphism of A is a bijective K-linear map α : A → A with α(xy) = α(y)α(x) and α(1) = 1. …
> We need α² = id for the following reason. … so σα is an involution of A ⊗ A exactly when α is involutive.
> …
> Let α be involutive, of either kind. Then σα(x ⊗ y) = α(y) ⊗ α(x) is a K-linear involution of A ⊗ A."

and printed p. 5 (§2): "They have the form xy + α(y)α(x) for a fixed automorphism or anti-automorphism α of A."
So Adrabi's α is (i) bijective and multiplicative and (ii) involutive; the paper's "linear map" is a
strict generalisation. The paper flags its other deviation from Adrabi (F2) but not this one, so the
citation as written reports a narrower source statement as if it were the source's.

Verdict: IMPRECISE (hypotheses of the cited construction dropped).
Minimal repair: "…for a linear map $\alpha\colon A\to A$ (Adrabi, Section 4, takes $\alpha$ to be an
involutive automorphism or anti-automorphism, and $\sigma_\alpha$ is an involution of $A\otimes A$ exactly then)."

### F6 — l.89 (abstract) against l.193 + l.320–323 (`cor:twisted`): the abstract promises braided-symmetric derivations for braidings that are not involutions — **IMPRECISE** (a gap, not a false theorem)

Paper, l.89:

> "For the symmetrized products $\mu_\sigma$, this asks when the algebra with that product is zero product
> determined, and **hence when the braided-symmetric derivations of that product can be studied through
> zero products**."

But the paper's only notion of braided-symmetric derivation is `def:adrabi-bsder` (l.193), which requires
$\sigma$ to be an *involution* of $A\otimes A$, quoting Adrabi Def. 3.1. Now `cor:twisted` (l.320–323) applies
to *every* algebra endomorphism $\alpha$, and by Adrabi p. 10, $\sigma_\alpha^2=\mathrm{id}$ iff $\alpha^2=\mathrm{id}$.
So for the paper's own headline application with $\alpha^2\ne\mathrm{id}$, "the braided-symmetric derivations of
that product" are not defined by the paper (nor by Adrabi, whose Def. 3.1 also needs an involution).

Concrete witness (`m3-twisted-involution.py`, exact arithmetic, output quoted):

```
E1  A = K^3, alpha = the 3-cycle e1 -> e3 -> e2 -> e1
    alpha^2 == id          : False
    sigma_alpha^2 == id    : False
    sigma_alpha(e1 (x) e1)   = ['e3 (x) e3']
    sigma_alpha^2(e1 (x) e1) = ['e2 (x) e2'] = alpha^2(e1) (x) alpha^2(e1) != e1 (x) e1
    zero-product basis pairs: [('e1','e2'), ('e1','e3'), ('e2','e1'), ('e2','e3'), ('e3','e1'), ('e3','e2')]
    dim span{e_i (x) e_j : e_i e_j = 0} = 6, dim ker mu-bar = 9 - 3 = 6  -> A is zpd
    => Corollary cor:twisted applies, but sigma_alpha is not an involution.
```

$A=K^3$ is commutative, unital and generated by the idempotents $e_1,e_2,e_3$, so it is zpd (Brešar 2021,
Theorem 2.27, printed p. 30: "A finite-dimensional unital algebra A is zpd if and only if it is generated by
idempotents"; independently checked by the tensor criterion above). The 3-cycle is an algebra endomorphism of
$K^3$ which is not involutive. Hence `cor:twisted` gives the determination theorem while the sentence of the
abstract has nothing to attach "braided-symmetric derivations" to.

Note that the Introduction itself is careful — l.136 begins "For an involution $\sigma$" — so the defect is
confined to l.89 (and to the same "hence" at l.138, which is harmless because l.136 has just restricted to
involutions).

Verdict: IMPRECISE. It becomes an outright error if l.89 is read as covering the twisted braidings of
`cor:twisted`/`cor:anti`, which are the paper's headline applications.
Minimal repair: "…and hence, **for an involutive $\sigma$,** when the braided-symmetric derivations of that
product can be studied through zero products"; alternatively define the Leibniz rule for an arbitrary linear
$\sigma$ (the equation of `def:adrabi-bsder` makes sense as it stands) and say that Adrabi Def. 3.1 is the
involutive case.

---

## 2. Horn & Johnson 2013

There is exactly one citation (l.352).

### F7 — l.352: "The transpose reverses products `\citep[\S 0.2.5]{HornJohnson2013}`" — **FINE**

Source. §0.2.5 exists, has the right number and the right subject; printed p. 6:

> "**0.2.5 The transpose, conjugate transpose, and trace.** If A = [a_ij] ∈ M_{m,n}(F), the transpose of A,
> denoted by A^T, is the matrix in M_{n,m}(F) whose i,j entry is a_ji …"

and the statement cited is on printed p. 7:

> "Both the transpose and the conjugate transpose obey the reverse-order law: (AB)* = B* A* and
> (AB)^T = B^T A^T."

That is exactly "$\alpha(xy)=\alpha(y)\alpha(x)$", i.e. the hypothesis of `cor:anti`. The section number is
correct (it is a subsection of §0.2 "Matrices" in Chapter 0 "Review and miscellanea") and the bibliography
entry matches the copy: "Matrix Analysis, 2nd edn. Cambridge University Press, Cambridge (2013)" against the
copyright page "First published 1985 … Second edition first published 2013".

Verdict: FINE. The only refinement a referee might make is that §0.2.5 *opens* on printed p. 6 while the law
itself is on p. 7 — no repair needed. No other claim of the paper rests on Horn & Johnson.

---

## 3. Sources that are not in the folder: two citations remain unverifiable, and what exactly depends on them

The folder holds only Adrabi 2026, Brešar 2021 and Horn–Johnson 2013. Two cited works are absent, and I
report exactly what cannot be checked rather than guessing.

### F8 — l.448–450 (`rem:inner`): "`\citep[Theorem 2.1]{AnLiHe2015}`" for "an algebra generated by idempotents is zJpd in characteristic other than 2" — **UNVERIFIABLE locator + IMPRECISE recall + one outright ERROR in the same sentence**

Paper, l.448–453:

> "In particular, for a matrix algebra, $M_n(B)$ is generated by **the idempotents $(e_{ii}+be_{ij})-e_{ii}$**
> for $i\ne j$ with $b\in B$, and an algebra generated by idempotents is zJpd in characteristic other than
> $2$ (An–Li–He, Theorem 2.1). So $M_n(B)$ is determined by $\mu_\alpha$ for every inner $\alpha$, in
> characteristic other than $2$, and Proposition~\ref{prop:matrix} is the case $n=2$ and $D=\mathrm{diag}(1,-1)$…"

**(a) What cannot be checked.** An, Li, He, *Zero Jordan product determined algebras*, Linear Algebra Appl.
**475** (2015) 90–93 is not in the folder. Neither the number "Theorem 2.1", nor its hypotheses (unital?
finite-dimensional? char ≠ 2 stated where?), nor whether it is stated for algebras or rings, can be verified.

**(b) What the folder does settle.** Brešar 2021 attributes the theorem to exactly that paper and states it,
printed p. 49:

> "The following theorem was obtained in [24] (and partially in [85]).
> **Theorem 3.15** Let A be an (associative) **unital** algebra over a field F of characteristic not 2.
> If A is generated by idempotents, then A is zJpd."

with bibliography entry "[24] G. An, J. Li, J. He, Zero Jordan product determined algebras. Linear Algebra
Appl. 475, 90–93 (2015)". So the *content and the attribution* of the paper's recall are corroborated; only
the locator is not. Two defects of the recall remain:

- the paper drops the source's hypothesis **"unital"**. Harmless in the application ($M_n(B)$ with $B$ unital
  is unital), but the recalled statement is wider than the source's.
- the paper's detour is unnecessary: Brešar 2021, printed p. 52, states the matrix case directly —

> "**Corollary 3.17** The following algebras over a field of characteristic not 2 are zJpd:
> (a) The algebra M_n(B), where n ≥ 2 and B is any unital algebra."

**(c) An error in the same sentence, independent of the citation.** The elements named
"$(e_{ii}+be_{ij})-e_{ii}$" are $be_{ij}$, and $(be_{ij})^2=0$: they are *not* idempotents (the idempotent is
$e_{ii}+be_{ij}$, since $(e_{ii}+be_{ij})^2 = e_{ii}+be_{ij}$ for $i\ne j$). As printed, the sentence applies
a theorem about algebras *generated by idempotents* to a generating set of nilpotent elements. The phrase is a
compression of the source it is derived from, Brešar 2021, proof of Corollary 2.4, printed p. 19 (the $\ne$ glyph
is dropped by `pdftotext`, so "i = j" below is "i ≠ j"):

> "If i ≠ j, then e_ii + se_ij is an idempotent, so se_ij = (e_ii + se_ij) − e_ii is a difference of two
> idempotents. From se_ii = se_ij · e_ji, where j ≠ i, it thus follows that se_ii also lies in the subring
> generated by idempotents."

(subscripts and the two "≠" restored by hand; `pdftotext` prints "eii + seij", "i = j", "j = i".)

The paper kept the last clause ("− e_ii") and dropped "difference of two". The conclusion survives —
$\{e_{ii}\}\cup\{e_{ii}+be_{ij} : i\ne j,\ b\in B\}$ is a set of idempotents and it generates
$M_n(B)$, because it contains the differences $be_{ij}$ and $e_{ij}e_{ji}=e_{ii}$ — but the argument as
written does not establish it.

Verdicts: locator **UNVERIFIABLE**; recall **IMPRECISE** (drops "unital"); generator description **ERROR**
(the named elements are not idempotents; the conclusion is still true).

Minimal repair, replacing l.448–450 up to the citation:

> "In particular $M_n(B)$ is generated by the idempotents $e_{ii}$ and $e_{ii}+be_{ij}$ ($i\ne j$, $b\in B$),
> and its off-diagonal part is generated by their differences $(e_{ii}+be_{ij})-e_{ii}=be_{ij}$; a unital
> algebra generated by idempotents is zJpd in characteristic other than $2$, so $M_n(B)$ is zJpd
> (Brešar 2021, Corollary 3.17(a), p. 52)."

If the paper prefers to keep the An–Li–He reference, it should read "(An–Li–He 2015, Theorem 2.1, as stated
in Brešar 2021, Theorem 3.15)", which makes the unverifiable locator a secondary citation of a verifiable one.

### F9 — l.251–253 (after `cor:criterion`) and l.124: "`\citep[Theorem 2.3]{BriceHuang2015}`" for "The criterion is stated for an arbitrary bilinear $\mu$, over a commutative ring" — **UNVERIFIABLE**

Paper, l.251–253:

> "The criterion is stated **for an arbitrary bilinear $\mu$, over a commutative ring**, by Brice and Huang
> (2015, Theorem 2.3); for $\mu$ the product it is Proposition 1.3 of Brešar, recalled as
> Proposition~\ref{prop:bresar-zpd}."

and l.124: "zpd for such a pair, with $\mu$ an arbitrary bilinear map, is the setting of Brice and Huang (2015)."

Brice, Huang, *On zero product determined algebras*, Linear Multilinear Algebra **63** (2015) 326–342 is not in
the folder. Unverifiable: (i) that a "Theorem 2.3" exists at that number; (ii) the hypothesis "over a
commutative ring"; (iii) that their $\mu$ is an arbitrary bilinear map and not the product of an algebra.
Nothing in the folder mentions either a ring-level or an arbitrary-$\mu$ form of the criterion on their behalf:
Brešar's only two pointers to [61] are "A more detailed analysis of the topic of this section is given in [61]"
(end of Ch. 1, printed p. 16) and "the algebra of strictly upper triangular matrices over a field … was shown in
[61]" (printed p. 25). Every form of the criterion that *is* checkable here is over a field — Brešar
Proposition 1.3 (printed p. 4, statement (i)–(iv), "Let A be a nonassociative algebra over a field F";
the proof starts on p. 5), Proposition 2.7 (printed p. 21, "Let A be a unital algebra over a field F"),
and the ring-level notion of Definition 2.1 (printed p. 17) is for biadditive $\varphi$ with range in the
ring, not for a bilinear $\mu\otimes$-criterion.

Consequence for the paper: none for correctness — `cor:criterion` is proved in §3 from Brešar's Proposition 1.3
and stands on its own — but the *priority/attribution* claim and, in particular, the phrase "over a commutative
ring" rest on a source the paper's own bibliography cannot support from this folder.

Verdict: UNVERIFIABLE (locator and hypotheses); no repair forced on the mathematics.
Minimal repair: drop "over a commutative ring" (it plays no role in the paper) and write
"The criterion for an arbitrary bilinear $\mu$ is Brice–Huang's Theorem 2.3 as we recall it; for $\mu$ the
product it is Proposition 1.3 of Brešar", or consult the original before keeping a hypothesis the paper never uses.

---

## 4. A source recall that is faithful (it was on the assigned list, so I report it)

### F10 — l.407 (`ex:dual`): "an algebra of the form studied in `\citep[Example 2.23]{Bresar2021}`" — **FINE**

Paper: "let $A = K[\varepsilon]/(\varepsilon^2)$, an algebra of the form studied in Brešar (2021, Example
2.23), where a unity is adjoined to an algebra with trivial multiplication; here that algebra is $K\varepsilon$."
Source, printed p. 26:

> "Example 2.23 Another natural candidate may be the algebra obtained by adjoining a unity to a zpd algebra A
> without unity that is not generated by idempotents. … let us look more closely at the simplest case where A
> has trivial multiplication. Then A# , the algebra obtained by adjoining a unity to A, is a commutative unital
> algebra. We claim that A# is symmetrically zpd. …
> Thus, ϕ is of the desired form, meaning that A# is indeed an example of a symmetrically zpd algebra that is
> not zpd (by Proposition 1.19)."

$K[\varepsilon]/(\varepsilon^2)$ is $(K\varepsilon)^\#$ with $K\varepsilon$ of trivial multiplication, so the
identification is exact, and Brešar's example already asserts that this algebra is not zpd — the paper's own
reproof through Theorem 2.27 is a re-derivation, not a contradiction. FINE.

*Source erratum, not the paper's error, recorded because `ex:dual` points at it.* Brešar's parenthetical
"(by Proposition 1.19)" cannot be right as printed. Proposition 1.19 is stated on printed p. 15 as "Let A be a
nonassociative algebra **such that A² = A**. Then A#, the algebra obtained by adjoining a unity to A, is not
zpd", and its proof (printed p. 16) runs: "However, if z ∈ A \ A², then ϕ(1, z) = z + A² … while ϕ(z, 1) = 0,
which shows that A# does not satisfy condition (iv) of Proposition 1.3." The argument needs an element of
$A\setminus A^2$, i.e. $A^2\ne A$ — and in Example 2.23, $A^2=\{0\}\ne A$. So the printed hypothesis should
read $A^2\ne A$ (equivalently $A\ne A^2$); with $A^2=A$ the quotient $A^\#/A^2$ collapses and the proof has
nothing to compare. This does not affect the audited paper, which does not cite Proposition 1.19 and proves its
non-zpd claim from Theorem 2.27.

---

## 5. Categories in which I found nothing

- **Adrabi 2026 — numbering, existence of locators, misattribution:** nothing. All six locators exist, in the
  right sections, and the four statements the paper recounts (the symmetrized product, Def. 3.1 in two places,
  Remark 3.4) are faithful; two are verbatim. The only defects are the two widenings F5 and F6.
- **Horn & Johnson 2013:** nothing. One citation, correct section, correct statement, correct edition.
- **Paper's assertions about what a source says:** exactly two are inaccurate — the dropped "unital" of F8 and
  the dropped "involutive automorphism or anti-automorphism" of F5. The assertions that were called into
  question are both **correct**: "we do not require $\sigma^2=\mathrm{id}$, which differs from Adrabi
  Definition 3.1" (F2, confirmed by Adrabi pp. 5 and 10), and "Brešar defines zpd for nonassociative
  algebras" — Brešar Definition 1.1, printed p. 4,
  "A **nonassociative** algebra A **over a field F** is said to be zero product determined if, for every bilinear
  functional ϕ : A × A → F …".
- **Not audited here** (other directions): the 27 Brešar citations as such, the proofs of `thm:zpd-fxy`,
  `prop:injective`, `cor:identity`, `thm:codim`, the Jordan-product paragraph, `rem:inner`'s algebra and
  `prop:matrix`'s F₃ numerics. Where one of my findings quotes Brešar (printed pp. 4, 15, 16, 17, 19, 21, 25, 26, 30, 49, 52)
  the quotation itself is verified by `m3-locators.py`, but I make no claim about those locators beyond the
  words I print.

---

## 6. Summary table

| locator (line, label) | verdict | one-line repair |
|---|---|---|
| l.127 Intro — "symmetrized products of Adrabi §1" | FINE | none |
| l.129 Intro — "we do not require σ²=id, which differs from Adrabi Def 3.1" | FINE | none; Adrabi p. 5/p. 10 confirm "involution" = σ²=id |
| l.136 Intro — "braided-symmetric derivation … Adrabi Def 3.1" | FINE | none |
| l.137 Intro — "these maps are the derivations of (A,·_σ), Adrabi Rem 3.4" | FINE | none |
| l.193 `def:adrabi-bsder` — Adrabi Def 3.1 | FINE | optional: also recall BSDerσ(A)_α = {D : Dα = αD} |
| l.134 Intro — "twisted swap x⊗y ↦ α(y)⊗α(x), for a linear map α (Adrabi §4)" | IMPRECISE | restore Adrabi's hypothesis: α an involutive automorphism or anti-automorphism |
| l.89 abstract — "hence when the braided-symmetric derivations of that product can be studied" | IMPRECISE | insert "for an involutive σ", or define the Leibniz rule for arbitrary linear σ |
| l.352 (`cor:bresar-matrix` aftermath) — "transpose reverses products, H&J §0.2.5" | FINE | none; law on printed p. 7 |
| l.448–450 `rem:inner` — "idempotents (e_ii+be_ij)−e_ii" | ERROR | those elements are be_ij with square 0; use the idempotents e_ii and e_ii+be_ij |
| l.450 `rem:inner` — "[AnLiHe2015, Theorem 2.1]" | UNVERIFIABLE + IMPRECISE (drops "unital") | cite Brešar 2021, Cor. 3.17(a), p. 52 (or Thm 3.15, p. 49, with "unital") |
| l.253 after `cor:criterion` — "[BriceHuang2015, Theorem 2.3], over a commutative ring" | UNVERIFIABLE | drop "over a commutative ring"; keep the locator only as a secondary attribution |
| l.124 Intro — "the setting of Brice and Huang (2015)" | UNVERIFIABLE | no repair forced; the priority claim cannot be checked from this folder |
| l.407 `ex:dual` — "of the form studied in Brešar Example 2.23" | FINE | none |

# Audit m5 — §4 (products of the form $f(xy)$) and §5 (`prop:matrix`, `rem:inner`, `q:noncomm`)

Member m5, swarm `smvxd25ff`.

**Revision audited: `5b7e067`** ("review: novel claim of the criterion dropped, alpha = id case of
`prop:injective` restored, `ex:dual`'s relation to Bresar's Example 2.23 stated"), 495 lines,
`md5 e9d9255b2408d9fb884e1cf40c7f36a4`. The .tex was revised four times while I audited it
(`68ce750`, then `c638a7f`, `7d379c0`, `5b7e067`); **every statement below was re-checked against
`5b7e067`**, and §3 records each repair that landed during the audit together with a check of the
repair itself. Line numbers are those of `5b7e067`; the label and the quoted words identify a
place if the file moves again.

Sources: `.scratch/refs/braided-sym-zpd-v7-references/` — Brešar 2021 (= "B"), Adrabi 2026 (= "A"),
Horn & Johnson 2013 (= "HJ"), extracted with `pdftotext -layout` into `.scratch/audit/m5/`.
"PDF p. N" counts pages of the file, "printed p. M" is the number printed on it. Offsets:
B: printed = PDF − 8 (PDF 33 carries "… 25"); HJ: printed = PDF − 20 (PDF 26 carries "6 …");
A is 11 pages and has no printed numbers.

**Scripts** (`results/audit-scripts/`, all run against the current text): `m5-f3.py` (the numbers of
`prop:matrix`, the `rem:inner` identities, the idempotent count), `m5-checks.py` (independence of
$D$, char 2, `thm:zpd-fxy`, `thm:codim`), `m5-side.py` (the generating idempotents, generation of
$M_n(B)$ over a non-commutative $B$, the non-unital counterexample, $T_2(\mathbb F_p)$),
`m5-dual.py` (`ex:dual`), `m5-quaternion.py` (`q:noncomm`), `m5-rank.py` (rank over $\mathbb F_p$ and
the `cor:criterion` test). Every number quoted below comes from these scripts or from the quoted
source; nothing is taken from another member's notes.

---

## Part 1 — findings on `5b7e067`

### m5-1 — l. 473 (`q:noncomm`), last clause — **IMPRECISE**

Paper: "… so in characteristic other than $2$ the matrix algebras over a field are settled; **the question is about algebras admitting an involutive automorphism that is not inner.**"

The clause does not follow from the sentence it closes, and it misstates the question of l. 472
("Which noncommutative algebras with an involutive automorphism $\alpha$ are determined by their
twisted product $xy+\alpha(yx)$?"). The paragraph's own first half settles *every* inner $\alpha$:
by `rem:inner`, determination is then equivalent to zJpd, so the open content is (i) which algebras
are zJpd and (ii) the non-inner $\alpha$ (where `cor:criterion` applies). "Which algebras admit a
non-inner involutive automorphism" is a different question about automorphism groups, and it is
not what remains: an algebra can admit a non-inner automorphism and still be settled, and the
quaternions (which are settled, negatively) admit the inner $\alpha=\mathrm{id}$ only.
Repair: "… the question is about a non-inner $\alpha$, where the criterion of
Corollary~\ref{cor:criterion} applies; for an inner $\alpha$ it is the question of which algebras
are zJpd."

### m5-2 — l. 465 (`rem:inner`): `\citep[Theorem 2.1]{AnLiHe2015}` — **UNVERIFIABLE locator**

An, Li, He (2015) is not in the reference folder, so the numbering "Theorem 2.1" and its exact
hypotheses cannot be checked. **That is the whole of what remains unverified**; the statement is
corroborated inside the folder by the source the paper now cites next to it, B Theorem 3.15,
**PDF 57 / printed 49**, whose proof section opens "The following theorem was obtained in [24]",
with B's [24] = "G. An, J. Li, J. He, Zero Jordan product determined algebras. Linear Algebra Appl.
475, 90–93 (2015)" — exactly the paper's reference. No repair needed beyond what is there; if the
referee wants the locator itself, it has to be checked against the journal paper.

### m5-3 — l. 158 and l. 267–268: `BriceHuang2015`, "Theorem 2.3 … over a commutative ring" — **UNVERIFIABLE (source absent)**

The Brice–Huang paper is in neither the folder nor the bibliography of a source in it, so neither
the numbering, nor "over a commutative ring", nor the credit in the Introduction (l. 158, "We first
record the criterion that the later proofs use: it is Proposition 1.3 of Brešar … and Theorem 2.3
of Brice and Huang for an arbitrary bilinear $\mu$ over a commutative ring") can be checked here.
The mathematics is checkable and correct independently: `cor:criterion` (l. 262) is Brešar
Prop. 1.3 (i)⟺(iii) applied to $(A,\mu)$ (B, PDF 12 / printed 4), and the paper proves it that way
(l. 270–273); the remark at l. 267–268 now says precisely that. The phrase "over a commutative
ring" is stronger than the paper's own field setting (l. 230) and is the part that cannot be
verified. Repair: quote the theorem, or write "over a field, cf. [BH, Thm 2.3]".

**No other error was found in this material.** Everything else I checked is correct; the
verification is recorded in Part 2, because "nothing found" is only useful with the numbers.

---

## Part 2 — what I verified as correct

### m5-2.1 — l. 435–447 (`prop:matrix`): the four numbers — **FINE**

Paper (l. 443–445): rank $4$, $\dim\ker\bar\mu_\alpha=12$, "exactly $417$" zero pairs, "the $417$
tensors $x\otimes y$ span a subspace of dimension $12$".

Recomputed independently (`m5-f3.py`: all $81^2$ pairs, Gaussian elimination over $\mathbb F_3$ in
the basis $E_{ij}\otimes E_{kl}$, $i,j,k,l\in\{1,2\}$):

* $\alpha$ = conjugation by $\operatorname{diag}(1,-1)$ is an involutive $\mathbb F_3$-linear automorphism and $\mu_\alpha(x,y)=xy+\alpha(yx)=xy+\alpha(y)\alpha(x)$ on all 6561 pairs;
* $\operatorname{rank}\bar\mu_\alpha=4$, hence $\dim\ker\bar\mu_\alpha=12$;
* the number of pairs with $\mu_\alpha(x,y)=0$ is exactly **417**;
* those 417 tensors span a **12**-dimensional subspace; $\Zs\subseteq\ker$ always, so the two subspaces are equal.

All four numbers and the closing argument are correct.

### m5-2.2 — l. 449 (the remark after `prop:matrix`): $12=12$ and $13=13$ — **FINE**

Same script: the ordinary product on $M_2(\mathbb F_3)$ gives $\dim\Zs=\dim\ker=12$; the transpose
twist $\mu(x,y)=xy+y^{\mathsf T}x^{\mathsf T}$ gives $\dim\Zs=\dim\ker=13$ (513 zero pairs, rank 3),
and $xy+y^{\mathsf T}x^{\mathsf T}=xy+(xy)^{\mathsf T}$ identically, as the sentence asserts. The
markup "$\dim\Zs=\dim\ker=13$" now states exactly what was computed.

### m5-2.3 — l. 452–461 (`rem:inner`): the Jordan-product identity, $\Phi$, independence of $D$ — **FINE**

Paper: "$xy+\alpha(yx)=xy+(Dy)(xD^{-1})=(xD^{-1})(Dy)+(Dy)(xD^{-1})=(xD^{-1})\circ(Dy)$"; "$\bar\mu_\alpha=\bar\circ\circ\Phi$"; "$\Zs_{\mu_\alpha}=\Phi^{-1}(\Zs_\circ)$"; "the answer does not depend on $D$"; and l. 457 "the **linear** automorphism".

Checks (`m5-f3.py`, `m5-checks.py`): the identity holds on all 6561 pairs (0 mismatches);
$\bar\mu_\alpha=\bar\circ\circ\Phi$ on all 6561 pairs (0 mismatches); $\Phi$ carries the 16 basis
tensors to a basis (rank 16, so it is invertible); for **all 48** invertible $D\in M_2(\mathbb F_3)$
one gets $(\operatorname{rank}\bar\mu_\alpha,\dim\ker,\dim\Zs)=(4,12,12)$ and "determined" — a
single value, as claimed. The deduction via `cor:criterion` is correct. The word "linear" is right:
$R_{D^{-1}}$ and $L_D$ are not multiplicative ($R_{D^{-1}}(uy)=uyD^{-1}$ but
$R_{D^{-1}}(u)R_{D^{-1}}(y)=uD^{-1}yD^{-1}$, which differ for $u=D$, $y=1$ whenever $D^2\ne D$).

### m5-2.4 — l. 462–468 (`rem:inner`): the generating idempotents and the zJpd input — **FINE**

Paper: "for a unital algebra $B$ and $n\ge2$ the matrix algebra $M_n(B)$ is generated by the idempotents $e_{ii}$ and $e_{ii}+be_{ij}$ for $i\ne j$ with $b\in B$ (indeed $be_{ij}=(e_{ii}+be_{ij})-e_{ii}$ and $be_{ii}=(be_{ij})e_{ji}$), and a unital algebra generated by idempotents is zJpd in characteristic other than $2$ \citep[Theorem 3.15]{Bresar2021}, originally \citep[Theorem 2.1]{AnLiHe2015}."

Verified (`m5-side.py`, `m5-f3.py`):

* $e_{ii}+be_{ij}$ is idempotent for every $b\in M_2(\mathbb F_3)$ and both $(i,j)\in\{(1,2),(2,1)\}$ — $(be_{ij})^2=0$ and $e_{ii}(be_{ij})=be_{ij}$, $(be_{ij})e_{ii}=0$;
* $(e_{ii}+be_{ij})-e_{ii}=be_{ij}$ and $(be_{ij})(e_{ji})=be_{ii}$, both checked for all $b\in M_2(\mathbb F_3)$ and $M_3(\mathbb F_3)$;
* the generation claim in the strong form, over a **non-commutative** $B$: inside $M_2(M_2(\mathbb F_2))=M_4(\mathbb F_2)$, the $32$ idempotents $e_{ii}$ and $e_{ii}+be_{ij}$ generate the whole algebra (multiplicative closure 403 elements, $\mathbb F_2$-span $65536=2^{16}$);
* "a **unital** algebra generated by idempotents is zJpd in char $\ne2$" is B Thm 3.15 (**PDF 57 / printed 49**: "Let $A$ be an (associative) unital algebra over a field $F$ of characteristic not 2. If $A$ is generated by idempotents, then $A$ is zJpd"), and the word "unital" cannot be dropped: $A=\{[[a,b],[0,0]]:a,b\in\mathbb F_3\}$ with $(a,b)(c,d)=(ac,ad)$ has no unity, is generated by its idempotents $(0,0),(1,0),(1,1),(1,2)$ (the three nonzero ones span $A$), is zpd ($\dim\Zs_\cdot=\dim\ker=2$) and is **not** zJpd ($\dim\ker\overline{\circ}=2$ but $\dim\Zs_\circ=1$: $e_0\circ e_1=e_1=e_1\circ e_0$, so $e_0\otimes e_1-e_1\otimes e_0\in\ker\overline{\circ}\setminus\Zs_\circ$).

The paper's own application ($M_n(B)$, unital) is unaffected; the hypothesis is present, so the
sentence is correct as it now stands.

### m5-2.5 — l. 471–473 (`q:noncomm`): the substance — **FINE**

Each claim of the rewritten paragraph, with its check:

* "an inner $\alpha$ … the answer is affirmative **exactly for the zJpd algebras**" — correct: it is `rem:inner`'s equivalence (verified in m5-2.3) plus the definition of zJpd ($A^+$ determined by $\circ$);
* "affirmative for $M_n(B)$ and for the triangular algebras of Corollary~\ref{cor:bresar-matrix}(b), in characteristic other than $2$, **since these are zJpd** \citep[Corollary 3.17]{Bresar2021}" — correct, and the locator is right: B Corollary 3.17, **PDF 60 / printed 52**, "The following algebras over a field of characteristic not 2 are zJpd: (a) … $M_n(B)$, where $n\ge2$ and $B$ is any unital algebra. (b) … $\mathrm{Tri}(A_1,M,A_2)$, where $A_1$ and $A_2$ are unital algebras generated by idempotents and $M$ is a unital $(A_1,A_2)$-bimodule." I also checked a triangular case numerically: $T_2(\mathbb F_3)$ with $\alpha$ = conjugation by $\operatorname{diag}(1,2)$ (an involutive inner automorphism) gives $\dim\Zs=\dim\ker=6$ for the twisted product, and $6=6$ for the Jordan product too;
* "negative for the real quaternions with $\alpha=\mathrm{id}$, which are not zJpd \citep[Example 3.19]{Bresar2021}" — correct. Own check (`m5-quaternion.py`): $\alpha=\mathrm{id}$ is inner ($D=1$), so $\mu_\alpha(x,y)=xy+yx$; the bilinear $\varphi((a,\mathbf x),(b,\mathbf y))=ab$ vanishes on every anticommuting pair (from $x\circ y=0$, i.e. $ab=\mathbf x\cdot\mathbf y$ and $a\mathbf y+b\mathbf x=0$, one gets $\mathbf x\cdot(a\mathbf y+b\mathbf x)=b(a^2+|\mathbf x|^2)=0$ and symmetrically $a(b^2+|\mathbf y|^2)=0$, so $a=0$ or $b=0$; the identity was checked symbolically, and a random exact search over $\mathbb Q$ found 961 anticommuting pairs, 596 of them with both entries nonzero, none with $\varphi\ne0$), yet $(1,0)\circ(1,0)+(0,i)\circ(0,i)=0$ while $\varphi$ sums to $1$ — so $\mathbb H$ fails Prop. 1.3(ii) and is not zJpd. B Example 3.19 (**PDF 61–62 / printed 53–54**) proves exactly this;
* "Every automorphism of $M_n(K)$, for a field $K$ and $n\ge2$, is inner (Skolem–Noether)" — correct.

### m5-2.6 — l. 420–428 (`ex:dual`) — **FINE**

Computed for $p=3,5,7$ on $\mathbb F_p[\varepsilon]/(\varepsilon^2)$ (`m5-dual.py`): the ordinary
product has $\dim\Zs=1<2=\dim\ker$ (so $A$ is not zpd, as claimed via `thm:bresar-idempotents`); the
idempotents are exactly $0,1$; the twisted product has $\dim\Zs=\dim\ker=3$ (determined, as
`thm:codim` predicts); and $\mu_\alpha=f(xy)$ with $f=\mathrm{id}+\alpha$, $f(a+b\varepsilon)=2a$, on
all pairs. The hypothesis char $K\ne2$ is used twice and correctly ($f(1)=2\ne0$; in char 2,
$(1+\varepsilon)^2=1$ would be a third idempotent). The two new parentheticals are right too: B's
Example 2.23 (**PDF 34 / printed 26**) does show that "$\mathrm{A}^\#$ is indeed an example of a
symmetrically zpd algebra that is not zpd", and the twisted product used here
($xy+\alpha(y)\alpha(x)=f(xy)$) is not that example's symmetrized product.

### m5-2.7 — the rest of §4–§5: `thm:zpd-fxy`, `prop:injective`, `cor:identity`, `thm:codim`, `cor:twisted`, `cor:anti`, `cor:triangular`, `rem:preserving`, `rem:derivations`, the Jordan paragraph, `def:determined` — **FINE**

Proofs read line by line; the load-bearing step and the check made:

* `thm:zpd-fxy` (l. 279–294). $\mu(x,y)=0$ follows from $xy=0$, so $\varphi$ vanishes on zero products and Brešar Prop. 1.3(i)⟹(iv) (**PDF 12 / printed 4**) gives $\psi_0$ with $\varphi(x,y)=\psi_0(xy)$. Unitality is used exactly at l. 288–289: $b\in\ker f\Rightarrow\mu(b,1)=f(b)=0\Rightarrow\psi_0(b)=\varphi(b,1)=0$, so $\ker f\subseteq\ker\psi_0$ and $\psi_0$ factors through $\operatorname{im}f$ (l. 290–292). Correct. Independent check: for **all 81** linear $f$ on the zpd algebra $\mathbb F_3\times\mathbb F_3$, the algebra is determined by $f(xy)$ (81/81, no failure).
* `prop:injective` (l. 297–308) and the restored sentence (l. 384–386): injective $f$ gives $\mu(x,y)=0\iff xy=0$, so `prop:injective` applies; and for an involution $\alpha$ with char $\ne2$, $\mathrm{id}+\alpha=2P$ onto the fixed points is injective only for $\alpha=\mathrm{id}$: there the map in play is $f=\mathrm{id}+\alpha=2\,\mathrm{id}$, which is injective, and `cor:identity`(ii) supplies the converse. Both correct.
* `cor:identity` (l. 311–321) and the char-2 sentence (l. 324): $f=2\,\mathrm{id}$ is injective for char $\ne2$; for char 2, $\mu\equiv0$ and every $\varphi$ in `def:determined` is zero — verified on $M_2(\mathbb F_2)$ ($\dim\Zs=\dim\ker=16$).
* Jordan paragraph (l. 326–328): $x\circ\tfrac12=x$ uses unitality and char $\ne2$; the new clause "so that $A^2=A$" is right ($\overline{\circ}$ and the span of all products have the same image); the "indeed" is right ($y=1$ forces $f=2\,\mathrm{id}$, so $yx=xy$ for char $\ne2$; for char 2, $f=0$ would give $xy+yx=0$ for all $x,y$, contradicting $xy\ne yx$).
* `cor:twisted` (l. 334–342), `cor:anti` (l. 345–353): an endomorphism plus commutativity, resp. an anti-multiplicative $\alpha$, give $\mu_\alpha=(\mathrm{id}+\alpha)(xy)$; both apply `thm:zpd-fxy`. Correct (with `cor:anti`'s unital hypothesis).
* `cor:triangular` (l. 371–380): $A$ is unital and zpd by Cor. 2.17(b), then `thm:zpd-fxy`. Correct; l. 382 (upper triangular = type (b), B Example 2.19, PDF 33 / printed 25) is right.
* `thm:codim` (l. 392–407): $n\in N\Rightarrow ny,xn\in N\Rightarrow\varphi(n,y)=\varphi(x,n)=0$ (l. 400); splitting $x=n_x+c(x)1$, $y=n_y+c(y)1$ gives $\varphi(x,y)=c(x)c(y)\varphi(1,1)$ (l. 401–402); the same splitting gives $f(y)=c(y)f(1)$ and, with $n_xy\in N$, $f(xy)=c(x)c(y)f(1)$ (l. 403); $a\mapsto af(1)$ is injective with left inverse $g$ (l. 404); $\psi(z)=g(z)\varphi(1,1)$ gives $\psi(f(xy))=\varphi(x,y)$ (l. 405–406). Correct; restricting to scalar-valued $\varphi$ is exactly Brešar Def. 1.1. Independent check: on $\mathbb F_3[t]/(t^3)$ with $f$ = constant term, $\dim\Zs=\dim\ker=8$.
* `rem:preserving` (l. 241–248), `rem:derivations` (l. 250–259): the bilinear maps $(x,y)\mapsto T(x)T(y)$ and $(x,y)\mapsto D(x)\cdot_\sigma y+x\cdot_\sigma D(y)$ vanish on the $\mu$-zero pairs, so Prop. 1.3(iv) applies; for $\mu=xy$ this is the first half of B Thm 7.2 (**PDF 117 / printed 114**), and "$S=D$ on $\operatorname{span}\{x\cdot_\sigma y\}$" is equivalent to $D$ being a braided-symmetric derivation. Correct.
* `def:determined` (l. 232–239): a faithful use of Prop. 1.3(iv); the "if and only if" is legitimate because the paper checks $(A,\mu)$ for zpd in the sense of Def. 1.1.

### m5-2.8 — citation fidelity of the material used in §4–§5 — **FINE**

| paper item | line | source | PDF / printed page | verdict |
|---|---|---|---|---|
| `def:bresar-zpd` = B Def. 1.1; "zpd for nonassociative algebras" | 183 / 139 | B Def. 1.1 with "Throughout the chapter, $A$ stands for a nonassociative algebra over a field $F$" | PDF 11–12 / 3–4 | **FINE** — nonassociative, over a field, both stated |
| l. 187 "as \citet[\S1.1] does" (the abbreviation zpd) | 187 | B §1.1 "The Definition of a zpd Nonassociative Algebra": "Throughout the book, we will use zpd as an abbreviation for 'zero product determined.'" | PDF 12 / 4 | **FINE** |
| `prop:bresar-zpd` = B Prop. 1.3 (i)–(iv) | 197 | B Prop. 1.3, (iv) "For every vector space $X$ over $F$ …" | PDF 12 / 4 | **FINE** — all four conditions, (iv) with arbitrary $X$ |
| `def:bresar-zjpd` = B Def. 3.14 | 189 | B Def. 3.14 | PDF 56 / 48 | **FINE** |
| `def:adrabi-bsder` = A Def. 3.1; l. 149 "\citet{Adrabi2026} takes $\alpha$ involutive, and we do not" | 208 / 149 | A §4: "so $\sigma_\alpha$ is an involution of $A\otimes A$ exactly when $\alpha$ is involutive"; "Let $\alpha$ be involutive, of either kind. Then $\sigma_\alpha(x\otimes y)=\alpha(y)\otimes\alpha(x)$ … The product it defines is $x\cdot_{\sigma_\alpha}y=xy+\alpha(y)\alpha(x)$" | A PDF p. 10 | **FINE** — the new sentence is correct, and A's formula matches the paper's |
| `def:bresar-zpp` = B Def. 7.1 | 216 | B Def. 7.1 | PDF 116 / 113 | **FINE** |
| `thm:bresar-zpp` = B Thm 7.2 incl. "Moreover … $c=T(1)$ … $T(x)=c\Phi(x)=\Phi(x)c$" | 222 | B Thm 7.2 | PDF 117 / 114 | **FINE** — the "Moreover" clause complete and correct |
| `cor:bresar-matrix` = B Cor. 2.17(a),(b) | 359 | B Cor. 2.17 | PDF 33 / 25 | **FINE** — hypotheses word for word |
| Tri definition, l. 357 `\citep[\S2.1]{Bresar2021}` | 357 | B §2.1 "zpd Rings": "… We denote it by $\mathrm{Tri}(R_1,M,R_2)$ and call a triangular ring." (§2.2 begins on printed p. 21 = PDF 29) | PDF 27 / 19 | **FINE** |
| l. 366 "The transpose reverses products \citep[\S 0.2.5]{HornJohnson2013}" | 366 | HJ §0.2.5 "The transpose, conjugate transpose, and trace"; "Both the transpose and the conjugate transpose obey the reverse-order law: … $(AB)^T=B^TA^T$" | PDF 26–27 / 6–7 | **FINE** — section number and pages correct |
| `thm:bresar-idempotents` = B Thm 2.27 | 414 | B Thm 2.27 | PDF 38 / 30 | **FINE** |
| B Thm 3.15 and Cor. 3.17 (l. 465, 473) | 465, 473 | B Thm 3.15; B Cor. 3.17 | PDF 57 / 49; PDF 60 / 52 | **FINE** |
| B Example 3.19 (l. 473, the quaternions) | 473 | B Ex. 3.19 | PDF 61–62 / 53–54 | **FINE** |
| Introduction \citep[Example 1.10] (local derivations) | 134, 153 | B Ex. 1.10 "… the answer is positive if $A$ is a unital zpd associative algebra" | PDF 16 / 8–9 | **FINE** |
| Introduction \citep[Preface] ×3; \citep[\S7.1]; \citep[\S7.3] | 126, 128, 129; 131; 135 | B Preface; B §7.1 (Banach, Lamperti); B §7.3 "Jordan Homomorphisms" | PDF 6; PDF 117 / 114; PDF 129 / 126 | **FINE** |
| l. 217 "algebras are associative \citep[\S7.1]" | 217 | B §7.1 "Throughout, it goes without saying that the algebras $A$ and $B$ are associative." | PDF 116 / 113 | **FINE** |

### m5-2.9 — internal consistency — **FINE**

27 distinct `\label`s, no duplicate numbering; every `\ref` resolves (checked against
`paper/build/braided-sym-zpd-v8.aux`; the build log has no undefined-reference warning); the three
labels never referenced (`cor:identity`, `def:bresar-zpd`, `def:bresar-zpp`) are unused, not
errors; all five bibliography keys exist and are cited. Abstract and Introduction map onto the
later results: criterion (l. 105 ↦ `cor:criterion`), unital zpd $\Rightarrow$ every $f(xy)$
(l. 108 ↦ `thm:zpd-fxy`), converse for injective $f$ (l. 109 ↦ `prop:injective`), the
commutative/endomorphism and anti-multiplicative cases (l. 164 ↦ `cor:twisted`, `cor:anti`), dual
numbers (l. 110, 166 ↦ `ex:dual`), the $\mathbb F_3$ computation (l. 111, 169 ↦ `prop:matrix`),
the question (l. 170 ↦ `q:noncomm`) — each is supported. The `claim-ok` comment at l. 164 ($K\times K$
with $\alpha(x,y)=(x+y,0)$; pairs $(e_2,e_2)$ and $(e_2,1)$) is correct in every characteristic:
both products are $e_2$, while $\mu=e_2+e_1$ and $\mu=e_2+2e_1$. The only typesetting nit:
"$\bar\circ\circ\,\Phi$" (l. 458) reads ambiguously; a thin space would help.

---

## Part 3 — repairs that landed during the audit, each checked

These were findings of mine on `68ce750` (and, for the last three, of the swarm as a whole). All are
now closed; I verified the repair itself rather than taking the changelog's word.

| repair | is it right? |
|---|---|
| `Tri` locator `\S2.2` → `\S2.1` (l. 357) | **yes** — B defines Tri on printed p. 19 / PDF 27; §2.2 (from printed p. 21) only uses it |
| "the automorphism $\Phi$" → "the **linear** automorphism" (l. 457) | **yes** — only linearity is used, and the two factors are not multiplicative |
| idempotents "$(e_{ii}+be_{ij})-e_{ii}$" → "$e_{ii}$ and $e_{ii}+be_{ij}$ … $be_{ij}=(e_{ii}+be_{ij})-e_{ii}$, $be_{ii}=(be_{ij})e_{ji}$" (l. 462–464) | **yes** — all three identities and the generation verified (m5-2.4); B's own proof says "$se_{ij}=(e_{ii}+se_{ij})-e_{ii}$ is a difference of two idempotents" (PDF 27 / printed 19) |
| "an algebra generated by idempotents" → "a **unital** algebra …", with B Thm 3.15 added (l. 464–465) | **yes**, and the hypothesis is indispensable (non-unital counterexample in m5-2.4) |
| "$n\ge2$" and now "for a unital algebra $B$" (l. 462) | **yes** — both are B's hypotheses in Cor. 2.4 and Cor. 2.17(a); without them $e_{ii}$ does not exist |
| `q:noncomm` rewritten twice; now "affirmative exactly for the zJpd algebras … \citep[Corollary 3.17] … negative for the real quaternions … \citep[Example 3.19]" (l. 473) | **yes** — every claim checked (m5-2.5); the earlier version ("affirmative … whenever $\alpha$ is inner") was false, $\mathbb H$ with $\alpha=\mathrm{id}$ being the counterexample |
| `rem:inner`'s last clause: "what that computation establishes is that $\mu_\alpha$ has no form $f(xy)$, not the determination itself" → "its computation checks the criterion of Corollary~\ref{cor:criterion} directly in a small case, and $\mu_\alpha$ has no form $f(xy)$ by the argument above" (l. 467–468) | **yes** — the old clause misdescribed `prop:matrix` (whose proof establishes $\Zs=\ker$, with no $f$ in it) and contradicted the abstract (l. 111) and the Introduction (l. 169); the new one is exactly what the proof does |
| "13 = 13" → "$\dim\Zs=\dim\ker=13$" (l. 449) | **yes** — both dimensions are 13 |
| "Throughout, $A$ is unital" → "Throughout Sections 3 to 5" (l. 230) | **yes** — the unit is used in §§4–5 |
| `ex:dual` now states its relation to B's Example 2.23 (l. 421) | **yes** — the example is symmetrically zpd and not zpd there, and the twisted product here is a different bilinear map |
| `prop:injective`'s converse restored for $\alpha=\mathrm{id}$ (l. 384–386) | **yes** — for $\alpha=\mathrm{id}$ the map is $f=\mathrm{id}+\alpha=2\,\mathrm{id}$, injective, and `cor:identity`(ii) gives the converse |

---

## Summary

| locator (line in `5b7e067`, label) | verdict | one-line repair |
|---|---|---|
| l. 473 `q:noncomm` — "the question is about algebras admitting an involutive automorphism that is not inner" | **IMPRECISE** | "the question is about a non-inner $\alpha$; for an inner one it is the question of which algebras are zJpd" |
| l. 465 `rem:inner` — `\citep[Theorem 2.1]{AnLiHe2015}` | **UNVERIFIABLE** | source absent; content corroborated by B Thm 3.15 (cited) and B Cor. 3.17 |
| l. 158, 267–268 — `BriceHuang2015` "Theorem 2.3 … over a commutative ring" | **UNVERIFIABLE** | source absent; quote the theorem or weaken to "over a field, cf. [BH, Thm 2.3]" |
| l. 435–447 `prop:matrix` — rank 4, $\dim\ker 12$, 417 pairs, span 12 | **FINE** | — (all four numbers reproduced independently) |
| l. 449 — "$\dim\Zs=\dim\ker=12$", "$\dim\Zs=\dim\ker=13$" | **FINE** | — (12/12 and 13/13 reproduced) |
| l. 452–461 `rem:inner` — Jordan identity, $\Phi$-intertwining, "linear automorphism", independence of $D$ | **FINE** | — (0 mismatches on 6561 pairs; all 48 invertible $D$ give 12/12) |
| l. 462–468 `rem:inner` — generating idempotents, "unital", `thm:zpd-fxy` case $n=2$ | **FINE** | — (identities and generation verified, incl. a non-commutative $B$; "unital" indispensable) |
| l. 471–473 `q:noncomm` — "exactly the zJpd algebras", $M_n(B)$, Tri, $H$ negative, Skolem–Noether | **FINE** | — (verified; $H$ by exact arithmetic, $T_2(\mathbb F_3)$ numerically, B Cor. 3.17/Ex. 3.19 quoted) |
| l. 420–428 `ex:dual` — dual numbers determined but not zpd; idempotents $0,1$; relation to B Ex. 2.23 | **FINE** | — (verified for $p=3,5,7$) |
| l. 279–407, 241–259, 311–386, 326–328, 232–239 — `thm:zpd-fxy`, `prop:injective`, `cor:identity`, Jordan paragraph, `cor:twisted`, `cor:anti`, `cor:triangular`, `thm:codim`, `rem:preserving`, `rem:derivations`, `def:determined` | **FINE** | — (proofs checked line by line; spot-checked numerically) |
| l. 183, 187, 189, 197, 208, 216, 222, 357, 359, 366, 414 — Brešar Def. 1.1/§1.1/Def. 3.14/Prop. 1.3/Def. 7.1/Thm 7.2/Cor. 2.17/§2.1/Thm 2.27, Adrabi Def. 3.1 and §4, Horn & Johnson §0.2.5 | **FINE** | — (word for word, hypotheses included, page numbers given) |

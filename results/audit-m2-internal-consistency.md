# Task C — internal consistency of `paper/braided-sym-zpd.tex` (referee report)

**Auditor:** m2 (swarm smvxd25ff, direction d5).
**Snapshot audited:** `paper/braided-sym-zpd.tex`, **496 lines, md5 `6f667038e087509e3e094b582f8a4262`**,
mtime 2026-11-01 05:10:58 UTC. **The file was edited twice while this audit ran** (480 → 491 → 496
lines); the section "Repaired while this audit was running" records those items, with the verification that
the repairs are correct. All line numbers below refer to the snapshot above.
**Build check:** the snapshot compiles twice with `pdflatex` (0 errors) into `.scratch/audit/m2/build/`, the
log has **no** undefined or multiply-defined reference, and the `.aux` numbers are 2.1–2.6, 3.1–3.4,
4.1–4.7, 5.1–5.6, all distinct.
**Scripts:** `results/audit-scripts/m2-xref.py` (cross-reference graph), `results/audit-scripts/m2-f3-check.py`
(exact $\mathbb{F}_3$ arithmetic), `results/audit-scripts/m2-idempotents-check.py` (idempotent / nilpotent /
block-matrix checks). Text extraction: `.scratch/audit/m2/paper-v8.txt`.
**Scope.** (i) the cross-reference graph and the numbering; (ii) every assertion of the abstract and of the
Introduction against the numbered results that are supposed to support it; (iii) prose and markup against
the mathematics. Source-locator fidelity (Brešar, Adrabi, Horn–Johnson) and the mathematical audit of §4,
of the numerics of `prop:matrix` and of `rem:inner` are other directions' work (d1/m6, d2/m5, d3/m3,
d4/m8, d7/m1); where my checks touch theirs I say so.

**Result in one line.** The reference layer is clean, the numbering has no duplicate, and every prose number
I recomputed is correct. **One error remains**: the abstract and the last sentence of Remark 5.5 contradict
each other about what the $\mathbb{F}_3$ computation establishes. Eight imprecisions follow, one of them a
missing support in the newly written Question 5.6.

---

## F1 — ERROR (L111 abstract / L467–469 `rem:inner`) — the abstract and Remark 5.5 contradict each other

**Paper, L111 (abstract, last sentence):**
> "A computation over $\mathbb{F}_3$ shows that the algebra of $2 \times 2$ matrices is determined by a
> twisted product that has no form $f(xy)$."

**Paper, L467–469 (`rem:inner`, last sentence):**
> "Proposition~\ref{prop:matrix} is the case $n = 2$ and $D = \operatorname{diag}(1,-1)$: what that
> computation establishes is that $\mu_\alpha$ has no form $f(xy)$, not the determination itself."

The two sentences say opposite things about the same computation: the abstract attributes *determination* to
it, `rem:inner` explicitly denies that it establishes determination.

**What the proof actually does (L441–447).** "The matrix of $\bar\mu_\alpha$ … has rank $4$ over
$\mathbb{F}_3$, so $\dim \ker \bar\mu_\alpha = 12$. Among the $81 \cdot 81$ pairs $(x,y)$, exactly $417$
satisfy $\mu_\alpha(x,y) = 0$. … the $417$ tensors $x \otimes y$ span a subspace of dimension $12$. So the
two subspaces have the same dimension and are equal." With Corollary 3.4, cited in the same proof (L443),
that *is* the determination of $M_2(\mathbb{F}_3)$ by $\mu_\alpha$. So "not the determination itself"
denies the conclusion of the proof above it.

**The "no form $f(xy)$" half is not a computation at all.** It is proved at L432 for *every* noncommutative
algebra with an automorphism:
> "When $\alpha$ is an automorphism of a noncommutative algebra, the twisted product $xy + \alpha(yx)$ is
> not of the form $f(xy)$ (indeed $y = 1$ forces $f = \mathrm{id} + \alpha$, and then $\alpha(yx) =
> \alpha(xy)$, so $yx = xy$ by injectivity of $\alpha$)."

I checked the hypotheses on the actual pair: $\alpha$ = conjugation by $\operatorname{diag}(1,-1)$ on
$M_2(\mathbb{F}_3)$ is an involutive automorphism with $\alpha(1)=1$, injective, and the algebra is
noncommutative (exact arithmetic, `m2-f3-check.py`, last line: "alpha^2 = id -> True ;
alpha(xy) = alpha(x)alpha(y) -> True"). Neither $417$ nor rank $4$ is used anywhere in that argument, and no
computation in the paper produces "no form $f(xy)$".

**Verdict: ERROR.** Two statements about the paper's own proof, at least one of which (L467–469) is false.
(The charitable reading — "the determination is now also a consequence of Remark 5.5, so the added value of
Proposition 5.4 is elsewhere" — is not what the sentence says, and it would still leave the abstract's
attribution wrong, because the computation establishes determination and says nothing about $f(xy)$.)

**Minimal repair.** L111: "… is determined by a twisted product which, by the argument following Example 5.3,
is not of the form $f(xy)$." L467–469: "… Proposition 5.4 is the case $n = 2$ and
$D = \operatorname{diag}(1,-1)$; its computation checks the criterion of Corollary 3.4 directly."

---

## F2 — IMPRECISE (L266–268 vs L158, L271) — the note after Corollary 3.4 still says Brešar covers only "$\mu$ the product"

**Paper, L267–268:**
> "The criterion is stated for an arbitrary bilinear $\mu$, over a commutative ring, by Brice and Huang
> \citep[Theorem 2.3]{BriceHuang2015}; **for $\mu$ the product** it is Proposition 1.3 of Brešar, recalled as
> Proposition~\ref{prop:bresar-zpd}."

but the Introduction, as revised in mid-audit (L158), now says
> "Our first result is a criterion, which is Proposition 1.3 of Brešar **for the algebra $(A,\mu)$**, and
> Theorem 2.3 of Brice and Huang for an arbitrary bilinear $\mu$ over a commutative ring."

and the proof (L271) applies Brešar's Proposition 1.3 "to the nonassociative algebra $(A,\mu)$" with $\mu$
arbitrary. A nonassociative algebra is a vector space with an arbitrary bilinear product, so Brešar's
statement already covers Corollary 3.4; the note's restriction "for $\mu$ the product" contradicts both the
Introduction and the proof.

**Verdict: IMPRECISE** (the Introduction and the proof are right; the note is the inaccurate sentence).
**Minimal repair.** "… by Brice and Huang \citep[Theorem 2.3]{BriceHuang2015}; the case $\mu$ = the product
of a nonassociative algebra is Proposition 1.3 of Brešar, recalled as Proposition 2.3, and Corollary 3.4 is
that statement applied to $(A,\mu)$."

**Unverifiable here.** `BriceHuang2015` is not among the supplied PDFs, so neither the commutative-ring
setting nor the exact content of its Theorem 2.3 can be checked from the material; I assert nothing about
them.

---

## F3 — IMPRECISE (L144 vs L208–211, L251) — "we do not require $\sigma^2=\mathrm{id}$", but the derivation notion does

**Paper, L144 (Introduction):**
> "In this paper a \emph{braiding} is a linear map $\sigma$ of $A \otimes A$, and we do not require
> $\sigma^2 = \mathrm{id}$, which differs from \citep[Definition 3.1]{Adrabi2026}."

**Paper, L208–210 (Definition 2.4, the only definition of the central notion):**
> "Let $A$ be a $K$-algebra and let $\sigma$ be a $K$-linear **involution** of $A \otimes A$. A
> \emph{braided-symmetric derivation} for $\sigma$ is a $K$-linear map $D \colon A \to A$ that satisfies
> $D(x \cdot_\sigma y) = D(x) \cdot_\sigma y + x \cdot_\sigma D(y)$ …"

and `rem:derivations` (L251): "Let $\sigma$ be an **involution** of $A \otimes A$". The paper never defines a
braided-symmetric derivation for a non-involutive $\sigma$.

**The three advertised braidings against Definition 2.4.** Identity and swap are involutions. The twisted
swap $\tau_\alpha(x \otimes y) = \alpha(y) \otimes \alpha(x)$ satisfies $\tau_\alpha^2(x \otimes y) =
\alpha^2(x) \otimes \alpha^2(y)$, so $\tau_\alpha$ is an involution **iff $\alpha^2 = \mathrm{id}$**. But
the abstract's twisted case is "$\alpha$ an endomorphism" (L106, L144–149), and an endomorphism need not
satisfy $\alpha^2 = \mathrm{id}$; the abstract nevertheless promises (L104) to study "the braided-symmetric
derivations of that product". For such an $\alpha$, no braided-symmetric derivation is defined.

**Verdict: IMPRECISE.**
**Minimal repair.** After Definition 2.4: "This definition is used only for involutions; the twisted swap is
an involution exactly when $\alpha^2 = \mathrm{id}$", and qualify L104 with "for involutions $\sigma$".

---

## F4 — IMPRECISE (L474 `q:noncomm`) — the triangular algebras are claimed zJpd, but nothing in the paper gives that

**Paper, L474:**
> "By Remark~\ref{rem:inner} an inner $\alpha$ makes the twisted product a Jordan product in disguise, so
> the answer is affirmative exactly for the zJpd algebras: it is affirmative for $M_n(B)$ **and for the
> triangular algebras of Corollary~\ref{cor:bresar-matrix}(b)**, in characteristic other than $2$, and
> negative for the real quaternions with $\alpha = \mathrm{id}$, which are not zJpd
> \citep[Example 3.19]{Bresar2021}."

* For $M_n(B)$ the paper has just proved the needed input: idempotent generation plus Brešar's Theorem 3.15
  (L463–466).
* For $\mathrm{Tri}(A_1,M,A_2)$ the paper proves **zpd** (Corollary 4.6(b), quoted from Brešar), while the
  sentence needs **zJpd**. The only route to zJpd that the paper uses is idempotent generation plus Brešar's
  Theorem 3.15 (L463–466), and generation by idempotents is not established for $\mathrm{Tri}(A_1,M,A_2)$
  anywhere in the paper — the passage of Brešar that states the zpd/zJpd link does so only for commutative
  algebras (2021, printed p. 49: "a commutative algebra is zpd if and only if it is zJpd"). So the triangular
  half of this sentence has no support in the paper.

**What does support it.** Brešar's **Corollary 3.17(b)** (2021, printed p. 52) says exactly: "The algebra
$\mathrm{Tri}(A_1, M, A_2)$, where $A_1$ and $A_2$ are unital algebras generated by idempotents and $M$ is a
unital $(A_1,A_2)$-bimodule", is zJpd over a field of characteristic not 2 — and part (a) is $M_n(B)$.

**Verdict: IMPRECISE** (true statement, missing/incorrect support).
**Minimal repair.** Cite \citep[Corollary 3.17]{Bresar2021} for both families: "… it is affirmative for
$M_n(B)$ and for the triangular algebras of Corollary 4.6(b), in characteristic other than $2$
\citep[Corollary 3.17]{Bresar2021} …".

---

## F5 — IMPRECISE (L173, L180–181) — §2 describes its own contents inaccurately

**Paper, L173:** "Section~\ref{sec:prelim} recalls the definitions and the results of Brešar that we use, and
it contains no new results."
**Paper, L180–181:** "This section recalls the notions of Brešar that we need, and none of it is new. We
recall two definitions and then the equivalent forms of the first."

§2 in fact consists of Definitions 2.1 and 2.2 (Brešar), Proposition 2.3 (Brešar), **Definition 2.4
(Adrabi [1, Definition 3.1])**, Definition 2.5 and Theorem 2.6 (Brešar): six items, one of them Adrabi's, and
"two definitions" describes only the first two.

**Verdict: IMPRECISE.**
**Minimal repair.** "Section 2 recalls the notions of Brešar and Adrabi that we use …"; "We recall the two
basic definitions and the equivalent forms of the first, then Definition 2.4 of Adrabi, Definition 7.1 and
Theorem 7.2 of Brešar."

---

## F6 — IMPRECISE (L234 `def:determined`) — "(iv)" alone cannot justify an "if and only if"

**Paper, L234:**
> "By \citet[Proposition 1.3(iv)]{Bresar2021} this holds **if and only if**, for every vector space $V$ and
> every bilinear map $\varphi \colon A \times A \to V$ with $\varphi(x,y) = 0$ whenever $\mu(x,y) = 0$,
> there is a linear map $\psi \colon A \to V$ with $\varphi(x,y) = \psi(\mu(x,y))$ …"

Condition (iv) is one condition; the equivalence used is (i)⟺(iv) of the same proposition. As written, a
definition contains a theorem and cites one *clause* of a proposition for an equivalence.

**Verdict: IMPRECISE.**
**Minimal repair.** "By the equivalence of (i) and (iv) in [4, Proposition 1.3], …".

---

## F7 — IMPRECISE (L452 `rem:inner`, L474) — a proposition-sized result is numbered as a Remark and then used as a result

`rem:inner` (L452–470) contains the equivalence "Hence $A$ is determined by $\mu_\alpha$ if and only if $A$
is determined by the Jordan product, and the answer does not depend on $D$" (L460–462), with a proof, and
Question 5.6 rests on it: "By Remark~\ref{rem:inner} an inner $\alpha$ makes …" (L474). A load-bearing
equivalence should not be a "Remark".

**Verdict: IMPRECISE.**
**Minimal repair.** Promote the general statement to a Proposition (or Lemma) with its proof and cite it in
Question 5.6; keep the matrix-algebra paragraph as a remark.

---

## F8 — IMPRECISE (L311 `cor:identity`, L183 `def:bresar-zpd`, L216 `def:bresar-zpp`) — one result and two definitions are never cited

Corollary 4.3 (L311) is the paper's result for the identity braiding and is referenced by **no** `\ref`
anywhere, although it is the only support for the abstract's "the identity braiding gives nothing new in
characteristic other than $2$" (L109) and for the Introduction's "The identity braiding has this form"
(L164). Definitions 2.1 and 2.5 are likewise never referenced (the text cites Brešar's own numbers instead).

**Verdict: IMPRECISE** (housekeeping).
**Minimal repair.** Cite Corollary 4.3 at L164 and after L324; cite Definition 2.5 in Theorem 2.6's "zero
product preserving linear map" and Definition 2.1 at L180, or drop the unused labels.

---

## F9 — IMPRECISE (L326, L148, L337) — naming and notation

* The Introduction names the three braidings "the identity", "the swap", "the twisted swap" (L147–149), but
  L326 calls the second one "**The standard braiding** gives the Jordan product"; the same product is
  elsewhere "the Jordan product".
* $\mu_\alpha$ is used from L337 on but never defined as the instance $\mu_{\tau_\alpha}$ of L145 for the
  twisted swap $\tau_\alpha$ of L149 (the reader has to infer it from L150).

**Verdict: IMPRECISE** (readable, not wrong).
**Minimal repair.** "the swap (standard) braiding" once; and "for the twisted braiding $\tau_\alpha$ we write
$\mu_\alpha = \mu_{\tau_\alpha}$".

---

## F10 — FINE (L441–447 `prop:matrix`) — the four numbers of the computation are correct

Recomputed exactly and independently (`m2-f3-check.py`): $\dim A \otimes A = 16$ over $\mathbb{F}_3$;
rank $\bar\mu_\alpha = 4$; $\dim \ker \bar\mu_\alpha = 12$; exactly **417** of the $81 \cdot 81 = 6561$ pairs
satisfy $\mu_\alpha(x,y)=0$; those 417 tensors span a subspace of dimension **12**. So the paper's four
numbers are right. (Hand cross-check of the count: $1\cdot 81 + 32 \cdot 9 + 48 \cdot 1 = 417$, with
$|\{x : \operatorname{rank} x = 1\}| = 32$ and $|\mathrm{GL}_2(\mathbb{F}_3)| = 48$.) d2/m5 holds the
numerics as its own direction; this is an independent confirmation, not a claim of new work.

**Verdict: FINE.**

---

## F11 — FINE (L450) — the "12" and "13" of the remark are correct

**Paper, L450:** "The same computation gives $\dim \Zs = \dim \ker = 12$ for the ordinary product … and
$\dim \Zs = \dim \ker = 13$ for the twist by the transpose, taken with the braiding product $xy + y^{\mathsf
T}x^{\mathsf T} = xy + (xy)^{\mathsf T}$." (Until mid-audit this read "$13 = 13$"; the repair is correct.)

Computation (`m2-f3-check.py`, exact):

| $\mu(x,y)$ | rank $\bar\mu$ | $\dim\ker\bar\mu$ | zero pairs | dim span |
|---|---|---|---|---|
| $xy$ (ordinary product) | 4 | 12 | 417 | 12 |
| $2xy$ (identity braiding) | 4 | 12 | 417 | 12 |
| $xy + yx$ (swap) | 4 | 12 | 417 | 12 |
| $xy + \alpha(y)\alpha(x)$, $\alpha$ = conj. $\mathrm{diag}(1,-1)$ | 4 | 12 | 417 | 12 |
| $xy + y^{\mathsf T}x^{\mathsf T} = xy + (xy)^{\mathsf T}$ | 3 | **13** | 513 | **13** |

Both claims hold. (Also: $xy + y^{\mathsf T}x^{\mathsf T} = (\mathrm{id}+T)(xy)$, so this case is already
covered by Corollary 4.5 with $\alpha = T$ — worth a pointer, not an error.)

**Verdict: FINE.**

---

## F12 — FINE — cross-reference graph, numbering, part-references

`m2-xref.py` on the snapshot: **27 labels, 58 `\ref`s, 0 dangling, 0 duplicate labels.** Every reference
carries the prose word matching the environment that holds the label (54 singular uses; the remaining 4 sit
in two plural pairs, L277 "Corollaries … and …" and L432 "Theorems … and …", and are correct). All
part-references exist: Corollary 4.6(a) (L162, 366, 450), Corollary 4.6(b) (L373, 379, 474), Proposition
2.3(iv) (L287). The two new `\ref`s of the mid-audit edit, "Throughout
Sections~\ref{sec:criterion} to~\ref{sec:beyond}" (L230), resolve and render as "Sections 3 to 5". I read all
58 semantically as well: each points at the statement its sentence needs.

The snapshot compiles with **no undefined and no multiply-defined reference** (`.scratch/audit/m2/build/`),
and the `.aux` assigns 2.1–2.6, 3.1–3.4, 4.1–4.7, 5.1–5.6, all distinct (the `theorem` counter is shared by
theorem/lemma/corollary/proposition/definition/example/question/remark, so no duplicate is possible; the
separate `notation` counter is never used).

**Verdict: FINE.**

---

## F13 — FINE — the source numbers quoted in the prose agree with the environments, and the two locators added mid-audit are right

| prose | environment with the same locator | checked against the source |
|---|---|---|
| L158 "Proposition 1.3 of Brešar" | Proposition 2.3, `[Proposition 1.3]` (L197) | (m6's direction) |
| L173 "the results of Brešar" | Definitions 2.1, 2.2, 2.5, Theorem 2.6 | — |
| L413 / L415 "Theorem 2.27" | Theorem 5.2, `[Theorem 2.27]` (L415) | (m6's direction) |
| L187 "as \citet[Definition 1.1]{Bresar2021} does" | Definition 2.1 (L183) | — |
| L466 "Theorem 3.15 … originally Theorem 2.1 of [2]" | — | **verified**: Brešar 2021, printed p. 49: "Theorem 3.15 Let A be an (associative) unital algebra over a field F of characteristic not 2. If A is generated by idempotents, then A is zJpd." Brešar's own attribution: "The following theorem was obtained in [24]", and his [24] is "G. An, J. Li, J. He, Zero Jordan product determined algebras. Linear Algebra Appl. 475, 90–93" — exactly the paper's [2]. |
| L474 "Example 3.19" | — | **verified**: Brešar 2021, printed pp. 53–54, concludes "Therefore, H is not zJpd." |

**Verdict: FINE.** (The two locators added during the audit are correct as quoted; the *original* numbering
"Theorem 2.1" of An–Li–He cannot be checked here because that paper is not in the supplied material, but the
substance is now carried by Brešar, which is.)

---

## Repaired while this audit was running (verified)

The file changed twice during the audit. The following items were repaired by that editing; I record them
because the repairs must be checked too, not because they are open.

| item | before | now | verification |
|---|---|---|---|
| the "idempotents" of `rem:inner` | "the idempotents $(e_{ii}+be_{ij})-e_{ii}$", i.e. $be_{ij}$, which has square $0$ | "$e_{ii}$ and $e_{ii}+be_{ij}$ … (indeed $be_{ij}=(e_{ii}+be_{ij})-e_{ii}$ and $be_{ii}=(be_{ij})e_{ji}$)" (L463–465) | `m2-idempotents-check.py`: $(e_{11}+be_{12})^2 = e_{11}+be_{12}$ and $(be_{12})(e_{21}) = be_{11}$ for $b \in M_2(\mathbb{F}_3)$ (non-commutative $B$), and $(be_{12})^2=0$; also over $\mathbb{F}_2,\mathbb{F}_3,\mathbb{F}_5$ with scalar $b$. **Correct now.** |
| "unital" in Corollaries 4.3, 4.4, 4.7 | assumed only in the §3 preamble, which was scoped to §3 | "Throughout **Sections 3 to 5**, $A$ is a unital associative algebra …" (L230) | the statement-level hypothesis is now in force wherever Theorem 4.1 is invoked. **Correct now** (the "unital" left in Theorems 4.1 and Corollary 4.5 is redundant, not wrong). |
| "$13 = 13$" | unexplained | "$\dim \Zs = \dim \ker = 13$" (L450) | F11: $13 = 13$ confirmed. **Correct now.** |
| Tri locator | `[\S2.2]{Bresar2021}` | `[\S2.1]{Bresar2021}` (L358) | (m6's direction) |
| Brice–Huang in the Introduction | credited only in the note after Corollary 3.4 | also at L158 | partially repaired: the note itself still says the old thing (F2). |
| $\Phi$ in `rem:inner` | "the automorphism" | "the linear automorphism" (L458) | correct: $\Phi$ is $K$-linear on $A\otimes A$, not an algebra automorphism. |
| An–Li–He | sole source for the zJpd step | Brešar's Theorem 3.15, "originally" An–Li–He (L466) | F13: verified. |

---

## Abstract and Introduction against the results (complete map)

Every sentence of the abstract (L102–111) and every *internal* assertion of the Introduction (the
source-attributions L126–136 belong to d1/m6 and d3/m3 and are not judged here):

| # | claim (line) | what supports it | verdict |
|---|---|---|---|
| A1 | L102 "every bilinear map that vanishes on the pairs with zero product factors through the product" | Definition 2.1 states the functional form; Proposition 2.3(iv) gives this form | FINE |
| A2 | L103 "replace the product by any bilinear map $\mu$" | Definition 3.1 | FINE |
| A3 | L104 "… and hence when the braided-symmetric derivations of that product can be studied through zero products" | Definition 2.4 + Remark 3.3, but 2.4 needs $\sigma$ involutive | **F3** |
| A4 | L105 "criterion in terms of the kernel … and it needs no surjectivity hypothesis" | Corollary 3.4 (no hypothesis at all) | FINE |
| A5 | L106 "three braidings on a commutative algebra … $\mu$ has the form $f(xy)$" | L309 ($f=2\,\mathrm{id}$), L326–329 (swap: $xy+yx=2xy$), Corollary 4.4 (twisted); the swap case is implicit only | FINE (implicit) |
| A6 | L107 "The same holds on any algebra when the twist reverses products" | Corollary 4.5 ("any [such] algebra") | FINE |
| A7 | L108 "Every unital zero product determined algebra is determined by every such $\mu$" | Theorem 4.1 | FINE |
| A8 | L109 "The converse holds when $f$ is injective, so the identity braiding gives nothing new in characteristic other than 2" | Proposition 4.2 + Corollary 4.3(ii), the latter never cited | **F8** |
| A9 | L110 "the dual numbers are determined by their twisted product but are not zero product determined" | Example 5.3 + Theorem 5.2 (char $\ne 2$ stated there; in char 2, $\alpha=\mathrm{id}$, $f=0$, $\mu\equiv0$ and the claim holds trivially) | FINE |
| A10 | L111 "A computation over $\mathbb{F}_3$ shows that … is determined by a twisted product that has no form $f(xy)$" | Proposition 5.4 (determination) + L432 (no form) — the computation shows neither part | **F1** |
| I1 | L155 "Remark 3.2 gives the first part of Theorem 2.6" | Remark 3.2, Theorem 2.6 | FINE |
| I2 | L154 "Remark 3.3 takes the first step" | Remark 3.3 | FINE |
| I3 | L158–159 first result (Brešar + Brice–Huang), Corollary 3.4 | Corollary 3.4 | FINE (note at L268 lags: F2) |
| I4 | L160–164 second result: Theorem 4.1, Corollary 4.6(a), Corollary 4.7, Proposition 4.2, Corollaries 4.4, 4.5 | all exist, quoted with the right words | FINE (mod. F8) |
| I5 | L165–167 third result: Theorem 5.1 + Example 5.3 | Theorem 5.1, Example 5.3 | FINE |
| I6 | L168–169 fourth result: "a twisted product that has no form $f(xy)$", Proposition 5.4 "shows by computation" | Proposition 5.4 shows determination; L432 shows no form | **F1** |
| I7 | L170 "Question 5.6 asks for the general case" | Question 5.6 | FINE |
| I8 | L173–176 plan of the paper | §2–§5 as described, except "the results of Brešar" for §2 | **F5** |

No claim of the abstract or Introduction is left without *some* support; the failures above are support
attributed to the wrong item (F1) and a missing support (F4).

---

## Categories in which I found nothing (explicitly)

* **Dangling references:** none (58/58 resolve).
* **Duplicated labels or numbers:** none (23 numbered items, all distinct in the `.aux`).
* **Prose word vs. environment kind:** no mismatch (54 singular uses correct; the 4 references in the two
  plural pairs are correct).
* **Part-references that do not exist:** none (4.6(a), 4.6(b), 2.3(iv) all present; nothing 
  references 4.3, which is F8).
* **Undefined or multiply-defined references in the build:** none (fresh build of the snapshot).
* **Prose numbers I could not reproduce:** none — 16, 4, 12, 417, 12, "12 = 12", "$\dim\Zs=\dim\ker=13$"
  all confirmed exactly.
* **Abstract/Introduction claims with no support at all:** none; one is attached to the wrong support (F1)
  and one support is missing (F4).

---

## Final table

| locator | verdict | one-line repair |
|---|---|---|
| L111 abstract / L467–469 `rem:inner` | **ERROR** | the two sentences contradict each other about the $\mathbb{F}_3$ computation: keep "determination" for the computation and cite L432 for "no form $f(xy)$". |
| L267–268 note after `cor:criterion` | IMPRECISE | Brešar's Proposition 1.3 already covers arbitrary $\mu$ (as L271 uses); drop "for $\mu$ the product". |
| L144 vs L208–211, L251 | IMPRECISE | Definition 2.4 needs $\sigma$ involutive; the twisted swap is involutive iff $\alpha^2=\mathrm{id}$ — say so. |
| L474 `q:noncomm` | IMPRECISE | the triangular algebras' zJpd-ness is not proved here: cite Brešar \citep[Corollary 3.17]{Bresar2021} (printed p. 52). |
| L173, L180–181 | IMPRECISE | §2 also quotes Adrabi's Definition 3.1: "the notions of Brešar and Adrabi". |
| L234 `def:determined` | IMPRECISE | "By the equivalence of (i) and (iv) in Proposition 1.3". |
| L452 `rem:inner` / L474 | IMPRECISE | promote the Jordan-product equivalence to a Proposition and cite it in Question 5.6. |
| L311 `cor:identity`, L183, L216 | IMPRECISE | cite Corollary 4.3 at L164 and L324; cite Definitions 2.1 and 2.5 where they are used. |
| L326, L148, L337 | IMPRECISE | one name for the swap; define $\mu_\alpha = \mu_{\tau_\alpha}$. |
| L441–447 `prop:matrix` | FINE | 16, rank 4, $\dim\ker$ 12, 417 zero pairs, span 12 — all reproduced exactly. |
| L450 | FINE | "12 = 12" and "$\dim\Zs=\dim\ker=13$" both reproduced (13 zero-dim, 513 zero pairs). |
| L463–465 `rem:inner` | FINE | the repaired idempotent sentence is correct (checked over non-commutative $B$). |
| L466 (`[3.15]`, `[2.1]`), L474 (`[3.19]`) | FINE | Brešar p. 49 / pp. 53–54 confirm both; his [24] is An–Li–He. |
| whole file (xref/numbering) | FINE | 58 references, 0 dangling, 0 duplicates, 0 undefined, all part-references valid. |

*Source-hygiene footnote (not a mathematical finding):* 19 review annotations `% claim-ok:` / `% reproof-ok:`
remain in the source (L147, 148, 150, 164, 193, 206, 213, 220, 248, 331, 344, 383, 410, 411, 419, 422, 434,
450, 473). Invisible in the PDF, but they should not be shipped.

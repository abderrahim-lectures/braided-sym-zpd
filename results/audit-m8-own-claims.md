# Referee report — own-claim audit of `paper/braided-sym-zpd.tex` (member m8, direction d4)

**Snapshot audited.** `paper/braided-sym-zpd.tex`, **496 lines, md5 `6578350f40e335d99da61adc07424726`**,
copied to `.ultramath/smvxd25ff/m8/final-snapshot.tex`. All line numbers below refer to it.
The file was edited **five times while this audit ran** (480 → 491 → 496 lines). Items that were present at
the start of the run and are no longer in the snapshot are recorded in §4, with a verification of the
repair, and are not listed as open findings.

**Method.** (i) Every statement in my scope was re-proved by hand. (ii) Every recalled source statement was
compared word by word with `pdftotext -layout` extracts that carry PDF-page markers
(`.scratch/audit/m8/{bresar,adrabi,hj}.txt`, made with `pagemap.py`). (iii) Every numeric claim was
recomputed in exact F_p arithmetic. (iv) Each theorem was stress-tested: all linear f on two zpd algebras,
non-zpd algebras satisfying `thm:codim`, and characteristic 2 versions.
Scripts: `results/audit-scripts/m8-f3-twisted.py`, `m8-q-noncomm-jordan.py`, `m8-stress-theorems.py`,
`m8-cor-twisted-anti.py`.

**Scope.** The assigned items: `def:determined`, `rem:preserving`, `rem:derivations`, `cor:criterion`,
`thm:zpd-fxy`, `prop:injective`, `cor:identity`, the Jordan-product paragraph, `cor:twisted`, `cor:anti`,
`cor:triangular`, `thm:codim`, `ex:dual`, `prop:matrix`, `rem:inner`, `q:noncomm`, the abstract and the
Introduction, plus the source recalls they rest on and the internal consistency of the cross-references.

---

## 1. Findings open in the audited snapshot

### F1 — IMPRECISE — L104 (abstract) and L154 (Introduction): "the braided-symmetric derivations of that product"

**Paper (L104):** "For the symmetrized products mu_sigma, this asks when the algebra with that product is zero
product determined, and hence when the braided-symmetric derivations of that product can be studied through
zero products."
**Paper (L154):** "So an algebra determined by mu_sigma is one whose braided-symmetric derivations can be
studied through zero products, as local derivations are [Bresar, Example 1.10]."

**Source (Adrabi 2026, Definition 3.1, PDF p. 5):** "Let A be a K-algebra and let sigma be a K-linear
**involution** of A (x) A. A braided-symmetric derivation for sigma is a K-linear map D: A -> A that
satisfies identity (1) ..."
**Source (Adrabi 2026, §4, PDF p. 10):** "... sigma_alpha is an involution of A (x) A exactly when alpha is
involutive."

**Mathematics.** The paper's own Definition 2.4 (L199) keeps "sigma a K-linear involution of A (x) A", and
`rem:derivations` (L251) begins "Let sigma be an **involution** of A (x) A". But the twisted swap
sigma(x (x) y) = alpha(y) (x) alpha(x) satisfies sigma^2(x (x) y) = alpha^2(x) (x) alpha^2(y), so sigma is an
involution **iff** alpha^2 = id. Corollary 4.4 (L335) assumes only that alpha is an endomorphism, and
Corollary 4.5 (L346) only that alpha reverses products; for alpha^2 != id (e.g. A = K x K, alpha(x,y) = (x,x))
these determine A by a product mu_sigma for which no braided-symmetric derivation is defined anywhere in the
paper. "The braided-symmetric derivations of that product" therefore does not denote a defined object for two
of the paper's three advertised braidings.

**Minimal repair.** In L104 and L154 insert "for an involution sigma": "... and hence, when sigma is an
involution, when the braided-symmetric derivations of that product can be studied ...".

### F2 — IMPRECISE — L141: "The main purpose of this paper is to decide which algebras are determined by which mu."

No decision procedure and no classification is delivered: the paper gives a criterion (Cor. 3.4), two
sufficient conditions (Thm. 4.1, Thm. 5.1), one counterexample (Ex. 5.3) and one computation (Prop. 5.4), and
its own §5 ends with an open question (L472–475). **Repair:** "The main purpose of this paper is to give a
criterion for determination by mu and to settle the question for several classes of algebras and products."

### F3 — IMPRECISE (markup) — L327: "x circ 1/2 = x"

1/2 is a scalar, A is a K-algebra and x in A; the intended element is (1/2)1. **Repair:** write
`$x \circ (\tfrac12\, 1) = x$`.

### F4 — UNVERIFIABLE — L158 and L267–268: BriceHuang2015, "Theorem 2.3"

**Paper (L158):** "Our first result is a criterion, which is Proposition 1.3 of Bresar for the algebra (A,mu),
and Theorem 2.3 of Brice and Huang for an arbitrary bilinear mu over a commutative ring."
**Paper (L267–268):** "The criterion is stated for an arbitrary bilinear mu, over a commutative ring, by
Brice and Huang [Theorem 2.3]; Proposition 1.3 of Bresar ... is the same statement for the product of a
nonassociative algebra, and Corollary 3.4 is that statement applied to (A,mu)."

The Brice–Huang paper is **not** in the folder and is not mentioned in any of the three supplied sources, so
three things cannot be checked here: that its Theorem 2.3 is the criterion Zs_mu = ker mu-bar; that it is
stated over a commutative ring for an arbitrary bilinear mu; and hence that Corollary 3.4 is a restatement
rather than a new result. What *can* be checked and does hold: the criterion is exactly Bresar's Proposition
1.3(iii) applied to (A,mu) (quoted in 2.4 below), so Corollary 3.4 is correct whatever the attribution.
**What a referee must ask for:** the exact wording of Brice–Huang Thm. 2.3.

### F5 — UNVERIFIABLE — L466: AnLiHe2015, "Theorem 2.1"

**Paper (L465–466):** "... and a unital algebra generated by idempotents is zJpd in characteristic other than
2 [Bresar, Theorem 3.15], originally [An–Li–He, Theorem 2.1]."

Verified in the source: Bresar **Theorem 3.15** says exactly this — "Let A be an (associative) unital algebra
over a field F of characteristic not 2. If A is generated by idempotents, then A is zJpd" (PDF p. 55) — and
Bresar attributes it to his reference [24], which is "G. An, J. Li, J. He, Zero Jordan product determined
algebras, Linear Algebra Appl. 475, 90–93" (bibliography, PDF p. 176). So the attribution is corroborated.
The *number* 2.1 and the exact hypotheses of the An–Li–He statement, however, cannot be checked: the paper is
not in the folder.

### F6 — NOTE (cosmetic) — three labels are never referenced

`cor:identity` (L311), `def:bresar-zpd` (L183) and `def:bresar-zpp` (L216) are defined but never referenced.
No mathematical content; a copy-editor would either reference them in the text or drop the labels.

---

## 2. Verified FINE, with the evidence

### 2.1 `def:determined` (L232–236) — FINE
**Paper:** "The algebra A is *determined by* mu if the nonassociative algebra (A,mu) is zpd. By [Bresar,
Proposition 1.3(iv)] this holds if and only if, for every vector space V and every bilinear map
phi: A x A -> V with phi(x,y) = 0 whenever mu(x,y) = 0, there is a linear map psi: A -> V with
phi(x,y) = psi(mu(x,y))."
**Source (Bresar, Def. 1.1, PDF p. 12 / printed 4):** "A nonassociative algebra A over a field F is said to be
zero product determined if, for every bilinear functional phi: A x A -> F satisfying phi(x,y) = 0 whenever
x, y in A are such that xy = 0, there exists a linear functional tau on A such that phi(x,y) = tau(xy) for all
x, y in A." — verbatim in the paper's Definition 2.1 (L183–185).
**Source (Bresar, Prop. 1.3(iv), PDF p. 12):** "For every vector space X over F and every bilinear map
phi: A x A -> X satisfying phi(x,y) = 0 whenever x, y in A are such that xy = 0, there exists a linear map
T: A -> X such that phi(x,y) = T(xy) for all x, y in A." So the "for every vector space V" form quoted in
Definition 3.1 is exactly (iv); the equivalence with zpd is Bresar's.

### 2.2 `rem:preserving` (L241–246) — FINE
With phi(x,y) = T(x)T(y) valued in B, Definition 3.1 gives S with S(mu(x,y)) = T(x)T(y); for mu(x,y) = xy this
is the first part of Bresar Thm. 7.2, whose statement in the paper (Theorem 2.6, L216–224) is verbatim
Bresar's, including "the range of T contains an invertible element of B (in particular, if T is surjective),
then c = T(1) is invertible in B and there exists a homomorphism Phi: A -> B such that
T(x) = c Phi(x) = Phi(x) c" (Bresar, PDF p. 117 / printed 114).

### 2.3 `rem:derivations` (L250–257) — FINE
The bilinear map (x,y) |-> D(x).y + x.D(y) vanishes on the pairs with x.y = 0 by hypothesis, so Definition 3.1
gives S with D(x).y + x.D(y) = S(x.y). Since both sides are linear in (x,y), "D is a braided-symmetric
derivation iff S = D on the span of the products" is exact (one direction is the Leibniz rule, the other is
linearity). Requires sigma an involution — see F1.

### 2.4 `cor:criterion` (L262–273) — FINE
**Source (Bresar, Prop. 1.3(iii), PDF p. 12):** "If z_i, w_i in A are such that sum_i z_i w_i = 0, then the
element sum_i z_i (x) w_i from A (x) A lies in span{x (x) y in A (x) A | xy = 0}." Applied to (A,mu) this is
ker mu-bar contained in Zs_mu, and Zs_mu contained in ker mu-bar always holds, so Zs_mu = ker mu-bar. The
proof in the paper says exactly this. Confirmed on every algebra computed below (each time
Zs_mu contained in ker mu-bar held with equality exactly when determined).

### 2.5 `thm:zpd-fxy` (L279–290) — FINE, including the use of unitality
Proof read line by line: mu(x,y) = f(xy) vanishes on zero products, so Bresar Prop. 1.3(iv) gives psi_0 with
phi = psi_0 o prod; for b in ker f, mu(b,1) = f(b) = 0 gives psi_0(b) = phi(b,1) = 0, so ker f is contained in
ker psi_0 and psi_0 factors through A/ker f = im f; extend to psi on A. The step mu(b,1) = f(b) is where
unitality is used, and the theorem states it (L280).
**Exhaustive test** (`m8-stress-theorems.py`): all 3^4 = 81 linear f on A = F_3 x F_3, all 3^9 = 19683 linear
f on A = T_2(F_3), all 16 linear f on F_2 x F_2 and all 512 on T_2(F_2): A is determined by f(xy) in **every**
case (criterion dim Zs = dim ker). No counterexample exists in these families.

### 2.6 `prop:injective` (L297–307) — FINE
f injective implies mu(x,y) = 0 iff xy = 0; a phi vanishing on zero products vanishes on mu-zero pairs, so
phi = psi o f o prod. Checked against the contrapositive numerically: A = F_3[eps] with
f(a + b eps) = a + 2b eps (injective) is **not** determined by f(xy) (dim ker = 2, dim Zs = 1), and A is not
zpd.

### 2.7 `cor:identity` (L311–317) and the characteristic-2 sentence (L321) — FINE
(i) is Theorem 4.1 with f = 2 id; (ii) is (i) plus Proposition 4.2 for char K != 2. The sentence "In
characteristic 2 the map mu is zero, every phi in Definition 3.1 is zero, and every algebra is determined by
mu" is correct: with mu = 0 the hypothesis of Definition 3.1 forces phi(x,y) = 0 for **all** pairs, hence
psi = 0; confirmed numerically on F_2 x F_2 (dim ker = dim Zs = 4).

### 2.8 The Jordan-product paragraph (L323–330) — FINE, both "indeed"
"If x = 1 forces f = 2 id": setting x = 1 in xy + yx = f(xy) gives f(y) = y + y = 2y. If char K != 2,
xy + yx = 2xy gives yx = xy; if char K = 2 then f = 0, so xy + yx = 0 for all x, y, which fails for a
noncommutative A. Both halves are correct, and unitality is available (standing hypothesis, L231). The
citation of Bresar §3.3 ("zJpd Algebras", PDF p. 56) is right.

### 2.9 `cor:twisted` (L335–340) and `cor:anti` (L346–351) — FINE
Proofs: alpha endomorphism on a commutative A gives alpha(y)alpha(x) = alpha(yx) = alpha(xy); alpha
anti-multiplicative gives alpha(y)alpha(x) = alpha(xy); in both cases mu_alpha = (id + alpha)(xy) and Theorem
4.1 applies. Note neither corollary needs alpha injective or involutive, and neither assumes it — correct as
stated.
**Numerical checks** (`m8-cor-twisted-anti.py`, `m8-stress-theorems.py`): F_3 x F_3 with alpha the swap;
T_2(F_3) with the anti-automorphism E_11 <-> E_22, E_12 |-> E_12; M_2(F_3) with the transpose; and the
**non-injective** endomorphism alpha(x,y) = (x,x) of F_3 x F_3. Determined in every case (e.g. T_2: dim ker =
7 = dim Zs; M_2 with the transpose: 13 = 13).

### 2.10 `cor:triangular` (L372–381) — FINE
A = Tri(A_1,M,A_2) is zpd by Corollary 4.6(b) and unital (unit with diagonal entries the units of A_1, A_2),
so Theorem 4.1 applies for **every** linear f; the last claim is Corollary 4.5.
**Check:** Tri(F_2 x F_2, F_2, F_2) is zpd (dim ker = dim Zs = 12) and is determined by f(xy) for 200 random
linear f in characteristic 2 — no failure.

### 2.11 `thm:codim` (L393–410) — FINE
Proof checked step by step: n in N implies ny, xn in N, so phi(n,y) = phi(x,n) = 0; the splitting
x = (x - c(x)1) + c(x)1 gives phi(x,y) = c(x)c(y)phi(1,1) and f(xy) = c(x)c(y)f(1); f(1) != 0 makes
a |-> a f(1) injective on K, so it has a left inverse g, and psi(z) = g(z)phi(1,1) satisfies
psi(f(xy)) = c(x)c(y)phi(1,1) = phi(x,y). (Note c(1) = 1 follows from 1 - c(1)1 in N and f(1) != 0.) The
"in words" restatement at L412 is accurate.
**Checks on non-zpd algebras** (`m8-stress-theorems.py`): the dual numbers (2.12); A = F_3 + V with V^2 = 0,
dim V = 2 — here dim ker = 6 > dim Zs = 4, so A is **not** zpd, yet dim ker = dim Zs = 8 for
mu(x,y) = f(xy), f the projection onto the scalar summand; and F_3[x]/(x^3), f = constant term (not zpd:
6 > 3; determined: 8 = 8), also over F_2 (8 = 8).

### 2.12 `ex:dual` (L421–434) — FINE
Every step holds: alpha(a + b eps) = a - b eps is an involutive automorphism; A commutative gives
mu_alpha = (id + alpha)(xy) with (id + alpha)(a + b eps) = 2a, so N = K eps is an ideal, f(1) = 2 != 0,
c(a + b eps) = a; Theorem 5.1 gives determination; the idempotents of K[eps] are 0, 1 (from a^2 = a,
2ab = b), so A is not generated by idempotents and Theorem 5.2 gives "not zpd". **Numbers**
(`m8-f3-twisted.py`, over F_3 and F_5): mu_alpha: dim ker = 3 = dim Zs (**determined**); ordinary product:
dim Zs = 1 < 2 = dim ker (**not zpd**). The example is sound.

### 2.13 `prop:matrix` (L436–449) and the "12 = 12", "13 = 13" remark (L450–451) — FINE, all numbers exact
Recomputed in exact F_3 arithmetic (`m8-f3-twisted.py`), A = M_2(F_3), alpha conjugation by diag(1,-1),
mu_alpha(x,y) = xy + alpha(yx):
* matrix of mu-bar_alpha in the matrix-unit basis: **rank 4**, so dim ker mu-bar_alpha = 16 - 4 = 12;
* among the 81 * 81 = 6561 pairs (x,y) **exactly 417** satisfy mu_alpha(x,y) = 0;
* the 417 tensors x (x) y span a subspace of dimension **12**; hence Zs = ker and A is determined.
* ordinary product: rank 4, dim ker = 12, 417 zero pairs, dim Zs = 12 — "12 = 12";
* transpose twist xy + y^T x^T: rank 3, dim ker = 13, 513 zero pairs, dim Zs = 13 — "13 = 13".
So the four numbers of the proof and both numbers of the remark are correct, and since the criterion is an
*equivalence*, the computation does establish determination (see §4, R3).

### 2.14 `q:noncomm` (L472–475) — FINE in the audited snapshot
Every clause checked: for inner alpha, `rem:inner`'s identity mu_alpha(x,y) = (xD^{-1}) o (Dy) and
mu-bar_alpha = circ-bar o Phi with Phi a linear automorphism carrying pure tensors to pure tensors give
Zs_{mu_alpha} = Phi^{-1}(Zs_circ) and ker mu-bar_alpha = Phi^{-1}(ker circ-bar), hence determination by
mu_alpha iff determination by the Jordan product = zJpd. M_n(B) and Tri(A_1,M,A_2) are zJpd in characteristic
!= 2: Bresar **Corollary 3.17** states exactly this ("(a) The algebra M_n(B), where n >= 2 and B is any unital
algebra. (b) The algebra Tri(A_1,M,A_2), ...", PDF p. 55). The real quaternions with alpha = id are not zJpd:
Bresar **Example 3.19** (PDF pp. 61–62) proves it with the functional phi((a,x),(b,y)) = ab, and the paper's
citation is exact. Skolem–Noether ("every automorphism of M_n(K), n >= 2, K a field, is inner") is standard,
and inner alpha is completely settled by `rem:inner`, so the closing sentence is correct.

### 2.15 Abstract (L101–112) and Introduction (L115–174) — FINE, every claim maps to a result
"The answer is a criterion ..." -> Cor. 3.4; "For the symmetrized products of three braidings on a commutative
algebra ... mu has the form f(xy)" -> Cor. 4.4 (and Cor. 4.3 for identity/swap); "The same holds on any
algebra when the twist reverses products" -> Cor. 4.5; "Every unital zpd algebra is determined by every such
mu" -> Thm. 4.1; "The converse holds when f is injective" -> Prop. 4.2; "identity braiding gives nothing new
in characteristic other than 2" -> Cor. 4.3(ii); "The converse fails for the twisted braiding, because the
dual numbers ..." -> Ex. 5.3; "A computation over F_3 ..." -> Prop. 5.4. The Introduction's Preface and §7.1
claims match Bresar's Preface ("many properties of A are determined by pairs of elements whose product is
zero"; "The concept of a zpd algebra arose from two unrelated papers ... commutativity preserving linear
maps ... local derivations", PDF p. 6) and §7.1 ("Banach ... His work was later completed by Lamperti", PDF
p. 117). Output of the check: **no unsupported abstract/Introduction claim**, apart from the scope point F1.

### 2.16 The source recalls used by these items — FINE
* Bresar Def. 1.1 — PDF p. 12 (printed 4), verbatim = paper Def. 2.1.
* Bresar Prop. 1.3, all four conditions — PDF pp. 12–14 (printed 4–6), verbatim = paper Prop. 2.3.
* Bresar Def. 3.14 — PDF p. 56 (printed 48), verbatim = paper Def. 2.2.
* Bresar Cor. 2.17 — PDF p. 33 (printed 25), verbatim = paper Cor. 4.6, hypotheses included.
* Bresar Ex. 2.19, Ex. 2.23 — PDF p. 33 and p. 34 (printed 25, 26).
* Bresar Thm. 2.27 — PDF p. 38 (printed 30), verbatim = paper Thm. 5.2.
* Bresar Ex. 1.10 — PDF pp. 16–17 (printed 8–9): "Let us show that the answer is positive if A is a unital
  zpd associative algebra."
* Bresar Def. 7.1, Thm. 7.2 — PDF pp. 116–117 (printed 113–114), verbatim including the "Moreover" clause.
* Bresar Thm. 3.15, Cor. 3.17 — PDF p. 55 (printed 47); Ex. 3.19 — PDF pp. 61–62 (printed 53–54).
  Bresar §7.3 "Jordan Homomorphisms" — PDF pp. 129–130 (printed 126–127), which says "Jordan homomorphisms
  appear naturally in the study of linear maps preserving zero products or commutativity" (the paper's
  Introduction sentence).
* Adrabi Def. 3.1 — PDF p. 5, verbatim = paper Def. 2.4; Rem. 3.4 — PDF p. 6; §1 ("sigma^2 = id",
  x . y = mu(x (x) y) + mu(sigma(x (x) y))) — PDF pp. 2–3; §4 (sigma_alpha(x (x) y) = alpha(y) (x) alpha(x),
  x . y = xy + alpha(y)alpha(x), alpha involutive) — PDF p. 10. So the paper's claim "we do not require
  sigma^2 = id, which differs from [Adrabi, Definition 3.1]" is **correct**.
* Horn & Johnson §0.2.5 — "0.2.5 The transpose, conjugate transpose, and trace" (PDF p. 26, printed 6); the
  reverse-order law (AB)^T = B^T A^T is on PDF p. 27 (printed 7). The locator and the claim are correct.

---

## 3. Internal consistency (Task C, the part in my scope)

* **Cross-references.** 27 labels, 55 references: every reference resolves; no duplicate label; two pdflatex
  passes produce **no** "undefined reference" and **no** "multiply defined" warning. The .aux numbering is
  2.1–2.6, 3.1–3.4, 4.1–4.7, 5.1–5.6, all distinct.
* **Prose numbers.** "Definition 3.1" = `def:determined` (L232), "Remark 3.3" = `rem:derivations` (L250),
  "Corollary 3.4" = `cor:criterion` (L262), "Theorem 4.1" = `thm:zpd-fxy` (L279), "Proposition 4.2" =
  `prop:injective` (L297), "Corollary 4.3" = `cor:identity` (L311), "Corollary 4.4" = `cor:twisted` (L335),
  "Corollary 4.5" = `cor:anti` (L346), "Corollary 4.6" = `cor:bresar-matrix` (L360), "Corollary 4.7" =
  `cor:triangular`, "Theorem 5.1" = `thm:codim` (L393), "Theorem 5.2" = `thm:bresar-idempotents`,
  "Example 5.3" = `ex:dual` (L421), "Proposition 5.4" = `prop:matrix` (L436), "Remark 5.5" = `rem:inner`
  (L452), "Question 5.6" = `q:noncomm` (L472). All correct.
* **Source locators in prose** (Bresar 1.1, 1.3, 2.17, 2.19, 2.23, 2.27, 3.14, 3.15, 3.17, 3.19, 7.1, 7.2,
  §1.1, §2.1, §3.3, §7.1, §7.3; Adrabi 3.1, 3.4, §1, §4; H&J §0.2.5): all exist and say what the paper
  says, except the two unverifiable items F4, F5.
* **Markup.** "12 = 12" and "13 = 13" (L450) are correct numerically (2.13); "f(xy)" in the section title and
  in the abstract matches Theorem 4.1; the bibliography keys all match their bibitems and all five are cited.

---

## 4. Defects repaired while this audit ran — the repairs verified correct

These were present in the snapshot at the start of my run and are absent from the audited one; I record them
because the report should say whether the fix is right.

* **R1 `rem:inner` (was L448):** "... M_n(B) is generated by the idempotents (e_ii + b e_ij) - e_ii for i != j
  ...". Those elements are b e_ij, which are **not** idempotents. The snapshot now reads "for a unital algebra
  B and n >= 2 ... generated by the idempotents e_ii and e_ii + b e_ij ... (indeed b e_ij = (e_ii + b e_ij) -
  e_ii and b e_ii = (b e_ij)e_ji)". **Verified:** for B = M_2(F_3) and n = 2 (so M_2(B) = M_4(F_3)),
  e_ii + b e_ij is idempotent for every b in a basis of B, b e_ij is not, and the algebra generated by these
  idempotents has dimension 16 = dim M_2(B).
* **R2 `q:noncomm` (was L458):** "the answer is affirmative ... whenever alpha is inner". **False:** take
  A = M_2(K) x K[eps] (noncommutative, unital, char K != 2) and alpha = id, which is inner and involutive;
  then mu_alpha is the Jordan product. Computed over F_3 and F_5 (`m8-q-noncomm-jordan.py`): dim ker = 30 >
  29 = dim Zs, so A is not determined by the Jordan product. (Theoretically: if B x C were zJpd then B would
  be zJpd, by restricting a separating functional; K[eps] is not, dim Zs = 1 < 2 = dim ker.) The snapshot's
  rewritten question is correct (2.14).
* **R3 `rem:inner` (was L468–469):** "what that computation establishes is that mu_alpha has no form f(xy),
  not the determination itself". The computation (rank 4, hence dim ker = 12; 417 zero pairs spanning 12)
  **does** establish determination, because Corollary 3.4 is an equivalence and Zs is contained in ker always.
  The snapshot now says the computation "checks the criterion of Corollary 3.4 directly in a small case",
  which is correct.
* **R4 locators:** the Tri(A_1,M,A_2) locator is now §2.1 (Bresar defines it in §2.1, PDF p. 27 / printed 19,
  not in §2.2, where Cor. 2.17 sits); the Adrabi §4 sentence now says Adrabi takes alpha involutive; "every
  automorphism of a matrix algebra is inner" now names M_n(K) over a field. All three corrections are right.

---

## 5. Summary table

| locator | verdict | one-line repair |
|---|---|---|
| L104, L154 (abstract, Introduction) | IMPRECISE | say "for an involution sigma" before "the braided-symmetric derivations" |
| L141 (Introduction) | IMPRECISE | soften "decide which algebras are determined by which mu" |
| L327 (§4) | IMPRECISE (markup) | write x circ ((1/2) 1) = x |
| L158, L267–268 (BriceHuang2015 Thm 2.3) | UNVERIFIABLE | obtain the paper; quote its Thm 2.3 before crediting the criterion |
| L466 (AnLiHe2015 Thm 2.1) | UNVERIFIABLE | attribution corroborated by Bresar [24]; verify number/hypotheses |
| L311, L183, L216 | NOTE | unused labels cor:identity, def:bresar-zpd, def:bresar-zpp |
| L232–236 `def:determined` | FINE | — (Bresar Def. 1.1 + Prop. 1.3(iv), PDF p. 12) |
| L241–246 `rem:preserving` | FINE | — |
| L250–257 `rem:derivations` | FINE | — (the definition needs an involution: see L104) |
| L262–273 `cor:criterion` | FINE | — (Bresar Prop. 1.3(iii), PDF p. 12) |
| L279–290 `thm:zpd-fxy` | FINE | — (all 81/19683/16/512 linear f tested, no failure) |
| L297–307 `prop:injective` | FINE | — |
| L311–321 `cor:identity` | FINE | — (char 2 case verified) |
| L323–330 Jordan paragraph | FINE | — (both "indeed" verified) |
| L335–340 `cor:twisted` | FINE | — |
| L346–351 `cor:anti` | FINE | — |
| L372–381 `cor:triangular` | FINE | — (200 random f in char 2: no failure) |
| L393–410 `thm:codim` | FINE | — (F_3 + V, F_3[x]/(x^3), F_2[x]/(x^3)) |
| L421–434 `ex:dual` | FINE | — (determined 3 = 3, not zpd 1 < 2, over F_3, F_5) |
| L436–449 `prop:matrix` | FINE | — (rank 4, dim ker 12, 417 pairs, dim Zs 12) |
| L450–451 remark | FINE | — (12 = 12, 13 = 13 confirmed) |
| L452–470 `rem:inner` | FINE in snapshot | — (R1, R3 repaired and verified) |
| L472–475 `q:noncomm` | FINE in snapshot | — (R2 repaired and verified; Bresar Cor. 3.17, Ex. 3.19) |
| L101–112 abstract | FINE except L104 | see L104 |
| L115–174 Introduction | FINE except L141 | see L141 |
| cross-references, numbering | FINE | 27 labels / 55 refs all resolve; no duplicates |

**Categories with nothing to report.** No wrong theorem number, no non-existent section, no result attributed
to the wrong source was found among the items verifiable from the three supplied sources; no false statement
survived the stress tests; no duplicated numbering and no unresolved reference exist in the snapshot.

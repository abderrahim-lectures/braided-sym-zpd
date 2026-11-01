# Audit report — the σ-/α-twisted product, cor:twisted, cor:anti
(member m1, swarm smvxd25ff, direction d7)

**Scope.** The paper's own twisted-product formalism and the two transport corollaries built on
it: `cor:twisted`, `cor:anti` (and `cor:triangular`, which is their application), the twisted-swap
sentences of the abstract and Introduction, the well-definedness/associativity of
`x ·_σ y = m(x⊗y + σ(x⊗y))`, and the F₃ numerics of `prop:matrix`, which I recomputed as a
cross-check. Brešar locators are d1's, Adrabi/Horn–Johnson locators are d3's, §4/JT is d2's.

**Version audited.** `paper/braided-sym-zpd.tex`, md5 `46a95204a40579ac10cf21ae06b54599`,
495 lines. *(The file was revised five times while I audited it — by the author's review pipeline,
not by me; I did not modify it. Line numbers are those of the md5 above; findings that an earlier
snapshot carried are marked with that snapshot's md5, and the fact that they were repaired
under me is itself the evidence that they were real.)*

Snapshots seen: (i) 480-line version, standing hypothesis "Throughout, A is a unital …" with no
section scope; (ii) `6f667038…`, 496 lines — standing hypothesis scoped to §§3–5, `rem:inner`'s last
clause inverted; (iii) `6578350f…` — that clause repaired; (iv) `e9d9255b…`, 495 lines — l.149 now
says that Adrabi takes α involutive; (v) `46a95204…` — l.104 and l.153 now say "for an involution
σ", which closes F1 below.

**Method.** Each statement proved or disproved by hand; every finite algebraic claim additionally
decided by machine over F_p. Scripts (all with self-tests whose answers are known independently:
dual numbers must come out "determined, not zpd"; α = id must give the Jordan product; α = 0 must
give the product):

* `results/audit-scripts/m1-twisted-corollaries.py` — exhaustive search over *all* commutative
  algebras of dimension ≤ 3 over F₂ and ≤ 2 over F₃, their zpd property, their non-unitality, all
  their endomorphisms α, and determination by μ_α.
* `results/audit-scripts/m1-twisted-checks.py` — C1–C5 below (K×K parenthetical, σ², associativity,
  "no form f(xy)", sharpness of `thm:zpd-fxy`).
* `results/audit-scripts/m1-matrix-numerics.py` — the F₃ numbers of `prop:matrix` and l.450.
* `results/audit-scripts/m1-smallest-case.py` — F2 below (M₂(F₂)).

Conventions: `T[i,j,k]` = coefficient of `e_k` in `e_i e_j`; `C[i,l]` = coefficient of `e_l` in
α(e_i); `μ_α(x,y) = xy + α(y)α(x)`, which is what the paper's twisted swap gives (l.145, l.150),
and `Zs_μ = span{x⊗y : μ(x,y) = 0}`, `μ̄` the linearisation.

---

## F1. Abstract l.104 / Introduction l.153: the derivation payoff and non-involutive σ — FINE in the live snapshot; IMPRECISE (now repaired) up to snapshot (iv)

*Live text, l.104 (abstract):* "For the symmetrized products $\mu_\sigma$, this asks when the algebra
with that product is zero product determined, **and hence, for an involution $\sigma$, when the
braided-symmetric derivations of that product can be studied through zero products**"; l.153: "So an
algebra determined by $\mu_\sigma$, **for an involution $\sigma$**, is one whose braided-symmetric
derivations can be studied through zero products". This is exactly the qualification the mathematics
requires, so the item is now correct.
*Text up to snapshot (iv)* (the version on which the finding was made): the same two sentences
without the words "for an involution $\sigma$" — "**and hence when the braided-symmetric
derivations of that product can be studied through zero products**" (l.104) and "So an algebra
determined by $\mu_\sigma$ is one whose braided-symmetric derivations can be studied …" (l.153).

*Paper, l.149 (added during this audit):* "… the twisted swap … which twists the swap [Adrabi §4];
\citet{Adrabi2026} takes $\alpha$ involutive, and we do not."

*Paper, l.209 (`def:adrabi-bsder`):* "let $\sigma$ be a $K$-linear **involution** of $A\otimes A$";
l.251 (`rem:derivations`): "Let $\sigma$ be an **involution** of $A\otimes A$".

*Source, Adrabi 2026, PDF p.5:* "Definition 3.1. Let A be a K-algebra and let σ be a K-linear
involution of A ⊗ A." Same page: "Let σ : A ⊗ A → A ⊗ A be a K-linear map with σ² = id."
*Source, Adrabi 2026, PDF p.10:* "x ⊗ y ↦ α²(x) ⊗ α²(y), so σα is an involution of A ⊗ A exactly
when α is involutive."

*My computation* (`m1-twisted-checks.py`, C2): σ(x⊗y) = α(y)⊗α(x) gives
σ²(x⊗y) = α²(x)⊗α²(y), i.e. **σ² = id ⟺ α² = id** (`True` for α² = id, `False` for random α² ≠ id).

So in snapshots (i)–(iv) the two halves of the paper did not meet: `cor:twisted` (l.334) allows an
arbitrary endomorphism α, for which σ_α is not an involution, so *no* braided-symmetric derivation
is defined for it by the paper's own `def:adrabi-bsder`, while the abstract and l.153 then promised
the derivation payoff for the symmetrized products in general. (In the live snapshot both sentences
carry "for an involution σ".)

**Verdict:** IMPRECISE in snapshots (i)–(iv); FINE in the live snapshot (v). **Repair applied**
during this audit: "for an involution σ" in both places — which, for the twisted swap, is exactly
α² = id.

**Status:** d3 (m3) put the same point on the board as d3/f6. I confirm it independently (the
σ² = α²⊗α² computation is mine) and record that the repair landed while this report was being
written.

---

## F2. l.433 "The next proposition uses it on the smallest case" — IMPRECISE

*Paper, l.433:* "The next proposition uses it on the smallest case." — with `prop:matrix` (l.435)
being $A = M_2(\mathbb{F}_3)$ and α = conjugation by diag(1,−1).

*My computation* (`m1-smallest-case.py`): $A = M_2(\mathbb{F}_2)$ (8 elements, against 81) with
$D=\begin{psmallmatrix}1&1\\0&1\end{psmallmatrix}$ (D² = 1, det D = 1) gives an **involutive** inner
automorphism α, and for μ_α(x,y) = xy + α(y)α(x):

| case | dim ker μ̄_α | dim Zs_{μ_α} | determined? | rank m̄ | rank [m̄; μ̄_α] |
|---|---|---|---|---|---|
| M₂(F₂), D = [[1,1],[0,1]] (α² = id) | 13 | 13 | yes | 4 | 7 |
| M₂(F₂), D = [[0,1],[1,1]] (order 3, α² ≠ id) | 13 | 13 | yes | 4 | 7 |

So the phenomenon of `prop:matrix` (determined, and μ_α of no form f(xy)) already occurs on the
smaller algebra M₂(F₂) with a *different* α; what is special about M₂(F₃) is only that
diag(1,−1) ≠ diag(1,1) there — in characteristic 2 the paper's α degenerates to the identity.

**Verdict:** IMPRECISE. **Repair:** "The next proposition uses it on a small case" — or "on the
smallest case in which α is diagonal, namely A = M₂(F₃) with α = conjugation by diag(1,−1)".

---

## F3. `cor:twisted` (l.334–341): statement and proof — FINE

*Paper, l.334–338:* "Let $A$ be commutative and zpd, and let $\alpha$ be an algebra endomorphism of
$A$. Then $A$ is determined by $\mu_\alpha(x,y) = xy + \alpha(y)\alpha(x)$."
*Proof, l.340:* "Apply Theorem~\ref{thm:zpd-fxy} with $f = \mathrm{id} + \alpha$."

The preliminary computation at l.333 is correct: α(y)α(x) = α(yx) (α multiplicative) = α(xy)
(A commutative), so μ_α = (id+α)(xy) with id+α linear — this is exactly the shape `thm:zpd-fxy`
(l.279: "Let $A$ be a **unital** zpd algebra, let $f$ linear, and let $\mu(x,y)=f(xy)$. Then $A$ is
determined by $\mu$") needs. The unit is used once in that theorem's proof ("Then $\mu(b,1)=f(b)=0$",
l.289) and is supplied by the standing hypothesis, **l.230**: "Throughout Sections 3 to 5, $A$ is a
unital associative algebra over a field $K$". So the proof is complete — *in this snapshot*.

Two verifications beyond the proof:

1. **The statement is true even without unitality** (so nothing is lost if the standing hypothesis
   is ever weakened). Exhaustive check (`m1-twisted-corollaries.py`): every commutative algebra of
   dimension ≤ 3 over F₂ (40 zpd, of which 37 non-unital; 59 704 zpd, 59 536 non-unital in
   dimension 3) and ≤ 2 over F₃ (393 zpd, 369 non-unital), with **every** endomorphism α and every
   one of them tested by the criterion: **0 counterexamples** to `cor:twisted`.
2. **The unital hypothesis of `thm:zpd-fxy` is not redundant**, so l.230 is doing real work here.
   Counterexample found (`m1-twisted-checks.py`, C5): over F₂ in dimension 3, A zpd and non-unital,
   table $e_0^2=e_1+e_2$, $e_0e_1=e_0$, $e_1^2=e_1$, $e_2^2=e_0$, all other products 0, with
   f given by $f(e_0)=0,\ f(e_1)=e_2,\ f(e_2)=e_1+e_2$: then $\dim\ker \overline{f\circ m} = 7$
   but $\dim Zs = 6$, so A is **not** determined by f(xy).

*Historical note:* in the first snapshot the standing hypothesis read "Throughout, $A$ is a unital
…" with no section scope, so `cor:twisted`'s proof then invoked a hypothesis its statement did not
carry. That is now repaired by l.230; the repair is what makes this item FINE.

**Verdict:** FINE. **Optional repair (presentational):** make the two neighbouring corollaries read
alike — either put "unital" into l.335 as well, or drop it from `cor:anti` (l.346), since l.230
already supplies it.

---

## F4. `cor:anti` (l.345–353) and its application to the transpose — FINE

*Paper, l.345–347:* "Let $A$ be a unital zpd algebra, and let $\alpha \colon A \to A$ be linear with
$\alpha(xy) = \alpha(y)\alpha(x)$ for all $x, y$. Then $A$ is determined by
$\mu_\alpha(x,y) = xy + \alpha(y)\alpha(x)$."
*Proof, l.351–352:* "Here $\alpha(y)\alpha(x) = \alpha(xy)$, so $\mu_\alpha(x,y) =
(\mathrm{id} + \alpha)(xy)$. Apply Theorem~\ref{thm:zpd-fxy} with $f = \mathrm{id} + \alpha$."

Every hypothesis of the cited theorem is discharged (unital zpd: statement; f = id+α linear:
α linear), and nothing else is used: α need not be unital (α(1) = 1 is nowhere used), injective,
surjective, or involutive. The added "unital" is exactly the hypothesis `thm:zpd-fxy` needs, so the
fix is sufficient as well as necessary-in-form.

The application at l.365–367 is correct: $M_n(K)$ is unital and zpd by `cor:bresar-matrix`(a)
(l.365), the transpose is anti-multiplicative, and for α = transpose
$\mu_\alpha(x,y) = xy + y^{\mathsf T}x^{\mathsf T} = xy + (xy)^{\mathsf T}$ — which is the product
used in the l.450 sentence, whose numbers I confirm below (F8).

**Verdict:** FINE, no repair.

---

## F5. `cor:triangular` (l.371–380), the main application of `cor:anti` — FINE

*Paper, l.371–374, 377–379.* "Let $A = \mathrm{Tri}(A_1, M, A_2)$ be as in Corollary 2.17(b) … and
let $f \colon A \to A$ be linear. Then $A$ is determined by $\mu(x,y) = f(xy)$. In particular $A$ is
determined by $xy + \alpha(y)\alpha(x)$ for every linear $\alpha$ … Proof: By Corollary 2.17(b), $A$
is zpd, and $A$ has the unit with diagonal entries the units of $A_1$ and $A_2$. Apply Theorem
`thm:zpd-fxy`, and then Corollary `cor:anti` for the last claim."

Checked: for unital $A_1, A_2$ and a **unital** bimodule $M$ ($1m = m = m1$), the matrix
$\mathrm{diag}(1,1)$ is a two-sided unit of $\mathrm{Tri}(A_1,M,A_2)$ — this is exactly where the
word "unital" on the bimodule is needed; the algebra is associative; so both `thm:zpd-fxy` and
`cor:anti` apply. Both claims follow.

**Verdict:** FINE, no repair.

---

## F6. l.164 (and l.331): "commutativity alone is not enough" — FINE, verified exactly

*Paper, l.164:* "… (commutativity alone is not enough: on K × K, a zpd algebra, with the linear
α(x,y) = (x+y,0), the pairs (e₂, e₂) and (e₂, 1) have the same product e₂ but μ = 1 and
μ = e₂ + 2e₁)"; l.331 carries the short form of the same claim.

*My computation* (`m1-twisted-checks.py`, C1), with e₁ = (1,0), e₂ = (0,1), α(x,y) = (x+y,0)
(i.e. α(e₁) = e₁, α(e₂) = e₁), over F₂, F₃, F₅ and by hand for an arbitrary field: α is **not**
multiplicative; e₂·e₂ = e₂ = e₂·1; μ(e₂,e₂) = e₂ + e₁·e₁ = e₂ + e₁ = 1, and
μ(e₂,1) = e₂ + α(1)α(e₂) = e₂ + (2e₁)(e₁) = e₂ + 2e₁ (in characteristic 2, α(1) = 0 and
μ(e₂,1) = e₂). The two values differ in every characteristic (1 ≠ e₂ + 2e₁ because their
difference is 2e₁ ≠ 0; in characteristic 2, 1 ≠ e₂). So the parenthetical is correct.

Extra observation (not claimed by the paper, useful if the hypothesis is ever questioned): over F₂
this A is **not** determined by μ_α (dim Zs = 1 < 2 = dim ker μ̄_α), while over F₃ and F₅ it is
(2 = 2). So the endomorphism hypothesis of `cor:twisted` is not removable in general over F₂, even
though F3 above shows the statement holds without unitality.

**Verdict:** FINE, no repair.

---

## F7. The twisted product is not associative — FINE (documented; the paper never assumes it is)

For α = conjugation by diag(1,−1) on $M_2(\mathbb{F}_3)$ and $x\cdot y := xy + \alpha(y)\alpha(x)$,
`m1-twisted-checks.py` (C3) produces the explicit failure
$x = e_{11}+e_{12}+2e_{21}+2e_{22}$, $y = 2e_{21}+2e_{22}$, $z = 2e_{21}+e_{22}$:
$(x\cdot y)\cdot z = e_{11}+2e_{12}$ but $x\cdot(y\cdot z) = 2e_{11}+e_{12}$.

This is **not** a defect: the paper's whole framework is non-associative —
`def:bresar-zpd` (l.183) quantifies over "nonassociative algebras", `def:determined` (l.233)
defines determination of "the nonassociative algebra $(A,\mu)$", and `cor:criterion` is applied to
it. No proof multiplies three elements with μ. Adrabi's §2 example likewise records "So ·σα is not
associative" (PDF p.6), so the paper's generalisation is in line with the source.

**Verdict:** FINE, no repair.

---

## F8. `prop:matrix` and the l.450 sentence: every number recomputed — FINE

Independent computation over F₃ (`m1-matrix-numerics.py`), independent of the paper's:

| product on M₂(F₃) | rank μ̄ | dim ker | zero pairs | dim span of zero tensors |
|---|---|---|---|---|
| twisted, α = conj diag(1,−1) (l.443–446) | 4 | **12** | **417** | **12** |
| ordinary product (l.450) | 4 | **12** | 417 | **12** |
| transpose twist, μ = xy + (xy)^T (l.450) | 3 | **13** | 513 | **13** |

All four numbers of `prop:matrix` (rank 4, ker 12, 417, span 12) and both numbers of the sentence
after it ("dim Zs = dim ker = 12", "dim Zs = dim ker = 13") are correct. Also confirmed:
μ_α is **not** of the form f(xy), in the exact linear-algebra sense — rank m̄ = 4 but
rank [m̄; μ̄_α] = 7, i.e. ker m̄ ⊄ ker μ̄_α; equivalently the y = 1 argument at l.431.

**Verdict:** FINE, no repair.

---

## F9. `rem:inner` (l.451–469) — FINE as it now stands; it was an **ERROR** in snapshot `6f667038…`

l.456's identity, the transport $\bar\mu_\alpha = \bar\circ\circ\,\Phi$ with
$\Phi(x\otimes y) = xD^{-1}\otimes Dy$ (l.458–459), $\ker\bar\mu_\alpha = \Phi^{-1}(\ker\bar\circ)$
and $Zs_{\mu_\alpha} = \Phi^{-1}(Zs_\circ)$ (l.459–460) are all correct, and so is the idempotent
generation at l.463–465: $e_{ii}$ and $e_{ii}+be_{ij}$ ($i\neq j$) are idempotents
($(e_{ii}+be_{ij})^2 = e_{ii}+be_{ij}$ since $e_{ij}e_{ii} = e_{ij}^2 = 0$), $be_{ij}$ is their
difference, and $be_{ii} = (be_{ij})e_{ji}$, so they generate $M_n(B)$.

In snapshot `6f667038…` the last clause read: "what that computation establishes is that
$\mu_\alpha$ has no form $f(xy)$, **not the determination itself**." That is inverted: the
computation of `prop:matrix` (417 tensors spanning 12 = dim ker μ̄_α) is exactly the
**determination**; the absence of a form f(xy) is not established by the computation at all but by
the y = 1 argument at l.431 (or by rank [m̄; μ̄_α] = 7 > 4 = rank m̄, F8 above). The current l.468–469
("its computation checks the criterion of Corollary~\ref{cor:criterion} directly in a small case,
and μ_α has no form f(xy) by the argument above") is correct.

**Verdict:** FINE (ERROR in `6f667038…`, repaired). No further repair.

---

## F10. l.384–385, the "no converse" sentence — FINE

"When α is an involution and char K ≠ 2, the map id+α is twice the projection onto the fixed points
of α. It is injective only for α = id, where the converse is Corollary `cor:identity`(ii), so for
α ≠ id Proposition `prop:injective` gives no converse."

Checked: for an involution α with 2 invertible, (id+α)/2 is the projection onto
$\ker(\mathrm{id}-\alpha)$, and $\ker(\mathrm{id}+\alpha) = \{x : \alpha(x) = -x\}$; since the
minimal polynomial of α divides $(t-1)(t+1)$ with distinct roots in char ≠ 2,
$A = A_+\oplus A_-$, so id+α is injective iff $A_- = 0$ iff α = id. For α = id, f = 2id and the
converse is `cor:identity`(ii). Correct.

**Verdict:** FINE, no repair.

---

## F11. What cannot be checked from the material supplied

The reference folder contains only Brešar 2021, Adrabi 2026 and Horn–Johnson. The paper's
Introduction l.158 also attributes the criterion, "for an arbitrary bilinear μ over a commutative
ring", to **Brice–Huang 2015, Theorem 2.3** — that paper is **not** in the folder, so neither the
locator nor the "over a commutative ring" part can be verified here (Brešar's Prop 1.3, which is in
the folder, is over a field). Likewise **An–Li–He 2015, Theorem 2.1** (l.466) is absent; d3 proposed
the verifiable substitute (Brešar Thm 3.15 / Cor 3.17). I flag these as unverifiable rather than
guess.

---

## Summary

| locator | verdict | one-line repair |
|---|---|---|
| abstract l.104 + l.153 (derivation payoff) | FINE now; IMPRECISE up to snapshot (iv) | applied during the audit: "for an involution σ" (for the twisted swap = α² = id) |
| l.433 "on the smallest case" | IMPRECISE | "on a small case", or name the restriction (diag(1,−1) is trivial in char 2; M₂(F₂) with an order-2 inner α already does it) |
| `cor:twisted` l.334–341 | FINE | none; optional: state "unital" here too, or drop it from l.346 |
| `cor:anti` l.345–353 | FINE | none |
| `cor:triangular` l.371–380 | FINE | none |
| l.164 / l.331 (K×K parenthetical) | FINE | none (μ(e₂,e₂)=1, μ(e₂,1)=e₂+2e₁ verified over F₂,F₃,F₅ and in general) |
| twisted product not associative | FINE | none — framework is non-associative throughout; explicit triple recorded |
| `prop:matrix` l.442–447 + l.450 | FINE | none (rank 4, ker 12, 417 pairs, span 12; 12 and 13 confirmed) |
| `rem:inner` l.451–469 | FINE | none now; its last clause was **ERROR** in snapshot `6f667038…` (roles of computation and of the y=1 argument interchanged) and is repaired |
| l.384–385 (injectivity of id+α) | FINE | none |
| Brice–Huang 2015 Thm 2.3; An–Li–He 2015 Thm 2.1 | unverifiable | papers absent from the folder; state the unverifiability, substitute Brešar 3.15/3.17 where possible |

**Categories with no finding.** I found **no** error in the twisted-product formalism itself: the
twisted swap is well defined for every linear α (it is $(\alpha\otimes\alpha)\circ\tau$), it is an
involution exactly when α² = id, the twisted product need not be associative and nothing in the
paper assumes it is, and `cor:twisted`, `cor:anti`, `cor:triangular` are all true with proofs that
close. No counterexample to `cor:twisted` or `cor:anti` exists in the small models searched
(59 536 + 369 non-unital commutative zpd algebras, all endomorphisms).

---

## Appendix: bugs in my own harness (recorded so the numbers can be trusted)

The first version of the search script had three defects, all found by the self-tests and fixed
before the numbers above were produced: (i) the kernel of $\bar\mu$ was computed from
`reshape(n,n*n)`, which indexes rows by the first tensor factor instead of the output coordinate —
it made $\dim Zs > \dim\ker$ and produced spurious "counterexamples"; (ii) the unitality test summed
over the wrong einsum index; (iii) the endomorphism test evaluated $\alpha(e_i)\cdot e_j$ instead of
$\alpha(e_i e_j)$. After the fix, the harness reproduces three known answers: the dual numbers are
determined by their twisted product and are not zpd; α = id gives the Jordan product; α = 0 gives
the product.

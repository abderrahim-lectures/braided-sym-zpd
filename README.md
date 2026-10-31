# Algebras Determined by a Braided-Symmetric Product

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v8**.

## The idea of the paper

An algebra is zero product determined when every bilinear map that vanishes on the pairs with zero product factors through the product. We replace the product by any bilinear map and ask the same question. For the symmetrized products $\mu_\sigma$, this asks when the algebra with that product is zero product determined, and hence when the braided-symmetric derivations of that product can be studied through zero products. The answer is a criterion in terms of the kernel of the induced map $A\otimes A\to A$, and it needs no surjectivity hypothesis. For the symmetrized products of three braidings on a commutative algebra, with $\alpha$ an endomorphism in the twisted case, $\mu$ has the form $f(xy)$ with $f$ linear. The same holds on any algebra when the twist reverses products. Every unital zero product determined algebra is determined by every such $\mu$. The converse holds when $f$ is injective, so the identity braiding gives nothing new in characteristic other than 2. The converse fails for the twisted braiding, because the dual numbers are determined by their twisted product but are not zero product determined. A computation over $\mathbb{F}_3$ shows that the algebra of $2\times 2$ matrices is determined by a twisted product that has no form $f(xy)$.

### Contents

1. Introduction
2. Preliminaries
3. Determined by a bilinear map
4. Products of the form f(xy)
5. Determined but not zpd

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-sym-zpd.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDFs of the released versions |
| `lean/Research/BraidedSymZpd/` | Lean 4 file that checks the $\mathbb{F}_3$ computation of `prop:matrix`; it also imports `Research.Zpd.Basic` and `Research.Zpd.DualNumbers` from the author's research repository, which are not published here, so it does not build from this repository alone |

Build the paper with `cd paper && latexmk -pdf braided-sym-zpd.tex`. The Lean file's `M2F3Check` block is self-contained and can be checked alone (`sed -n '/^namespace M2F3Check/,/^end M2F3Check/p' … > M2F3Check.lean && lean M2F3Check.lean`); a full `cd lean && lake build` needs the two missing modules and a mathlib revision pinned to the toolchain.

## Change log

One entry per released version, newest first. Only the commits for v3 to v8 are in this repository's history, and no tags have been created.

- **v8** (2026-10-31): corrections from an external review, all listed in the header comment of `paper/braided-sym-zpd.tex`: the version stamp, the undefined linearisation of the Jordan product, the hypothesis of the abstract's sentence on the twisted braiding, the `Tri` locator (§2.2), the credit for matrix algebras, `mu` for the product in the definition of the symmetrized product, and one-line proofs for two assertions. Two statements were too strong and are corrected: `thm:zpd-fxy` now assumes $A$ unital (it is false without it), and the abstract's sentence on the twisted braiding now assumes $\alpha$ an endomorphism.
- **v7** (2026-10-17): the notion is tied to braided-sym-deriv (A is determined by mu exactly when the nonassociative algebra (A, mu) is zpd; braided-symmetric derivations are the derivations of (A, \cdot_sigma), Adrabi2026 Definition 3.1 and Remark 3.4), the criterion is now Corollary cor:criterion of Bresar Proposition 1.3 applied to (A, mu) instead of a reproof, Remark rem:derivations treats derivations through zero products; two claims are added, Corollary `cor:triangular` and Proposition `prop:matrix` (the $\mathbb{F}_3$ computation);
- **v6** (2026-10-17): the layout follows braided-sym-deriv (a Preliminaries section recalls the definitions and the equivalent forms of Bresar; the Introduction points to every section), the citation of Bresar Theorem 2.27 carries its locator and the dual numbers example has a linking sentence. No claim changes; sections 2 to 4 are now 3 to 5.
- **v5** (2026-10-16): every result recalled from a reference is stated as the source gives it: the source's own kind (proposition, lemma, theorem, corollary, definition), its whole statement, one environment per result, nothing merged or specialized. No claim changes.
- **v4** (2026-10-16): the sentences that mention Lean are removed, as the owner rule of 2026-10-15 asks; the Lean file lives in the public repository of the paper. No claim changes.
- **v3** (2026-10-16): Bresar Corollary 2.17(a), Theorem 2.27 and Definition 3.14 are stated before use. No claim changes.
- **v2** (2026-09-27): introduction defines the three braidings directly and no longer cites braided-sym-deriv; Corollary 3.5 (anti-endomorphism twist) answers the transpose case of Question 4.3; the question is restated for the automorphism conjugation by diag(1,-1)
- **v1** (2026-09-25): first version

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. A. Adrabi, Braided-symmetric derivations of algebras, preprint, Mohammed V University in Rabat, 2026.
2. Brice, D., Huang, H.: On zero product determined algebras. Linear and Multilinear Algebra **63**, 326–342 (2015).
3. Brešar, M.: Zero Product Determined Algebras. Frontiers in Mathematics. Birkhäuser, Cham (2021).
4. Horn, R.A., Johnson, C.R.: Matrix Analysis, 2nd edn. Cambridge University Press, Cambridge (2013).

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.

# Algebras Determined by a Braided-Symmetric Product

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v6**.

## The idea of the paper

An algebra is zero product determined when every bilinear map that vanishes on the pairs with zero product factors through the product. We replace the product by any bilinear map and ask the same question. The answer is a quotient criterion that needs no surjectivity hypothesis. For the symmetrized products of three braidings on a commutative algebra, has the form f(xy) with f linear. The same holds on any algebra when the twist reverses products, as the transpose does on matrices. Every unital zero product determined algebra is determined by every such . The converse holds when f is injective, so the identity braiding gives nothing new in characteristic other than 2. The converse fails for the twisted braiding, because the dual numbers are determined by their twisted product but are not zero product determined.

### Contents

1. Introduction
2. Preliminaries
3. Determined by a bilinear map
4. Products of the form f(xy)
5. Determined but not zpd
6. Acknowledgments

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-sym-zpd.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDF of the latest release |
| `lean/Research/BraidedSymZpd/` | Lean 4 files that check computations and lemmas of the paper (mathlib only) |

Build the paper with `cd paper && latexmk -pdf braided-sym-zpd.tex`. Build the Lean files with `cd lean && lake build`.

## Change log

One entry per released version, newest first. Each version is also a tag of this repository.

- **v6** (2026-10-17): the layout follows braided-sym-deriv (a Preliminaries section recalls the definitions and the equivalent forms of Bresar; the Introduction points to every section), the citation of Bresar Theorem 2.27 carries its locator and the dual numbers example has a linking sentence. No claim changes; sections 2 to 4 are now 3 to 5.
- **v5** (2026-10-16): every result recalled from a reference is stated as the source gives it: the source's own kind (proposition, lemma, theorem, corollary, definition), its whole statement, one environment per result, nothing merged or specialized. No claim changes.
- **v4** (2026-10-16): the sentences that mention Lean are removed, as the owner rule of 2026-10-15 asks; the Lean file lives in the public repository of the paper. No claim changes.
- **v3** (2026-10-16): Bresar Corollary 2.17(a), Theorem 2.27 and Definition 3.14 are stated before use. No claim changes.
- **v1** (2026-09-25): first version
- **v2** (2026-09-27): introduction defines the three braidings directly and no longer cites braided-sym-deriv; Corollary 3.5 (anti-endomorphism twist) answers the transpose case of Question 4.3; the question is restated for the automorphism conjugation by diag(1,-1)

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. Brešar, M.: Zero Product Determined Algebras. Frontiers in Mathematics. Birkhäuser, Cham (2021).

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.

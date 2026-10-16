# Algebras Determined by a Braided-Symmetric Product

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v3**.

## The idea of the paper

An algebra is zero product determined when every bilinear map that vanishes on the pairs with zero product factors through the product. We replace the product by any bilinear map and ask the same question. The answer is a quotient criterion that needs no surjectivity hypothesis. For the symmetrized products of three braidings on a commutative algebra, has the form f(xy) with f linear. The same holds on any algebra when the twist reverses products, as the transpose does on matrices. Every unital zero product determined algebra is determined by every such . The converse holds when f is injective, so the identity braiding gives nothing new in characteristic other than 2. The converse fails for the twisted braiding, because the dual numbers are determined by their twisted product but are not zero product determined. All results are proved in Lean 4.

### Contents

1. Introduction
2. Determined by a bilinear map
3. Products of the form f(xy)
4. Determined but not zpd
5. Acknowledgments

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-sym-zpd.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDF of the latest release |
| `lean/Research/BraidedSymZpd/` | Lean 4 files that check computations and lemmas of the paper (mathlib only) |

Build the paper with `cd paper && latexmk -pdf braided-sym-zpd.tex`. Build the Lean files with `cd lean && lake build`.

## Change log

One entry per released version, newest first. Each version is also a tag of this repository.

- **v3** (2026-10-16): Bresar Corollary 2.17(a), Theorem 2.27 and Definition 3.14 are stated before use. No claim changes.
- **v1** (2026-09-25): first version
- **v2** (2026-09-27): introduction defines the three braidings directly and no longer cites braided-sym-deriv; Corollary 3.5 (anti-endomorphism twist) answers the transpose case of Question 4.3; the question is restated for the automorphism conjugation by diag(1,-1)

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. Brešar, M.: Zero Product Determined Algebras. Frontiers in Mathematics. Birkhäuser, Cham (2021).

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.

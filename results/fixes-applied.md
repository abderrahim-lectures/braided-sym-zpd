# Fix pass on the paper — what changed, and what could not be fixed

Working-tree changes only: **nothing is committed**, and the released artifact `pdf/braided-sym-zpd-v7.pdf`
is untouched. The fixes are unreleased; the author should cut a v8 if they are kept.

Baseline for the defect numbers: `results/deep-review-v7.md` (audit of commit `977d4ab`).

## What was changed

### `paper/braided-sym-zpd.tex`

| Defect | Change |
|---|---|
| D1 | `\paperversion{2}` → `{7}`; the title page now prints "Preprint version 7" |
| D2 | the undefined `q_\circ` is replaced by the map it names, $\overline{\circ}\colon A\otimes A\to A$, $x\otimes y\mapsto x\circ y$ |
| D6, D17 | the `Tri(A_1,M,A_2)` locator is `\S2.2` instead of `\S2.1`, and the duplicated citation is gone |
| D7 | the abstract's sentence on three braidings now carries "with $\alpha$ an endomorphism in the twisted case" |
| D8 | `thm:zpd-fxy` now reads "Let $A$ be a unital zpd algebra" — this is not cosmetic: without it the theorem is **false**, with the counterexample given in D8 of the review |
| D11 | the "13 = 13" remark names its product, $xy+y^{\mathsf T}x^{\mathsf T}$ |
| D12 | the abstract no longer advertises a "quotient criterion": it says the criterion is in terms of the kernel of the induced map |
| D13 | the abstract no longer speaks of "the symmetrised products of braided-symmetric derivations"; it speaks of the products $\mu_\sigma$ and of their braided-symmetric derivations |
| D14 | the symmetrised product in §2 is written with $m$, the linearisation of the product, not with $\mu$ |
| D15 | the header no longer credits v7 with removing the acknowledgments (that was v6), and a review-pass note records this pass |
| D18 | the introduction credits matrix algebras to `thm:zpd-fxy` with Corollary 2.17(a), and triangular algebras to `cor:triangular` |
| D19 | the two "not of the form $f(xy)$" assertions (lines 292, 395) now carry their one-line proofs |

### `README.md`

| Defect | Change |
|---|---|
| D3 | the three stripped expressions are restored ($\mu_\sigma$, $f(xy)$, $\mu$, $2\times2$) |
| D4 | the claim that every version is a tag is replaced by the truth: only v3–v7 are in the history and no tags exist |
| D5 | "mathlib only" is corrected, and the build paragraph no longer claims that `lake build` works |
| D9 | the v7 entry now records the two claims it added, and an "unreleased" entry lists this fix pass |
| D16 | v2 again precedes v1 in a list that claims to be newest-first |

### `lean/Research/BraidedSymZpd/BraidedSymZpd.lean`

| Defect | Change |
|---|---|
| D5 | the two `induction` blocks over $B\otimes_k B$ gain the missing `| zero =>` branch — this was a genuine elaboration error, not a missing import |
| D10 | the docstring no longer advertises `symProdLinear` or `mapDetermined_symProd_std_iff_zJpd` (neither exists in the file); the cross-reference points at `mapOfQuot_jordanProd_surjective`; the "noncommutative case is open" sentence is replaced by what the file actually shows (the $\mathbb{F}_3$ computation below, and `mapDetermined_twisted_anti_of_zpd` for a product-reversing $\alpha$); references to `BraidedSymmetric.lean` and `formalization-debt.md` now say that those files are not in this repository |

## What was verified after the changes

- The paper builds: `cd paper && latexmk -pdf braided-sym-zpd.tex`, 7 pages, no undefined references,
  one overfull `\vbox` of 0.69pt (a page-break artifact, invisible).
- The Lean file, **with the unpublished `Research.Zpd.Basic` replaced by a scratch stub and the `Dual`
  section removed**, elaborates completely on Lean 4.33.1 with the Mathlib at `/opt/mathlib` — including
  both repaired induction blocks and the three `M2F3Check` guards. Before the fix the same check failed
  with exactly the two `zero` errors.

## What could not be fixed, and why

- **D5, the rest of it.** `Research.Zpd.Basic` and `Research.Zpd.DualNumbers` are not in this repository,
  and they are not Mathlib: `DualNumbers`, `dualFst` and `dualSnd` occur **zero** times in Mathlib, so
  they are the author's own API inside the unpublished module. Nothing in this repository can supply
  them. `lakefile.toml` also pins Mathlib to `rev = "master"` while `lean-toolchain` pins `v4.35.0`, and
  no `lake-manifest.json` is committed; a correct pin needs the author's working setup. The `Dual`
  section of the Lean file is therefore **unverified** — it is the one part whose elaboration I could not
  reproduce.
- **D6's confidence.** `\S2.2` follows from the book's table of contents (§2.1 is "zpd Rings", §2.2 is
  "Examples and Non-examples of zpd Algebras"), but I could not read §2.2 itself. The author should
  confirm the locator.
- **The released PDF.** `pdf/braided-sym-zpd-v7.pdf` still says "Preprint version 2" and still contains
  the old abstract. It is the v7 artifact, so I did not overwrite it; a v8 build is needed.

## One further observation, recorded rather than changed

`mapDetermined` in the Lean file quantifies its target `V : Type v`, i.e. at the universe of `B`, whereas
`def:determined` in the paper quantifies over *every* vector space. I found this because a
`ZeroProductDetermined` whose `V` sits in a different universe does not unify with it. It is a technical
restriction rather than a mathematical one, but it is a faithfulness gap between the Lean statement and
the paper, and it should not be "fixed" without seeing the signature of `Research.Zpd.Basic`, which the
author's other files also use.

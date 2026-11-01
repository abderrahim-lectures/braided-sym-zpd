# Statement audit: the finrank bridge (`M2F3Bridge`) against `prop:matrix`

Scope: `lean/Research/BraidedSymZpd/M2F3Bridge.lean`, compared with the paper's `prop:matrix` and
with the proof the paper gives for it. Proof status and the axiom audit are separate, at the end.

## Source

**Paper**, `paper/braided-sym-zpd.tex`, `prop:matrix`:

> Let `A = M₂(𝔽₃)` and let `α` be conjugation by `diag(1,−1)`, an involutive automorphism. Then `A`
> is determined by `μ_α(x,y) = xy + α(yx)`.

Its proof: by `cor:criterion` it suffices to show `Zs_{μ_α} = ker μ̄_α`, and `Zs ⊆ ker` always
holds; "the matrix of `μ̄_α` in the bases of matrix units has rank 4 over `𝔽₃`, so
`dim ker μ̄_α = 12`; among the `81·81` pairs exactly `417` satisfy `μ_α(x,y) = 0`; Gaussian
elimination shows that the `417` tensors span a subspace of dimension 12; so the two subspaces have
the same dimension and are equal".

## What the Lean statement is

```
BraidedSymZpd.M2F3Bridge.determined : Determined mu
```

a **closed** statement: it has no hypotheses at all — `K := ZMod 3`, `A := Matrix (Fin 2) (Fin 2) K`,
`alpha`, `mu` are concrete definitions at the top of the file. A hidden assumption therefore cannot
hide in a hypothesis; the audit has to check the definitions and the conclusion.

| source | Lean | verdict |
|---|---|---|
| `A = M₂(𝔽₃)` | `A := Matrix (Fin 2) (Fin 2) (ZMod 3)`, with `Fact (Nat.Prime 3)` giving the field | match |
| `α` = conjugation by `diag(1,−1)` | `alpha`, `diagPM`, `alpha_eq : alpha x = diagPM * x * diagPM`, `diagPM_mul_self : diagPM * diagPM = 1` | match |
| `α` an **involutive automorphism** | `alpha_mul : alpha (x*y) = alpha x * alpha y`, `alpha_involutive : Function.Involutive alpha` | **added by this audit** — before it, only the linearity of `α` was available |
| `μ_α(x,y) = xy + α(yx)` | `mu := ZpdCore.twistMu alphaLM`, i.e. `xy + α y * α x`; `mu_apply_paper : mu x y = x * y + alpha (y * x)` | **added by this audit** — the two forms agree because `α` is multiplicative, and that step is now machine-checked |
| "`A` is determined by `μ_α`" | `Determined mu` (`def:determined`) | match |
| rank of `μ̄_α` is `4` | `finrank_range : finrank (range μ̄) = 4` | equivalent (rank = `finrank` of the range) |
| `dim ker μ̄_α = 12` | `finrank_ker : finrank (ker μ̄) = 12`, from rank–nullity and `finrank_tensor : finrank (A ⊗ A) = 16` | match |
| the `417` tensors span dimension `12` | `linearIndependent_tensors` (twelve of them are independent) and `finrank_Zmu : finrank Z_μ = 12` | same dimension, different certificate — see below |
| `Zs = ker μ̄` | `Zmu_eq_ker`, then `Determined` by `determined_iff` | match |

## Where the proof differs from the paper's, and why that is not a fidelity problem

The paper spans `Z_μ` with **all 417** zero-pair tensors and compares the dimension with `ker μ̄`.
The Lean does not enumerate the 417: it exhibits **twelve** zero-pair tensors, proves them linearly
independent with a `decide`-checked pivot matrix (`cert : nInv * piv = 1`), and gets

```
12 ≤ finrank Z_μ ≤ finrank (ker μ̄) = 12
```

so `Z_μ = ker μ̄` by `Submodule.eq_of_le_of_finrank_eq`. Both are the paper's sentence "the two
subspaces have the same dimension and are equal"; the Lean's route needs less computation.
The numbers themselves — `417` zero pairs, rank `4`, the 417 tensors spanning `12` — are checked
separately, by kernel evaluation, in `lean/Research/BraidedSymZpd/M2F3.lean`
(`zeroPairs_card`, `rankMu_eq`, `rank_zeroPairs`). The bridge does not consume those three
theorems; it re-derives the two dimensions it needs.

## What is not a hidden assumption

* There is no hypothesis in `determined` to check; the definitions are the concrete ones above.
* `ZMod 3` is `𝔽₃` (`Fact (Nat.Prime 3)` is an instance in the file).
* `Determined` quantifies its test space `V` in the same universe as `A` — the documented technical
  restriction of `ZpdCore.Determined` (a Lean proposition cannot quantify over all universes), not a
  mathematical hypothesis.
* `finrank` is taken over `ZMod 3`; `Module.finrank_tensorProduct` and `Module.finrank_matrix` give
  `4` and `16`, and no finiteness hypothesis is added by hand.

## Axiom audit (rerun)

`cd lean && ./check.sh` builds all six modules. For this file:

```
'BraidedSymZpd.M2F3Bridge.alpha_mul'              depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.alpha_involutive'       depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.mu_apply_paper'         depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.linearIndependent_tensors' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.w_indep'                depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.finrank_range'          depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.finrank_ker'            depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.Zmu_eq_ker'             depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.determined'             depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no project axiom; the file elaborates without warnings.

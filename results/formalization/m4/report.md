# m4 — the two Lean 4 formalisation tasks (swarm `smvxe6cn7`)

Both tasks are formalised, compile, and use only Lean's standard axioms. Two files:

| file | task | main statements |
|---|---|---|
| `Task1Triangular.lean` | TASK 1, `cor:triangular` | `ZpdCore.Tri.cor_triangular`, `Tri.determined_comp_mul`, `Tri.determined_twist`, `Tri.zeroProductDetermined` |
| `Task2Matrix.lean` | TASK 2, `prop:matrix` | `BraidedSymZpd.determined_matrix2`, `M2F3Bridge.determined`, `M2F3Bridge.Zmu_eq_ker` |

Each file is self-contained and imports only Mathlib plus the shipped project modules
`ZpdCore.Zpd` and (for Task 2) `Research.BraidedSymZpd.BraidedSymZpd`.  Nothing in `lean/` or
`paper/` was modified by me, and neither file depends on any other member's file: I verified both
against a library rebuilt from source in a private `LEAN_PATH` that contains no project `.olean`
(see "Independent rebuild" below).

## Task 1 — `cor:triangular`, proved

`ZpdCore.Tri.cor_triangular` states, for a field `K`, unital `K`-algebras `A₁`, `A₂`, and a unital
`(A₁, A₂)`-bimodule `M` (`Module A₁ M`, `Module A₂ᵐᵒᵖ M`, `IsScalarTower` on both sides,
`SMulCommClass A₁ A₂ᵐᵒᵖ M`), assuming `Subring.closure {e : A₁ | e * e = e} = ⊤` and
`Subring.closure {e : A₂ | e * e = e} = ⊤`, the conjunction of

* `ZeroProductDetermined K (Tri A₁ M A₂)`;
* `∀ f : Tri A₁ M A₂ →ₗ[K] Tri A₁ M A₂, Determined (compMu (LinearMap.mul K (Tri A₁ M A₂)) f)`,
  i.e. `A` is determined by `μ (x, y) = f (x * y)` for every linear `f`;
* `∀ α, (∀ x y, α (x * y) = α y * α x) → Determined (twistMu α)`, i.e. `A` is determined by the
  twisted product for every linear `α` with `α (x * y) = α y * α x`.

The hypotheses are exactly the paper's; no hypothesis is weakened or added, `M` is an arbitrary
bimodule, and `f`, `α` are arbitrary `K`-linear maps.

Proof route (the paper's):
1. `ZpdCore.zpd_of_idempotents_generate`: Brešar, Theorem 2.15 (Lemma 2.2). For a bilinear
   `φ : A →ₗ[K] A →ₗ[K] V` vanishing on zero products, the set
   `R₀ = {r | ∀ x z, φ (x * r) z = φ x (r * z)}` is a `Subring` of `A` (`one_mem'` is
   `mul_one`/`one_mul`; `mul_mem'` moves `r` and then `s` across `φ`), and every idempotent `e`
   lies in it, via `x * e * (z - e * z) = 0` and `(x - x * e) * (e * z) = 0`. Hence
   `R₀ = ⊤`, and taking `r = y` gives `φ x y = φ (x * y) 1`.
2. `ZpdCore.Tri`: the type `Tri A₁ M A₂` of triples `(a, m, b)`, componentwise addition,
   `(a, m, b) * (a', m', b') = (a * a', a • m' + m • b', b * b')`, unit `(1, 0, 1)`, with
   `AddCommGroup`, `Ring`, `Module K` and `Algebra K` instances (the `Algebra` instance needs
   `algebraMap k • m = k • m = m • algebraMap k`, which follows from the two `IsScalarTower`s).
3. `ZpdCore.Tri.closure_idempotents`: Brešar, Corollary 2.5 — `(r₁, 0, 0)` and `(0, 0, r₂)` are
   built by induction over `Subring.closure_induction` from the idempotents of `A₁`, `A₂`, and
   `(0, m, 0) = (1, m, 0) - (1, 0, 0)` is a difference of two idempotents, so the idempotents of
   `Tri A₁ M A₂` generate it.
4. The two conclusions follow from `ZpdCore.determined_comp_of_right_id` (with the right identity
   `1` of the product) and `ZpdCore.anti_twisted_determined`.

`ZpdCore.zmod2_tri_zpd` shows the hypotheses are satisfiable (`Tri` over `ZMod 2`).

## Task 2 — `prop:matrix`, proved

`BraidedSymZpd.determined_matrix2` is the paper's statement in the library's own form:

```
BraidedSymZpd.determined_matrix2 :
  ZpdCore.Determined (ZpdCore.twistMu (BraidedSymZpd.conjByUnit (K := ZMod 3) D))
```

where `D : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ` is the unit with underlying matrix
`diag (1, -1)` (`M2F3Bridge.u`, `M2F3Bridge.D`).  `M2F3Bridge.alphaLM_eq_conjByUnit` proves that
the linear map `alpha` used for the numerical work (sign flip on the two off-diagonal entries) is
exactly `conjByUnit D`, so this is `Determined` for `μ_α (x, y) = x * y + α y * α x`,
`α = conjByUnit diag (1,-1)` — the paper's `prop:matrix`.  No weakening: the algebra is
`M₂(𝔽₃)`, the map is the paper's conjugation, and `Determined` is the library's definition.

Proof route (the paper's `cor:criterion` plus the numbers):
1. `M2F3Bridge.linearIndependent_tensors`: twelve pure tensors `xT j ⊗ yT j` with
   `μ (xT j) (yT j) = 0` (`mu_zero`), certified independent by the 12×12 pivot matrix `piv` and a
   left inverse `nInv` with `nInv * piv = 1` proved by `decide` (`cert`); independence then
   follows from `Fintype.linearIndependent_iff`.
2. `twelve_le_finrank_Zmu` (from `finrank_span_eq_card` and `Submodule.finrank_mono`) and
   `ZpdCore.Zmu_le_ker`.
3. `four_le_finrank_range`: four independent elements `w` of the range (`w_indep` by `decide`).
4. `finrank_tensor : finrank K (A ⊗[K] A) = 16` from `Module.finrank_tensorProduct` and
   `Module.finrank_matrix`; rank–nullity `LinearMap.finrank_range_add_finrank_ker` gives
   `finrank_range = 4`, `finrank_ker = 12`, `finrank_Zmu = 12`.
5. `Zmu_eq_ker` by `Submodule.eq_of_le_of_finrank_eq`, then `ZpdCore.determined_iff`.

The concrete facts are kernel-checked by `decide` (`cert`, `w_indep`, `mu_zero`, `w_eq`,
`u_mul_u`) — no `native_decide`, no `#eval`/`#guard` proofs.

### Additions of mine in `Task2Matrix.lean`

* `M2F3Bridge.u`, `u_eq_diagonal`, `u_mul_u`, `D`, `coe_D`, `coe_inv_D`, `alpha_eq_conj`,
  `alphaLM_eq_conjByUnit`: `alpha` is the inner conjugation by `diag (1, -1)`.
* `determined_matrix2`: the paper's statement in `conjByUnit` form.
* `determined_jordan`: `M₂(𝔽₃)` is determined by the *symmetrised* product `x * y + y * x`
  (`twistMu LinearMap.id`), via `BraidedSymZpd.determined_twist_conj_iff` (`rem:inner`).
* `determined_all_inner`: `prop:matrix` for **every** inner conjugation, not only `diag (1,-1)`.
* `muBar_twist_id_flip`: the flip identity `μ̄_∘ = ∘̄ ∘ (id + flip)`, and `Zmu_twist_id`: `Z_∘` is
  spanned by the anticommuting pairs `x ⊗ y` with `x * y + y * x = 0`.
* The flip-eigenspace form of the kernel, in characteristic `≠ 2`:
  `flip_flip`, `flip_symmetrization` (`2⁻¹ • (t + flip t)` is flip-invariant),
  `flip_antisymmetrization` (`2⁻¹ • (t - flip t)` is anti-invariant),
  `mem_ker_muBar_twist_id_iff` (`t ∈ ker μ̄_∘ ↔ ` the product kills the symmetric part) and
  `ker_muBar_twist_id_eq` (`ker μ̄_∘ = ker (∘̄ ∘ (2⁻¹ • (id + flip)))`).

## What is assumed

* Mathlib (Lean v4.33.1, the built Mathlib on `LEAN_PATH`) plus the project modules
  `ZpdCore.Zpd` and `Research.BraidedSymZpd.BraidedSymZpd` as shipped in `lean/`. No other member's
  file, no added axiom, no `sorry`, no `native_decide`.
* `ZMod 3` is used as a field through `instance : Fact (Nat.Prime 3) := ⟨by decide⟩` (the library's
  own `M2F3.lean` does the same).
* The library's `ZpdCore.Determined` quantifies over `V : Type u` in the *same* universe as `K` and
  `A` (a documented technical restriction of the library's definition, see the docstring of
  `ZpdCore.Zpd`); the statements above are the library's, unchanged.
* `#print axioms` for every theorem in both files reports only `propext`, `Classical.choice` and
  `Quot.sound`.
* Every line of both files is at most 100 characters (checked with Python `len` on the decoded
  lines; note that `𝔽₃` and `⁻¹` are one character but several bytes).

## Commands and output

```
$ cd lean && LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean ../results/formalization/m4/Task1Triangular.lean
```

```
$ cd lean && LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean ../results/formalization/m4/Task1Triangular.lean
'ZpdCore.zpd_of_idempotents_generate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.Tri.closure_idempotents' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.Tri.zeroProductDetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.Tri.determined_comp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.Tri.determined_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.zmod2_tri_zpd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZpdCore.Tri.cor_triangular' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

```
$ cd lean && LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean ../results/formalization/m4/Task2Matrix.lean
```

```
$ cd lean && LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean ../results/formalization/m4/Task2Matrix.lean
'BraidedSymZpd.M2F3Bridge.linearIndependent_tensors' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.w_indep' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.finrank_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.finrank_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.Zmu_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.M2F3Bridge.determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.muBar_twist_id_flip' depends on axioms: [propext, Quot.sound]
'BraidedSymZpd.mem_ker_twist_id_iff' depends on axioms: [propext, Quot.sound]
'BraidedSymZpd.M2F3Bridge.alphaLM_eq_conjByUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.determined_matrix2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.determined_jordan' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.determined_all_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.Zmu_twist_id' depends on axioms: [propext, Quot.sound]
'BraidedSymZpd.flip_flip' depends on axioms: [propext, Quot.sound]
'BraidedSymZpd.flip_symmetrization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.flip_antisymmetrization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.mem_ker_muBar_twist_id_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidedSymZpd.ker_muBar_twist_id_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

### Independent rebuild

To show that neither file depends on the untracked files that are currently also present under
`lean/` (`lean/ZpdCore/Triangular.lean`, `lean/Research/BraidedSymZpd/M2F3Bridge.lean`, added by
other members, and `lean/check.sh`'s extra lines — I did not create or change them), I rebuilt the
library from source into a private `LEAN_PATH` containing no project `.olean`:

```
OUT=../.ultramath/smvxe6cn7/m4/build/lib/lean; mkdir -p $OUT/ZpdCore $OUT/Research/BraidedSymZpd
LEAN_PATH="$OUT:<Mathlib dirs only>" lean -o $OUT/ZpdCore/Zpd.olean ZpdCore/Zpd.lean
LEAN_PATH="$OUT:<Mathlib dirs only>" lean -o $OUT/Research/BraidedSymZpd/BraidedSymZpd.olean \
  Research/BraidedSymZpd/BraidedSymZpd.lean
LEAN_PATH="$OUT:<Mathlib dirs only>" lean ../results/formalization/m4/Task1Triangular.lean   # exit 0
LEAN_PATH="$OUT:<Mathlib dirs only>" lean ../results/formalization/m4/Task2Matrix.lean       # exit 0
```

Both elaborations printed the `#print axioms` lines quoted above and exited with status 0.

## Attribution

The two *developments* were written by other members of this swarm and placed in `lean/`
(untracked there): the Task-1 development `lean/ZpdCore/Triangular.lean` by member m2 (direction
d2) and the twelve-tensor bridge `lean/Research/BraidedSymZpd/M2F3Bridge.lean` by member m5
(direction d4).  Since the acceptance criteria require the files under
`results/formalization/<member>/`, I re-elaborated both from source and extended them; nothing in
them had to be repaired, they compile as they stand.  My additions: the `cor_triangular`
conjunction under the paper's label in Task 1, and in Task 2 the `conjByUnit` form of
`prop:matrix`, its statement for the symmetrised product and for all inner conjugations, and the
flip-eigenspace description of `ker μ̄_∘` (my own direction d8).  I verified every statement
printed above myself.

# `ZJpd.lean` — zero Jordan product determined algebras, and `prop:matrix` without enumeration

Member `m3`, swarm `smvxe6cn7`. File: [`ZJpd.lean`](ZJpd.lean), 316 lines, Lean 4.33.1 + Mathlib,
all lines ≤ 100 columns.

## What this file does

It proves **Task 2's conclusion** (`prop:matrix` for `M₂(𝔽₃)` and `α` = conjugation by
`diag (1, -1)`) by a *structural* route that enumerates nothing:

* it proves the An–Li–He lemma (`Zero Jordan product determined algebras`, LAA 475 (2015),
  Theorem 2.1 — the step the paper's `rem:inner` cites for Brešar's Theorem 3.15): **a unital
  algebra over a field with `2 ≠ 0` whose idempotents span it linearly is zero Jordan product
  determined**, i.e. `Determined (twistMu LinearMap.id)`, where `twistMu id x y = x * y + y * x`;
* it checks that the idempotents of `M₂(K)` span it (`e₁₁`, `e₂₂`, `e₁₁ + e₁₂`, `e₁₁ + e₂₁`);
* it concludes, through the library's `BraidedSymZpd.determined_twist_conj_iff` (the paper's
  `rem:inner`), `Determined (twistMu (conjByUnit D))` for **every** unit `D`, hence for
  `D = diag (1, -1)` over `ZMod 3`.

This is independent of the kernel-evaluation route (`417` pairs, rank `4`, dimension `12`) and of
`cor:triangular`; it also promotes `prop:matrix` from one unit `D` over `𝔽₃` to every unit over
every field of characteristic `≠ 2`.

## Exact statements proved

| Declaration | Statement |
|---|---|
| `ZJpd.two_smul_phi_apply_of_idem` | for `φ : A →ₗ A →ₗ V` with `φ x y = 0` whenever `x*y + y*x = 0`, any idempotent `e` and any `a`: `2 • φ a e = φ (a*e) 1 + φ (e*a) 1` |
| `ZJpd.two_smul_phi_apply` | the same for `b` in the linear span of the idempotents |
| `ZJpd.determined_twistMu_id` | `(2:K) ≠ 0` and `Submodule.span K {e | e*e = e} = ⊤` ⟹ `Determined (twistMu (LinearMap.id))` |
| `ZJpd.span_idempotents_eq_top` | for any field `K`: the idempotents of `Matrix (Fin 2) (Fin 2) K` span it |
| `ZJpd.determined_twistMu_id_matrix` | `(2:K) ≠ 0` ⟹ `M₂(K)` is determined by `twistMu LinearMap.id` |
| `ZJpd.determined_twistMu_conjByUnit` | `(2:K) ≠ 0`, any unit `D` ⟹ `Determined (twistMu (conjByUnit D))` |
| `ZJpd.twistMu_conjByUnit_apply` | `twistMu (conj D) x y = x*y + conj D (y*x)` (the paper's `μ_α (x,y) = xy + α(yx)`) |
| `ZJpd.conjByUnit_diagUnit_apply` | the conjugation by `diagUnit` is `x ↦ diag (1,-1) * x * diag (1,-1)`, written out |
| **`ZJpd.determined_matrix2`** | **`Determined (twistMu (conjByUnit diagUnit))` for `Matrix (Fin 2) (Fin 2) (ZMod 3)`, `diagUnit = diag (1, -1)`** — Task 2's statement |

`ZJpd.determined_matrix2` is the statement the problem calls `BraidedSymZpd.determined_matrix2`;
it is stated in this file's own namespace because `lean/` is not modified.

## Method

For an idempotent `e` put `f = 1 - e`. The four Peirce pieces `a₁ = e a e`, `u = e a f`,
`v = f a e`, `a₀ = f a f` satisfy `a = a₁ + u + v + a₀`, `a e = a₁ + v`, `e a = a₁ + u`, and the
zero-product pairs `(a₁, f)`, `(a₀, e)`, `(u, 1 - 2e)`, `(v, 1 - 2e)` (checked symbolically before
formalisation, and in Lean). Vanishing on those gives `φ a₁ 1 = φ a₁ e`, `φ a₀ e = 0`,
`2 • φ u e = φ u 1`, `2 • φ v e = φ v 1`, hence `2 • φ a e = φ (a e) 1 + φ (e a) 1`; linearity in
the second slot extends this to the span of the idempotents, and then
`φ a b = τ (a*b + b*a)` with `τ z = 2⁻¹ • φ z 1`.

The file imports only `ZpdCore.Zpd`, `Research.BraidedSymZpd.BraidedSymZpd` (both pre-existing) and
`Mathlib.Algebra.Field.ZMod`; it does **not** depend on the `ZpdCore/Triangular.lean` or
`Research/BraidedSymZpd/M2F3Bridge.lean` that other swarm members added to `lean/`, so it checks
against the library as shipped.

## Library reuse (nothing in `lean/` changed)

* `ZpdCore.Determined`, `ZpdCore.twistMu`, `ZpdCore.twistMu_apply`, `ZpdCore.muBar` API.
* `BraidedSymZpd.determined_twist_conj_iff`, `BraidedSymZpd.conjByUnit`,
  `BraidedSymZpd.conjByUnit_mul` — the paper's `rem:inner`, already in the library, so the inner
  twist is transferred to the symmetrised product for free.

## Assumptions and honest scope

* No `sorry`, no `native_decide`, no added axiom (see the audit below). `decide` is used only for
  the unit laws of `diagUnit` and for `(2 : ZMod 3) ≠ 0`; every mathematical step is symbolic.
* The idempotent-span hypothesis is *linear spanning*, which is what the An–Li–He argument needs.
  It holds for `M₂(K)` over any field (proved), hence for `prop:matrix`. It is **not** proved here
  for `M_n(B)` with `B` a general unital algebra, so the paper's `rem:inner` sentence for general
  `B` (which needs the full Brešar Theorem 3.15, i.e. idempotent-*generated* algebras plus the
  Peirce induction of An–Li Theorem 4.4) is **not** covered by this file.
* Task 1 (`cor:triangular`) is not addressed by this file.

## Command run and output

```
cd lean && LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH" lean ../results/formalization/m3/ZJpd.lean
```

`cd lean && ./check.sh` was run first so that the `.olean`s of the library exist. Tail of the
output (exit status `0`, no warnings):

```
'ZJpd.two_smul_phi_apply_of_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.two_smul_phi_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.determined_twistMu_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.span_idempotents_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.determined_twistMu_id_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.determined_twistMu_conjByUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZJpd.determined_matrix2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

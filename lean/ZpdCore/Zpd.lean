/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Algebras determined by a bilinear map

Brešar's zero-product-determined (zpd) algebras are defined for the product of an algebra.
This file develops the same theory for an arbitrary bilinear map `μ` on a `K`-module `A`, which
is the setting of the paper "Algebras Determined by a Braided-Symmetric Product" (all labels
below refer to that paper).

## Main definitions

* `ZpdCore.muBar`: the linearisation `μ̄ : A ⊗[K] A → A` of a bilinear `μ`.
* `ZpdCore.Zmu`: the subspace `Z_μ` of `A ⊗[K] A` spanned by the pure tensors `x ⊗ y` with
  `μ x y = 0`.
* `ZpdCore.Determined`: `A` is determined by `μ` (`def:determined`).
* `ZpdCore.ZeroProductDetermined`: the case `μ = mul`, Brešar's zpd property
  (Definition 1.1 of the reference).

## Main results

* `ZpdCore.determined_iff`: `cor:criterion`, `Determined μ ↔ Z_μ = ker μ̄`, with no
  unitality, associativity or surjectivity hypothesis.
* `ZpdCore.determined_comp_of_right_id`: `thm:zpd-fxy`, in the sharp form in which the unit is
  used only as a right identity of the product.
* `ZpdCore.determined_of_injective_comp`: `prop:injective`.
* `ZpdCore.codim_determined`: `thm:codim`.
* `ZpdCore.identity_determined_iff`: `cor:identity`.
* `ZpdCore.jordan_forces_comm` and `ZpdCore.twisted_forces_comm`: the two "not of the form
  `f (x * y)`" assertions of the paper.

## Implementation notes

Every vector space in this file lives in one universe: the definition of `Determined`
quantifies over `V : Type u` with `K` and `A` in `Type u`. A proposition in Lean can only
quantify over a fixed universe, so this is a technical restriction of the formalisation, not a
mathematical one: the paper's `def:determined` quantifies over every vector space.

No `sorry`, no added axioms; the `#print axioms` block at the end of the file reports only
`propext`, `Classical.choice` and `Quot.sound`.
-/

@[expose] public section

open TensorProduct

namespace ZpdCore

universe u

variable {K : Type u} [Field K]
variable {A : Type u} [AddCommGroup A] [Module K A]

/-! ## The linearisation of a bilinear map and the space `Z_μ` -/

/-- The linearisation `μ̄ : A ⊗[K] A → A` of a bilinear map `μ`, characterised by
`μ̄ (x ⊗ y) = μ x y`. -/
noncomputable def muBar (μ : A →ₗ[K] A →ₗ[K] A) : A ⊗[K] A →ₗ[K] A :=
  TensorProduct.lift μ

@[simp]
theorem muBar_tmul (μ : A →ₗ[K] A →ₗ[K] A) (x y : A) : muBar μ (x ⊗ₜ[K] y) = μ x y :=
  rfl

/-- `Z_μ`: the subspace of `A ⊗[K] A` spanned by the pure tensors `x ⊗ y` with `μ x y = 0`. -/
noncomputable def Zmu (μ : A →ₗ[K] A →ₗ[K] A) : Submodule K (A ⊗[K] A) :=
  Submodule.span K {t : A ⊗[K] A | ∃ x y : A, μ x y = 0 ∧ t = x ⊗ₜ[K] y}

theorem tmul_mem_Zmu {μ : A →ₗ[K] A →ₗ[K] A} {x y : A} (h : μ x y = 0) :
    x ⊗ₜ[K] y ∈ Zmu μ :=
  Submodule.subset_span ⟨x, y, h, rfl⟩

/-- `Z_μ ⊆ ker μ̄`, as stated before `cor:criterion` in the paper. -/
theorem Zmu_le_ker (μ : A →ₗ[K] A →ₗ[K] A) : Zmu μ ≤ LinearMap.ker (muBar μ) := by
  rw [Zmu, Submodule.span_le]
  rintro t ⟨x, y, h, rfl⟩
  simpa using h

/-! ## Determined by `μ` and the criterion -/

/-- `def:determined`: every bilinear map vanishing on the pairs with `μ x y = 0` factors
through `μ`. -/
def Determined (μ : A →ₗ[K] A →ₗ[K] A) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] (φ : A →ₗ[K] A →ₗ[K] V),
    (∀ x y : A, μ x y = 0 → φ x y = 0) →
      ∃ ψ : A →ₗ[K] V, ∀ x y : A, φ x y = ψ (μ x y)

/-- The easy half of `cor:criterion`: if every element of `ker μ̄` is a combination of zero
products, then `A` is determined by `μ`. -/
theorem determined_of_ker_le (μ : A →ₗ[K] A →ₗ[K] A)
    (h : LinearMap.ker (muBar μ) ≤ Zmu μ) : Determined μ := by
  intro V _ _ φ hφ
  have hZ : Zmu μ ≤ LinearMap.ker (TensorProduct.lift φ) := by
    rw [Zmu, Submodule.span_le]
    rintro t ⟨x, y, hxy, rfl⟩
    simpa using hφ x y hxy
  have hker : LinearMap.ker (muBar μ) ≤ LinearMap.ker (TensorProduct.lift φ) :=
    le_trans h hZ
  obtain ⟨q, hq⟩ := (muBar μ).range.exists_isCompl
  let ψ₁ : (A ⊗[K] A ⧸ LinearMap.ker (muBar μ)) →ₗ[K] V :=
    Submodule.liftQ _ (TensorProduct.lift φ) hker
  let e : (A ⊗[K] A ⧸ LinearMap.ker (muBar μ)) ≃ₗ[K] (muBar μ).range :=
    LinearMap.quotKerEquivRange (muBar μ)
  let ψ₂ : (muBar μ).range →ₗ[K] V := ψ₁.comp e.symm.toLinearMap
  refine ⟨LinearMap.ofIsCompl hq ψ₂ 0, ?_⟩
  intro x y
  have h3 : ψ₁ (Submodule.Quotient.mk (x ⊗ₜ[K] y) : A ⊗[K] A ⧸ LinearMap.ker (muBar μ)) =
      (TensorProduct.lift φ) (x ⊗ₜ[K] y) := rfl
  have key : ∀ (hz : muBar μ (x ⊗ₜ[K] y) ∈ (muBar μ).range),
      ψ₂ ⟨muBar μ (x ⊗ₜ[K] y), hz⟩ = φ x y := by
    intro hz
    have h2 : e.symm ⟨muBar μ (x ⊗ₜ[K] y), hz⟩ =
        Submodule.Quotient.mk (x ⊗ₜ[K] y) :=
      LinearMap.quotKerEquivRange_symm_apply_image (muBar μ) (x ⊗ₜ[K] y) hz
    show ψ₁ (e.symm _) = φ x y
    rw [h2, h3]
    rfl
  have h4 : LinearMap.ofIsCompl hq ψ₂ 0 (μ x y) =
      ψ₂ ⟨muBar μ (x ⊗ₜ[K] y), LinearMap.mem_range_self _ _⟩ := by
    rw [← muBar_tmul μ x y]
    exact LinearMap.ofIsCompl_apply_left hq ⟨muBar μ (x ⊗ₜ[K] y), LinearMap.mem_range_self _ _⟩
  exact (h4.trans (key _)).symm

/-- The other half of `cor:criterion`: an element of `ker μ̄` outside `Z_μ` is separated from
`Z_μ` by a linear functional, which yields a bilinear map that does not factor through `μ`. -/
theorem ker_le_Zmu_of_determined (μ : A →ₗ[K] A →ₗ[K] A) (h : Determined μ) :
    LinearMap.ker (muBar μ) ≤ Zmu μ := by
  intro w hw
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (Zmu μ) w]
  intro ℓ hℓ
  obtain ⟨φ, hφ⟩ : ∃ φ : A →ₗ[K] A →ₗ[K] K, ∀ x y : A, φ x y = ℓ (x ⊗ₜ[K] y) :=
    ⟨(TensorProduct.mk K A A).compr₂ ℓ, fun x y => by simp⟩
  have hφ0 : ∀ x y : A, μ x y = 0 → φ x y = 0 := by
    intro x y hxy
    rw [hφ x y, (Submodule.mem_dualAnnihilator ℓ).1 hℓ (x ⊗ₜ[K] y) (tmul_mem_Zmu hxy)]
  obtain ⟨ψ, hψ⟩ := h K φ hφ0
  have hall : ∀ t : A ⊗[K] A, ℓ t = ψ (muBar μ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [muBar_tmul]; exact (hφ x y).symm.trans (hψ x y)
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  rw [hall w, LinearMap.mem_ker.1 hw, map_zero]

/-- **`cor:criterion`**: `A` is determined by `μ` if and only if `Z_μ = ker μ̄`. No
unitality, associativity, surjectivity or finite-dimensionality hypothesis. -/
theorem determined_iff (μ : A →ₗ[K] A →ₗ[K] A) :
    Determined μ ↔ Zmu μ = LinearMap.ker (muBar μ) :=
  ⟨fun h => le_antisymm (Zmu_le_ker μ) (ker_le_Zmu_of_determined μ h),
   fun h => determined_of_ker_le μ (le_of_eq h.symm)⟩

/-! ## Products of the form `f (m x y)`, and the converse for injective `f` -/

/-- The bilinear map `(x, y) ↦ f (m x y)`, that is, `μ = f ∘ m`. -/
noncomputable def compMu (m : A →ₗ[K] A →ₗ[K] A) (f : A →ₗ[K] A) : A →ₗ[K] A →ₗ[K] A :=
  m.compr₂ f

@[simp]
theorem compMu_apply (m : A →ₗ[K] A →ₗ[K] A) (f : A →ₗ[K] A) (x y : A) :
    compMu m f x y = f (m x y) := rfl

/-- **`thm:zpd-fxy`**, in the sharp form in which the unit is used only through a right
identity `e` of `m` (`m b e = b`). No associativity of `m` and no two-sided unit are needed. -/
theorem determined_comp_of_right_id (m : A →ₗ[K] A →ₗ[K] A) (hm : Determined m)
    (f : A →ₗ[K] A) (e : A) (he : ∀ b : A, m b e = b) : Determined (compMu m f) := by
  intro V _ _ φ hφ
  have hzero : ∀ x y : A, m x y = 0 → φ x y = 0 := by
    intro x y hxy
    exact hφ x y (by rw [compMu_apply, hxy, map_zero])
  obtain ⟨ψ₀, hψ₀⟩ := hm V φ hzero
  have hker : LinearMap.ker f ≤ LinearMap.ker ψ₀ := by
    intro b hb
    have h1 : compMu m f b e = 0 := by
      rw [compMu_apply, he b, LinearMap.mem_ker.1 hb]
    have h2 : φ b e = 0 := hφ b e h1
    rw [LinearMap.mem_ker]
    calc ψ₀ b = ψ₀ (m b e) := by rw [he b]
      _ = φ b e := (hψ₀ b e).symm
      _ = 0 := h2
  obtain ⟨q, hq⟩ := f.range.exists_isCompl
  let ψ₁ : (A ⧸ LinearMap.ker f) →ₗ[K] V := Submodule.liftQ _ ψ₀ hker
  let e' : (A ⧸ LinearMap.ker f) ≃ₗ[K] f.range := LinearMap.quotKerEquivRange f
  let ψ₂ : f.range →ₗ[K] V := ψ₁.comp e'.symm.toLinearMap
  refine ⟨LinearMap.ofIsCompl hq ψ₂ 0, ?_⟩
  intro x y
  have h3 : ψ₁ (Submodule.Quotient.mk (m x y) : A ⧸ LinearMap.ker f) = ψ₀ (m x y) := rfl
  have key : ∀ (hz : f (m x y) ∈ f.range), ψ₂ ⟨f (m x y), hz⟩ = φ x y := by
    intro hz
    have h2 : e'.symm ⟨f (m x y), hz⟩ = Submodule.Quotient.mk (m x y) :=
      LinearMap.quotKerEquivRange_symm_apply_image f (m x y) hz
    show ψ₁ (e'.symm _) = φ x y
    rw [h2, h3, hψ₀]
  have h4 : LinearMap.ofIsCompl hq ψ₂ 0 (compMu m f x y) =
      ψ₂ ⟨f (m x y), LinearMap.mem_range_self _ _⟩ := by
    rw [compMu_apply]
    exact LinearMap.ofIsCompl_apply_left hq ⟨f (m x y), LinearMap.mem_range_self _ _⟩
  exact (h4.trans (key _)).symm

/-- **`prop:injective`**: if `f` is injective and `A` is determined by `f ∘ m`, then `A` is
determined by `m`. -/
theorem determined_of_injective_comp (m : A →ₗ[K] A →ₗ[K] A) (f : A →ₗ[K] A)
    (hf : Function.Injective f) (h : Determined (compMu m f)) : Determined m := by
  intro V _ _ φ hφ
  have hφ' : ∀ x y : A, compMu m f x y = 0 → φ x y = 0 := by
    intro x y hxy
    rw [compMu_apply, LinearMap.map_eq_zero_iff f hf] at hxy
    exact hφ x y hxy
  obtain ⟨ψ, hψ⟩ := h V φ hφ'
  exact ⟨ψ.comp f, fun x y => by rw [hψ x y, compMu_apply]; rfl⟩

/-- The product `μ ≡ 0` determines every module (the paper's characteristic `2` remark). -/
theorem determined_zero : Determined (0 : A →ₗ[K] A →ₗ[K] A) := by
  intro V _ _ φ hφ
  exact ⟨0, fun x y => by rw [hφ x y rfl]; rfl⟩

/-! ## The special case of the product: Brešar's zpd algebras -/

/-- Brešar's zero product determined property (Definition 1.1 of the reference): `A` is
determined by its own product. -/
abbrev ZeroProductDetermined (K : Type u) [Field K] (A : Type u) [Ring A] [Algebra K A] : Prop :=
  Determined (LinearMap.mul K A)

section Algebra

variable {A : Type u} [Ring A] [Algebra K A]

/-- **`cor:identity` (i)**: a zpd algebra is determined by `μ x y = 2 * (x * y)`. -/
theorem identity_determined (h : ZeroProductDetermined K A) :
    Determined (compMu (LinearMap.mul K A) ((2 : K) • LinearMap.id)) :=
  determined_comp_of_right_id (LinearMap.mul K A) h _ 1 (fun b => mul_one b)

/-- **`cor:identity` (ii)**: in characteristic other than `2`, `A` is determined by
`μ x y = 2 * (x * y)` if and only if `A` is zpd. -/
theorem identity_determined_iff (h2 : (2 : K) ≠ 0) :
    Determined (compMu (LinearMap.mul K A) ((2 : K) • LinearMap.id)) ↔
      ZeroProductDetermined K A := by
  refine ⟨fun h => determined_of_injective_comp _ ((2 : K) • LinearMap.id) ?_ h,
    fun h => identity_determined h⟩
  intro x y hxy
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
  have h' : (2 : K) • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  rcases smul_eq_zero.1 h' with h | h
  · exact absurd h h2
  · exact sub_eq_zero.1 h

/-! ### The two "not of the form `f (x * y)`" assertions -/

/-- The Jordan product `x * y + y * x` is `f (x * y)` for a linear `f` only if `A` is
commutative; no hypothesis on the characteristic is needed. -/
theorem jordan_forces_comm (f : A →ₗ[K] A)
    (h : ∀ x y : A, f (x * y) = x * y + y * x) : ∀ x y : A, x * y = y * x := by
  intro x y
  have h1 : f (x * y) = x * y + x * y := by
    simpa using h 1 (x * y)
  rw [h x y] at h1
  exact (add_left_cancel h1).symm

/-- The twisted product `x * y + α y * α x` is `f (x * y)` for a linear `f`, with `α` a unital
multiplicative injective map, only if `A` is commutative. -/
theorem twisted_forces_comm (α : A →+* A) (hα : Function.Injective α) (f : A →ₗ[K] A)
    (h : ∀ x y : A, f (x * y) = x * y + α y * α x) : ∀ x y : A, x * y = y * x := by
  have hgen : ∀ z : A, f z = z + α z := by
    intro z
    simpa using h z 1
  intro x y
  have h1 : f (x * y) = x * y + α x * α y := by
    rw [hgen, map_mul]
  rw [h x y] at h1
  have h2 : α x * α y = α y * α x := (add_left_cancel h1).symm
  have h3 : α (y * x) = α (x * y) := by rw [map_mul, map_mul, h2]
  exact (hα h3).symm

/-- The abstract's sentence on the three braidings: on a commutative algebra the symmetrized
products of the identity braiding, the swap and the twisted swap (`α` multiplicative) are all
of the form `f (x * y)` with `f` linear. -/
theorem three_braidings_commutative (hcomm : ∀ x y : A, x * y = y * x) (α : A →ₗ[K] A)
    (hα : ∀ x y : A, α (x * y) = α x * α y) (x y : A) :
    (x * y + x * y = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y)) ∧
      (x * y + y * x = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y)) ∧
      (x * y + α y * α x = (LinearMap.id + α : A →ₗ[K] A) (x * y)) := by
  have h2 : x * y + y * x = x * y + x * y := by rw [hcomm y x]
  have hf : x * y + x * y = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y) := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, two_smul]
  refine ⟨hf, h2.trans hf, ?_⟩
  rw [LinearMap.add_apply, LinearMap.id_apply, hα, hcomm (α y) (α x)]

/-! ### `thm:codim` -/

/-- **`thm:codim`**: if `ker f` is a two-sided ideal of codimension `1` not containing `1`,
then `A` is determined by `x, y ↦ f (x * y)`, with no zpd hypothesis. -/
theorem codim_determined (f : A →ₗ[K] A)
    (hN : ∀ n : A, f n = 0 → ∀ b : A, f (n * b) = 0 ∧ f (b * n) = 0)
    (hc : ∃ c : A →ₗ[K] K, ∀ x : A, f (x - c x • (1 : A)) = 0)
    (h1 : f 1 ≠ 0) : Determined (compMu (LinearMap.mul K A) f) := by
  obtain ⟨c, hc⟩ := hc
  intro V _ _ φ hφ
  have hφ' : ∀ x y : A, f (x * y) = 0 → φ x y = 0 := fun x y h => hφ x y (by simpa using h)
  have hleft : ∀ n : A, f n = 0 → ∀ y : A, φ n y = 0 := fun n hn y => hφ' n y (hN n hn y).1
  have hright : ∀ n : A, f n = 0 → ∀ y : A, φ y n = 0 := fun n hn y => hφ' y n (hN n hn y).2
  have hB : ∀ y : A, φ 1 y = c y • φ 1 1 := by
    intro y
    have hy : y - c y • (1 : A) + c y • 1 = y := sub_add_cancel _ _
    calc φ 1 y = φ 1 ((y - c y • 1) + c y • 1) := by rw [hy]
      _ = φ 1 (y - c y • 1) + φ 1 (c y • 1) := by rw [map_add]
      _ = 0 + c y • φ 1 1 := by rw [hright _ (hc y) 1, map_smul]
      _ = c y • φ 1 1 := zero_add _
  have hC : ∀ x y : A, φ x y = (c x * c y) • φ 1 1 := by
    intro x y
    have hx : x - c x • (1 : A) + c x • 1 = x := sub_add_cancel _ _
    calc φ x y = φ ((x - c x • 1) + c x • 1) y := by rw [hx]
      _ = φ (x - c x • 1) y + φ (c x • 1) y := by rw [map_add, LinearMap.add_apply]
      _ = 0 + c x • φ 1 y := by rw [hleft _ (hc x) y, map_smul, LinearMap.smul_apply]
      _ = c x • φ 1 y := zero_add _
      _ = c x • (c y • φ 1 1) := by rw [hB y]
      _ = (c x * c y) • φ 1 1 := by rw [smul_smul]
  have hD : ∀ y : A, f y = c y • f 1 := by
    intro y
    have hy : y - c y • (1 : A) + c y • 1 = y := sub_add_cancel _ _
    calc f y = f ((y - c y • 1) + c y • 1) := by rw [hy]
      _ = f (y - c y • 1) + f (c y • 1) := by rw [map_add]
      _ = 0 + c y • f 1 := by rw [hc y, map_smul]
      _ = c y • f 1 := zero_add _
  have hE : ∀ x y : A, f (x * y) = (c x * c y) • f 1 := by
    intro x y
    have hxy : x * y = (x - c x • 1) * y + c x • y := by
      rw [sub_mul, smul_mul_assoc, one_mul]
      abel
    calc f (x * y) = f ((x - c x • 1) * y + c x • y) := by rw [hxy]
      _ = f ((x - c x • 1) * y) + f (c x • y) := by rw [map_add]
      _ = 0 + c x • f y := by rw [(hN _ (hc x) y).1, map_smul]
      _ = c x • f y := zero_add _
      _ = c x • (c y • f 1) := by rw [hD y]
      _ = (c x * c y) • f 1 := by rw [smul_smul]
  have hex : ∃ ℓ : A →ₗ[K] K, ℓ (f 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    have hmem : f 1 ∈ (⊥ : Submodule K A) := by
      rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (⊥ : Submodule K A) (f 1)]
      intro ℓ _
      exact hcon ℓ
    simpa using hmem
  obtain ⟨ℓ, hℓ⟩ := hex
  let g : A →ₗ[K] K := (ℓ (f 1))⁻¹ • ℓ
  have hg : g (f 1) = 1 := by
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ]
  let ψ : A →ₗ[K] V :=
    { toFun := fun z => g z • φ 1 1
      map_add' := by intro a b; rw [map_add, add_smul]
      map_smul' := by
        intro a z
        rw [map_smul, smul_eq_mul]
        exact mul_smul a (g z) (φ 1 1) }
  refine ⟨ψ, ?_⟩
  intro x y
  have hgE : g (f (x * y)) = c x * c y := by
    rw [hE x y, map_smul, hg, smul_eq_mul, mul_one]
  have hψapp : ψ (compMu (LinearMap.mul K A) f x y) = g (f (x * y)) • (φ 1 1) := rfl
  rw [hψapp, hgE, hC x y]

/-- When `f 1 = 0`, the remaining hypotheses of `thm:codim` force `f = 0`, so the conclusion
still holds: the hypothesis `f 1 ≠ 0` is not needed for the statement. -/
theorem codim_determined_of_f_one_zero (f : A →ₗ[K] A)
    (hc : ∃ c : A →ₗ[K] K, ∀ x : A, f (x - c x • (1 : A)) = 0) (h1 : f 1 = 0) :
    Determined (compMu (LinearMap.mul K A) f) := by
  obtain ⟨c, hc⟩ := hc
  have hf0 : f = 0 := by
    ext x
    have hx : x = (x - c x • 1) + c x • 1 := (sub_add_cancel _ _).symm
    rw [hx, map_add, hc x, map_smul, h1, smul_zero, zero_add, LinearMap.zero_apply]
  rw [hf0]
  exact determined_zero

/-! ### The twisted product -/

/-- The twisted product `(x, y) ↦ x * y + α y * α x` as a bilinear map. -/
noncomputable def twistMu (α : A →ₗ[K] A) : A →ₗ[K] A →ₗ[K] A :=
  LinearMap.mk₂ K (fun x y => x * y + α y * α x)
    (fun x₁ x₂ y => by rw [map_add]; noncomm_ring)
    (fun c x y => by simp [map_smul])
    (fun x y₁ y₂ => by rw [map_add]; noncomm_ring)
    (fun c x y => by simp [map_smul])

@[simp]
theorem twistMu_apply (α : A →ₗ[K] A) (x y : A) : twistMu α x y = x * y + α y * α x :=
  rfl

/-- If `α` reverses products, the twisted product is `(id + α) (x * y)`. No commutativity and no
unitality of `α` is needed. -/
theorem twistMu_eq_compMu_of_anti (α : A →ₗ[K] A) (hα : ∀ x y : A, α (x * y) = α y * α x) :
    twistMu α = compMu (LinearMap.mul K A) (LinearMap.id + α) := by
  ext x y
  rw [twistMu_apply, compMu_apply, LinearMap.add_apply, LinearMap.id_apply, ← hα]
  rfl

/-- **`cor:anti`**: if `A` is a zpd algebra and `α` reverses products, then `A` is determined
by the twisted product `x * y + α y * α x`. No commutativity hypothesis. -/
theorem anti_twisted_determined (h : ZeroProductDetermined K A) (α : A →ₗ[K] A)
    (hα : ∀ x y : A, α (x * y) = α y * α x) : Determined (twistMu α) := by
  rw [twistMu_eq_compMu_of_anti α hα]
  exact determined_comp_of_right_id _ h _ 1 (fun b => mul_one b)

/-- **`cor:twisted`**: if `A` is a commutative zpd algebra and `α` is multiplicative, then `A`
is determined by the twisted product `x * y + α y * α x`. -/
theorem twisted_determined (hcomm : ∀ x y : A, x * y = y * x) (h : ZeroProductDetermined K A)
    (α : A →ₗ[K] A) (hα : ∀ x y : A, α (x * y) = α x * α y) : Determined (twistMu α) := by
  have hanti : ∀ x y : A, α (x * y) = α y * α x := by
    intro x y
    rw [hα, hcomm (α y) (α x)]
  exact anti_twisted_determined h α hanti

end Algebra

end ZpdCore

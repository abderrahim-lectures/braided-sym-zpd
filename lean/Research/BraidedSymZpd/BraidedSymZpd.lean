/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

public import ZpdCore.Zpd
public import Mathlib.Algebra.DualNumber

/-!
# Algebras determined by a braided-symmetric product

This file formalises the paper "Algebras Determined by a Braided-Symmetric Product". The general
theory — `Determined`, the criterion `cor:criterion`, `thm:zpd-fxy`, `prop:injective`,
`cor:identity`, `thm:codim`, `cor:twisted` and `cor:anti` — is proved in `ZpdCore.Zpd` with the
paper's hypotheses. This file adds the results that mention the symmetrized products explicitly.

## Main results

* `BraidedSymZpd.preserving`: `rem:preserving`, zero-product-preserving maps carried over to `μ`.
* `BraidedSymZpd.derivation`: `rem:derivations`, the same for derivations.
* `BraidedSymZpd.dualAlpha`: the involution `a + bε ↦ a - bε` of `ex:dual`.
* `BraidedSymZpd.dualNumbers_determined`: the dual numbers are determined by the twisted
  product (`ex:dual`, via `thm:codim`).
* `BraidedSymZpd.dualNumbers_not_zpd`: the dual numbers are not zpd.
* `BraidedSymZpd.twistMu_conjByUnit`: `rem:inner`, the twisted product of an inner automorphism
  is a Jordan product in disguise.

The numerical content of `prop:matrix` is checked in `Research.BraidedSymZpd.M2F3`.
-/

@[expose] public section

open TensorProduct

namespace BraidedSymZpd

open ZpdCore

universe u

/-! ## `rem:preserving` and `rem:derivations` -/

variable {K : Type u} [Field K] {A : Type u} [AddCommGroup A] [Module K A]

/-- **`rem:preserving`**: if `A` is determined by `μ` and `T` sends `μ`-zero pairs to zero
products, then `T (x) T (y)` factors through `μ`. This is the first part of Theorem 7.2 of the
reference, with the product replaced by `μ`. -/
theorem preserving {B : Type u} [Ring B] [Algebra K B] (μ : A →ₗ[K] A →ₗ[K] A)
    (h : Determined μ) (T : A →ₗ[K] B) (hT : ∀ x y : A, μ x y = 0 → T x * T y = 0) :
    ∃ S : A →ₗ[K] B, ∀ x y : A, T x * T y = S (μ x y) :=
  h B (LinearMap.mk₂ K (fun x y => T x * T y)
    (fun x₁ x₂ y => by simp only [map_add, add_mul])
    (fun c x y => by simp only [map_smul, smul_mul_assoc])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun c x y => by simp only [map_smul, mul_smul_comm])) hT

/-- **`rem:derivations`**: if `A` is determined by `μ` and `D` satisfies the derivation
identity on the `μ`-zero pairs, then the Leibniz defect of `D` factors through `μ`. With
`μ = μ_σ` this says that a braided-symmetric derivation is one whose defect vanishes on the
span of the products, as the paper states. -/
theorem derivation (μ : A →ₗ[K] A →ₗ[K] A) (h : Determined μ) (D : A →ₗ[K] A)
    (hD : ∀ x y : A, μ x y = 0 → μ (D x) y + μ x (D y) = 0) :
    ∃ S : A →ₗ[K] A, ∀ x y : A, μ (D x) y + μ x (D y) = S (μ x y) :=
  h A (LinearMap.mk₂ K (fun x y => μ (D x) y + μ x (D y))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply]; abel)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, smul_add])
    (fun x y₁ y₂ => by simp only [map_add]; abel)
    (fun c x y => by simp only [map_smul]; rw [smul_add])) hD

/-! ## `ex:dual`: the dual numbers

`A = K[ε]/(ε²)` with `α (a + bε) = a - bε`. By `thm:codim`, `A` is determined by
`μ_α (x, y) = x * y + α y * α x`, and `A` is not zpd.
-/

section Dual

/-- The projection `a + bε ↦ a` of the dual numbers, as a linear map. -/
def dualFst : DualNumber K →ₗ[K] K where
  toFun x := TrivSqZeroExt.fst x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualFst_apply (x : DualNumber K) : dualFst (K := K) x = TrivSqZeroExt.fst x := rfl

/-- The involution `a + bε ↦ a - bε` of the dual numbers (`ex:dual`). -/
noncomputable def dualAlpha : DualNumber K →ₗ[K] DualNumber K where
  toFun x := TrivSqZeroExt.inl (TrivSqZeroExt.fst x) - TrivSqZeroExt.inr (TrivSqZeroExt.snd x)
  map_add' _ _ := by
    ext <;> simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
    abel
  map_smul' _ _ := by ext <;> simp [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul]

@[simp]
theorem dualAlpha_fst (x : DualNumber K) :
    TrivSqZeroExt.fst (dualAlpha (K := K) x) = TrivSqZeroExt.fst x := by
  simp [dualAlpha]

@[simp]
theorem dualAlpha_snd (x : DualNumber K) :
    TrivSqZeroExt.snd (dualAlpha (K := K) x) = -TrivSqZeroExt.snd x := by
  simp [dualAlpha]

theorem dualAlpha_involutive : Function.Involutive (dualAlpha (K := K)) := by
  intro x
  ext <;> simp

/-- The involution `a + bε ↦ a - bε` is multiplicative. -/
theorem dualAlpha_mul (x y : DualNumber K) :
    dualAlpha (K := K) (x * y) = dualAlpha (K := K) x * dualAlpha (K := K) y := by
  ext
  · simp
  · simp only [dualAlpha_fst, dualAlpha_snd, DualNumber.snd_mul]
    ring

end Dual

/-! ## `ex:dual`, continued: determined but not zpd -/

/-- `f = id + α`, so that `μ_α (x, y) = f (x * y)`. -/
noncomputable def dualF : DualNumber K →ₗ[K] DualNumber K := LinearMap.id + dualAlpha

theorem dualF_fst (x : DualNumber K) :
    TrivSqZeroExt.fst (dualF (K := K) x) = 2 * TrivSqZeroExt.fst x := by
  simp [dualF, two_mul]

theorem dualF_snd (x : DualNumber K) : TrivSqZeroExt.snd (dualF (K := K) x) = 0 := by
  simp [dualF]

theorem dualF_eq_zero_iff (h2 : (2 : K) ≠ 0) (x : DualNumber K) :
    dualF (K := K) x = 0 ↔ TrivSqZeroExt.fst x = 0 := by
  constructor
  · intro h
    have h1 : TrivSqZeroExt.fst (dualF (K := K) x) = 0 := by rw [h, TrivSqZeroExt.fst_zero]
    rw [dualF_fst] at h1
    rcases mul_eq_zero.1 h1 with h' | h'
    · exact absurd h' h2
    · exact h'
  · intro h
    ext
    · rw [dualF_fst, h, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [dualF_snd, TrivSqZeroExt.snd_zero]

/-- The bilinear form `(x, y) ↦ fst x * snd y` used to show that the dual numbers are not zpd. -/
def dualPhi : DualNumber K →ₗ[K] DualNumber K →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => TrivSqZeroExt.fst x * TrivSqZeroExt.snd y)
    (fun x₁ x₂ y => by simp only [TrivSqZeroExt.fst_add, add_mul])
    (fun c x y => by simp only [TrivSqZeroExt.fst_smul, smul_eq_mul, mul_assoc])
    (fun x y₁ y₂ => by simp only [TrivSqZeroExt.snd_add, mul_add])
    (fun c x y => by simp only [TrivSqZeroExt.snd_smul, smul_eq_mul]; ring)

@[simp]
theorem dualPhi_apply (x y : DualNumber K) :
    dualPhi (K := K) x y = TrivSqZeroExt.fst x * TrivSqZeroExt.snd y := rfl

theorem dualPhi_vanishes {x y : DualNumber K} (hxy : x * y = 0) :
    dualPhi (K := K) x y = 0 := by
  have h1 : TrivSqZeroExt.fst x * TrivSqZeroExt.fst y = 0 := by
    have := congrArg TrivSqZeroExt.fst hxy
    simpa using this
  rcases mul_eq_zero.1 h1 with hx | hy
  · rw [dualPhi_apply, hx, zero_mul]
  · have h2 : TrivSqZeroExt.fst x * TrivSqZeroExt.snd y = 0 := by
      have := congrArg TrivSqZeroExt.snd hxy
      simp only [DualNumber.snd_mul, TrivSqZeroExt.snd_zero, hy, mul_zero, add_zero] at this
      exact this
    rw [dualPhi_apply, h2]

/-- **`ex:dual`**: the dual numbers are not zpd. The bilinear form `(x, y) ↦ fst x * snd y`
vanishes on zero products but does not factor through the product, since `1 * ε = ε * 1`. -/
theorem dualNumbers_not_zpd : ¬ ZeroProductDetermined K (DualNumber K) := by
  intro h
  obtain ⟨ψ, hψ⟩ := h K (dualPhi (K := K)) (fun x y hxy => dualPhi_vanishes hxy)
  have h1 : ψ (DualNumber.eps) = 1 := by
    have := (hψ 1 DualNumber.eps).symm
    simpa [dualPhi_apply] using this
  have h2 : ψ (DualNumber.eps) = 0 := by
    have := (hψ DualNumber.eps 1).symm
    simpa [dualPhi_apply] using this
  rw [h1] at h2
  exact one_ne_zero h2

/-- **`ex:dual`**: in characteristic other than `2`, the dual numbers are determined by the
twisted product `μ_α (x, y) = x * y + α y * α x` of the involution `α (a + bε) = a - bε`,
although they are not zpd. -/
theorem dualNumbers_determined_not_zpd (h2 : (2 : K) ≠ 0) :
    Determined (twistMu (dualAlpha (K := K))) ∧ ¬ ZeroProductDetermined K (DualNumber K) := by
  refine ⟨?_, dualNumbers_not_zpd⟩
  have hα : ∀ x y : DualNumber K,
      dualAlpha (K := K) (x * y) = dualAlpha (K := K) y * dualAlpha (K := K) x := by
    intro x y
    rw [dualAlpha_mul]
    exact mul_comm _ _
  rw [twistMu_eq_compMu_of_anti (dualAlpha (K := K)) hα]
  refine codim_determined (dualF (K := K)) ?_ ⟨dualFst (K := K), ?_⟩ ?_
  · intro n hn b
    rw [dualF_eq_zero_iff h2] at hn
    constructor
    · rw [dualF_eq_zero_iff h2]
      simp only [TrivSqZeroExt.fst_mul, hn, zero_mul]
    · rw [dualF_eq_zero_iff h2]
      simp only [TrivSqZeroExt.fst_mul, hn, mul_zero]
  · intro x
    rw [dualF_eq_zero_iff h2]
    simp only [dualFst_apply, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_smul, smul_eq_mul,
      TrivSqZeroExt.fst_one, mul_one, sub_self]
  · intro h
    have := congrArg TrivSqZeroExt.fst h
    rw [dualF_fst, TrivSqZeroExt.fst_one, mul_one, TrivSqZeroExt.fst_zero] at this
    exact h2 this

/-! ## `rem:inner`: an inner twisted product is a Jordan product in disguise -/

section Inner

variable {R : Type u} [Ring R] [Algebra K R]

/-- Conjugation `x ↦ D * x * D⁻¹` by a unit, as a linear map. -/
def conjByUnit (D : Rˣ) : R →ₗ[K] R where
  toFun x := ↑D * x * ↑D⁻¹
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' c x := by simp [mul_assoc]

theorem conjByUnit_apply (D : Rˣ) (x : R) :
    conjByUnit (K := K) D x = ↑D * x * ↑D⁻¹ := rfl

theorem conjByUnit_mul (D : Rˣ) (x y : R) :
    conjByUnit (K := K) D (x * y) = conjByUnit (K := K) D x * conjByUnit (K := K) D y := by
  simp only [conjByUnit_apply, mul_assoc]
  rw [← mul_assoc (↑D⁻¹) (↑D) (y * ↑D⁻¹), Units.inv_mul, one_mul]

/-- **`rem:inner`**: for an inner `α = conj D`, the twisted product of `x` and `y` is the Jordan
product of `x * D⁻¹` and `D * y`. -/
theorem twistMu_conjByUnit (D : Rˣ) (x y : R) :
    twistMu (conjByUnit (K := K) D) x y =
      (x * ↑D⁻¹) * (↑D * y) + (↑D * y) * (x * ↑D⁻¹) := by
  rw [twistMu_apply, ← conjByUnit_mul]
  simp only [conjByUnit_apply, mul_assoc]
  rw [← mul_assoc (↑D⁻¹) (↑D) y, Units.inv_mul, one_mul]

end Inner

end BraidedSymZpd

/-! ## Axiom audit

Every declaration below is checked to depend only on Lean's three standard axioms. -/

#print axioms ZpdCore.determined_iff
#print axioms ZpdCore.determined_comp_of_right_id
#print axioms ZpdCore.determined_of_injective_comp
#print axioms ZpdCore.identity_determined_iff
#print axioms ZpdCore.jordan_forces_comm
#print axioms ZpdCore.twisted_forces_comm
#print axioms ZpdCore.three_braidings_commutative
#print axioms ZpdCore.codim_determined
#print axioms ZpdCore.twisted_determined
#print axioms ZpdCore.anti_twisted_determined
#print axioms BraidedSymZpd.preserving
#print axioms BraidedSymZpd.derivation
#print axioms BraidedSymZpd.dualAlpha_mul
#print axioms BraidedSymZpd.dualNumbers_not_zpd
#print axioms BraidedSymZpd.dualNumbers_determined_not_zpd
#print axioms BraidedSymZpd.twistMu_conjByUnit

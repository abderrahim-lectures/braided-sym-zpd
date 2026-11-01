/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

public import ZpdCore.Zpd
public import Research.BraidedSymZpd.BraidedSymZpd
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Idempotent-spanned algebras are zero Jordan product determined

An-Li-He (`Zero Jordan product determined algebras`, LAA 475 (2015), Theorem 2.1), the key step
of Bresar's Theorem 3.15 quoted in the paper's `rem:inner`: if `A` is a unital algebra over a
field `K` with `2 ≠ 0` whose idempotents span it linearly, then `A` is zero Jordan product
determined, i.e. `Determined (twistMu LinearMap.id)`, where `twistMu id x y = x * y + y * x`.

The proof is the Peirce computation: for a bilinear `phi` vanishing on the pairs with
`x * y + y * x = 0`, an idempotent `e`, `f = 1 - e` and arbitrary `a`, the Peirce pieces
`a1 = e a e`, `u = e a f`, `v = f a e`, `a0 = f a f` satisfy the zero-product pairs
`(a1, f)`, `(a0, e)`, `(u, 1 - 2e)`, `(v, 1 - 2e)`, which gives
`2 * phi a e = phi (a * e) 1 + phi (e * a) 1`; linearity in the second slot extends this to the
span of the idempotents, and then `phi a b = tau (a * b + b * a)`.

## Main results

* `ZJpd.two_smul_phi_apply_of_idem`: the Peirce identity for one idempotent.
* `ZJpd.two_smul_phi_apply`: the same for every element of the span of the idempotents.
* `ZJpd.determined_twistMu_id`: `Determined (twistMu LinearMap.id)` when the idempotents span.
* `ZJpd.determined_twistMu_conjByUnit`: `Determined (twistMu (conjByUnit D))` for **every** unit
  `D`, by `BraidedSymZpd.determined_twist_conj_iff` (the paper's `rem:inner`).
* `ZJpd.span_idempotents_matrix` and `ZJpd.determined_matrix2`: the case `M2(K)`, hence
  `prop:matrix` for `K = ZMod 3` and the conjugation by `diag (1, -1)`, with no enumeration.
-/

open TensorProduct

open ZpdCore

namespace ZJpd

universe u

section Core

variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {V : Type u} [AddCommGroup V] [Module K V]

/-- The Peirce computation for a single idempotent: a bilinear map vanishing on Jordan-zero pairs
is `1`-balanced at every idempotent. -/
theorem two_smul_phi_apply_of_idem {φ : A →ₗ[K] A →ₗ[K] V}
    (hφ : ∀ x y : A, x * y + y * x = 0 → φ x y = 0) {e : A} (he : e * e = e) (a : A) :
    (2 : K) • φ a e = φ (a * e) 1 + φ (e * a) 1 := by
  set f : A := 1 - e with hf
  have hfe : f * e = 0 := by rw [hf, sub_mul, one_mul, he, sub_self]
  have hef : e * f = 0 := by rw [hf, mul_sub, mul_one, he, sub_self]
  have he1 : e + f = 1 := by rw [hf, add_sub_cancel]
  set a1 : A := e * a * e with ha1
  set u : A := e * a * f with hu
  set v : A := f * a * e with hv
  set a0 : A := f * a * f with ha0
  have hdec : a = a1 + u + v + a0 := by
    simp only [ha1, hu, hv, ha0, hf]
    noncomm_ring
  have hae : a * e = a1 + v := by
    simp only [ha1, hv]
    rw [← add_mul, ← add_mul, he1, one_mul]
  have hea : e * a = a1 + u := by
    simp only [ha1, hu]
    rw [← mul_add, he1, mul_one]
  have h1 : a1 * f + f * a1 = 0 := by
    have hl : a1 * f = 0 := by
      simp only [ha1]
      rw [mul_assoc (e * a) e f, hef, mul_zero]
    have hr : f * a1 = 0 := by
      simp only [ha1]
      rw [← mul_assoc f (e * a) e, ← mul_assoc f e a, hfe, zero_mul, zero_mul]
    rw [hl, hr, add_zero]
  have h0 : a0 * e + e * a0 = 0 := by
    have hl : a0 * e = 0 := by
      simp only [ha0]
      rw [mul_assoc (f * a) f e, hfe, mul_zero]
    have hr : e * a0 = 0 := by
      simp only [ha0]
      rw [← mul_assoc e (f * a) f, ← mul_assoc e f a, hef, zero_mul, zero_mul]
    rw [hl, hr, add_zero]
  have hue : u * e = 0 := by
    simp only [hu]
    rw [mul_assoc (e * a) f e, hfe, mul_zero]
  have heu : e * u = u := by
    simp only [hu]
    rw [mul_assoc e a f, ← mul_assoc e e (a * f), he, ← mul_assoc e a f]
  have hve : v * e = v := by
    simp only [hv]
    rw [mul_assoc (f * a) e e, he]
  have hev : e * v = 0 := by
    simp only [hv]
    rw [mul_assoc f a e, ← mul_assoc e f (a * e), hef, zero_mul]
  have hu2 : u * (2 * e) = 0 := by
    rw [two_mul, mul_add, hue, add_zero]
  have h2eu : (2 * e) * u = u + u := by
    rw [two_mul, add_mul, heu]
  have hu' : u * (1 - 2 * e) + (1 - 2 * e) * u = 0 := by
    rw [mul_sub, mul_one, hu2, sub_zero, sub_mul, one_mul, h2eu]
    abel
  have hv2 : v * (2 * e) = v + v := by
    rw [two_mul, mul_add, hve]
  have h2ev : (2 * e) * v = 0 := by
    rw [two_mul, add_mul, hev, add_zero]
  have hv' : v * (1 - 2 * e) + (1 - 2 * e) * v = 0 := by
    rw [mul_sub, mul_one, hv2, sub_mul, one_mul, h2ev]
    abel
  have h2A : (2 : A) * e = (2 : K) • e := by rw [two_mul, two_smul]
  have z1 : φ a1 1 = φ a1 e := by
    have h := hφ a1 f h1
    rw [hf, map_sub, sub_eq_zero] at h
    exact h
  have z0 : φ a0 e = 0 := hφ a0 e h0
  have zu : (2 : K) • φ u e = φ u 1 := by
    have h := hφ u (1 - 2 * e) hu'
    rw [map_sub, h2A, map_smul, sub_eq_zero] at h
    exact h.symm
  have zv : (2 : K) • φ v e = φ v 1 := by
    have h := hφ v (1 - 2 * e) hv'
    rw [map_sub, h2A, map_smul, sub_eq_zero] at h
    exact h.symm
  have hz1 : (2 : K) • φ a1 e = φ a1 1 + φ a1 1 := by rw [two_smul, z1]
  have hz0 : (2 : K) • φ a0 e = 0 := by rw [z0, smul_zero]
  calc (2 : K) • φ a e
      = (2 : K) • φ (a1 + u + v + a0) e := by rw [hdec]
    _ = (2 : K) • (φ a1 e + φ u e + φ v e + φ a0 e) := by simp
    _ = (2 : K) • φ a1 e + (2 : K) • φ u e + (2 : K) • φ v e + (2 : K) • φ a0 e := by
        rw [smul_add, smul_add, smul_add]
    _ = (φ a1 1 + φ a1 1) + φ u 1 + φ v 1 + 0 := by rw [hz1, zu, zv, hz0]
    _ = φ (a * e) 1 + φ (e * a) 1 := by
        rw [hae, hea]
        simp only [map_add, LinearMap.add_apply]
        abel

/-- The Peirce identity for every element of the linear span of the idempotents. -/
theorem two_smul_phi_apply {φ : A →ₗ[K] A →ₗ[K] V}
    (hφ : ∀ x y : A, x * y + y * x = 0 → φ x y = 0) {b : A}
    (hb : b ∈ Submodule.span K {e : A | e * e = e}) (a : A) :
    (2 : K) • φ a b = φ (a * b) 1 + φ (b * a) 1 := by
  induction hb using Submodule.span_induction with
  | mem e he => exact two_smul_phi_apply_of_idem hφ he a
  | zero => simp
  | add x y _ _ ihx ihy =>
      rw [map_add, smul_add, ihx, ihy, mul_add, add_mul]
      simp only [map_add, LinearMap.add_apply]
      abel
  | smul c x _ ih =>
      rw [LinearMap.map_smul, smul_comm (2 : K) c, ih, smul_add, Algebra.smul_mul_assoc,
        map_smul, LinearMap.smul_apply, Algebra.mul_smul_comm, map_smul, LinearMap.smul_apply]

/-- **An-Li-He / Bresar, zero Jordan product determined form.** A unital algebra over a field
with `2 ≠ 0` whose idempotents span it linearly is determined by its symmetrised product
`x * y + y * x`. -/
theorem determined_twistMu_id (h2 : (2 : K) ≠ 0)
    (hA : Submodule.span K {e : A | e * e = e} = ⊤) :
    Determined (twistMu (LinearMap.id : A →ₗ[K] A)) := by
  intro V _ _ φ hφ
  refine ⟨(2 : K)⁻¹ • φ.flip 1, fun a b => ?_⟩
  have hb : b ∈ Submodule.span K {e : A | e * e = e} := by rw [hA]; exact Submodule.mem_top
  have key := two_smul_phi_apply hφ hb a
  show φ a b = ((2 : K)⁻¹ • φ.flip 1) (twistMu (LinearMap.id : A →ₗ[K] A) a b)
  simp only [twistMu_apply, LinearMap.id_apply, LinearMap.smul_apply, map_add,
    LinearMap.flip_apply]
  rw [← smul_add, ← key, smul_smul, inv_mul_cancel₀ h2, one_smul]

end Core

/-! ## The algebra `M₂(K)` is spanned by its idempotents -/

section Matrix2

variable (K : Type u) [Field K]

/-- The matrix unit `e₁₁`. -/
def m00 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]

/-- The matrix unit `e₂₂`. -/
def m11 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]

/-- The matrix unit `e₁₂`. -/
def m01 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- The matrix unit `e₂₁`. -/
def m10 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

/-- The idempotent `e₁₁ + e₁₂`. -/
def p01 : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 0]

/-- The idempotent `e₁₁ + e₂₁`. -/
def p10 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 0]

theorem idem_m00 : m00 K * m00 K = m00 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m00, Matrix.mul_apply, Fin.sum_univ_two]

theorem idem_m11 : m11 K * m11 K = m11 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m11, Matrix.mul_apply, Fin.sum_univ_two]

theorem idem_p01 : p01 K * p01 K = p01 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p01, Matrix.mul_apply, Fin.sum_univ_two]

theorem idem_p10 : p10 K * p10 K = p10 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p10, Matrix.mul_apply, Fin.sum_univ_two]

theorem m01_eq : m01 K = p01 K - m00 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m01, p01, m00, Matrix.sub_apply]

theorem m10_eq : m10 K = p10 K - m00 K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m10, p10, m00, Matrix.sub_apply]

/-- **`M₂(K)` is spanned by its idempotents**, for every field `K`. -/
theorem span_idempotents_eq_top :
    Submodule.span K {e : Matrix (Fin 2) (Fin 2) K | e * e = e} = ⊤ := by
  have h00 : m00 K ∈ Submodule.span K {e : Matrix (Fin 2) (Fin 2) K | e * e = e} :=
    Submodule.subset_span (idem_m00 K)
  have h11 : m11 K ∈ Submodule.span K {e : Matrix (Fin 2) (Fin 2) K | e * e = e} :=
    Submodule.subset_span (idem_m11 K)
  have h01 : m01 K ∈ Submodule.span K {e : Matrix (Fin 2) (Fin 2) K | e * e = e} := by
    rw [m01_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span (idem_p01 K)) h00
  have h10 : m10 K ∈ Submodule.span K {e : Matrix (Fin 2) (Fin 2) K | e * e = e} := by
    rw [m10_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span (idem_p10 K)) h00
  rw [eq_top_iff]
  intro M _
  have hM : M = M 0 0 • m00 K + M 0 1 • m01 K + M 1 0 • m10 K + M 1 1 • m11 K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [m00, m01, m10, m11, Matrix.add_apply]
  rw [hM]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h00) (Submodule.smul_mem _ _ h01))
    (Submodule.smul_mem _ _ h10)) (Submodule.smul_mem _ _ h11)

/-- `M₂(K)` is determined by its symmetrised product, in characteristic `≠ 2`. -/
theorem determined_twistMu_id_matrix (h2 : (2 : K) ≠ 0) :
    Determined (twistMu (LinearMap.id :
      Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)) :=
  determined_twistMu_id h2 (span_idempotents_eq_top K)

/-- **`rem:inner` for `M₂(K)`**: the twisted product of the conjugation by **any** unit `D`
determines the algebra, in characteristic `≠ 2`. -/
theorem determined_twistMu_conjByUnit (h2 : (2 : K) ≠ 0) (D : (Matrix (Fin 2) (Fin 2) K)ˣ) :
    Determined (twistMu (BraidedSymZpd.conjByUnit (K := K) D)) :=
  (BraidedSymZpd.determined_twist_conj_iff (K := K) D).mpr
    (determined_twistMu_id_matrix K h2)

end Matrix2

/-! ## `prop:matrix`: the case `M₂(𝔽₃)` and `α = conj (diag (1, -1))` -/

/-- The unit `diag (1, -1)` of `M₂(𝔽₃)`. -/
def diagUnit : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by decide
  inv_val := by decide

/-- The conjugation by `diag (1, -1)`, written out. -/
theorem conjByUnit_diagUnit_apply (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    BraidedSymZpd.conjByUnit (K := ZMod 3) diagUnit x
      = !![1, 0; 0, -1] * x * !![1, 0; 0, -1] := rfl

/-- **`prop:matrix`**: `M₂(𝔽₃)` is determined by the twisted product
`x * y + α (y * x)` of the conjugation `α` by `diag (1, -1)`. -/
theorem determined_matrix2 :
    Determined (twistMu (BraidedSymZpd.conjByUnit (K := ZMod 3) diagUnit)) :=
  determined_twistMu_conjByUnit (ZMod 3) (by decide) diagUnit

/-! ## The paper's `μ_α (x, y) = x * y + α (y * x)` for a multiplicative inner twist -/

section ConjFormula

variable {K : Type u} [Field K]
variable {R : Type u} [Ring R] [Algebra K R]

/-- For a multiplicative `α = conj D`, the symmetrised twisted product is the paper's
`μ_α (x, y) = x * y + α (y * x)`. -/
theorem twistMu_conjByUnit_apply (D : Rˣ) (x y : R) :
    twistMu (BraidedSymZpd.conjByUnit (K := K) D) x y
      = x * y + BraidedSymZpd.conjByUnit (K := K) D (y * x) := by
  rw [twistMu_apply, ← BraidedSymZpd.conjByUnit_mul]

end ConjFormula

/-! ## Axiom audit

No `sorry`, no `native_decide`, no added axiom: each declaration depends only on Lean's three
standard axioms. -/

#print axioms ZJpd.two_smul_phi_apply_of_idem
#print axioms ZJpd.two_smul_phi_apply
#print axioms ZJpd.determined_twistMu_id
#print axioms ZJpd.span_idempotents_eq_top
#print axioms ZJpd.determined_twistMu_id_matrix
#print axioms ZJpd.determined_twistMu_conjByUnit
#print axioms ZJpd.determined_matrix2

end ZJpd

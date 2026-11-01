/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

public import ZpdCore.Zpd
public import Research.BraidedSymZpd.BraidedSymZpd
public import Research.BraidedSymZpd.ZJpd
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The finrank bridge for `prop:matrix`

The paper's Proposition `prop:matrix` is proved by counting dimensions: for `A = M₂(𝔽₃)` and
`α` the conjugation by `diag (1, -1)`, the linearisation `μ̄_α` has rank `4`, so its kernel has
dimension `16 - 4 = 12`, and the `417` pairs `(x, y)` with `μ_α (x, y) = 0` span a subspace
of dimension `12`. Equal dimensions together with `Z_μ ⊆ ker μ̄` give `Z_μ = ker μ̄`, and by the
criterion `cor:criterion` this is the determination of `A` by `μ_α`.

`Research.BraidedSymZpd.M2F3` checks the three numbers by kernel evaluation. This file closes the
gap between those numbers and the statement: it exhibits

* twelve zero-pair tensors `x ⊗ y` and a pivot matrix whose inverse is checked by `decide`, which
  proves that they are linearly independent, hence `12 ≤ finrank Z_μ`;
* four independent elements `μ (x) (y)` of the range, hence `4 ≤ finrank (range μ̄)`;

and then rank-nullity, `Module.finrank_tensorProduct` and `Submodule.eq_of_le_of_finrank_eq` give
`Z_μ = ker μ̄` and finally `ZpdCore.Determined μ`, which is `prop:matrix`.

Nothing here is `sorry`-based or an added axiom: the pivots are `decide`-checked and the
`#print axioms` block at the end reports only Lean's standard axioms.
-/

@[expose] public section

open TensorProduct
open scoped TensorProduct

namespace BraidedSymZpd

namespace M2F3Bridge


abbrev K := ZMod 3
abbrev A := Matrix (Fin 2) (Fin 2) K

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example : Field K := inferInstance

def alpha (x : A) : A := fun i j => if i = j then x i j else -x i j

def alphaLM : A →ₗ[K] A where
  toFun := alpha
  map_add' x y := by
    ext i j
    by_cases h : i = j <;> simp [alpha, h, add_comm]
  map_smul' c x := by
    ext i j
    by_cases h : i = j <;> simp [alpha, h]

/-- The matrix `diag (1, -1)`. -/
def diagPM : A := !![1, 0; 0, -1]

theorem diagPM_mul_self : diagPM * diagPM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- `alpha` is the conjugation by `diag (1, -1)`, as in `ex:dual` and `prop:matrix`. -/
theorem alpha_eq (x : A) : alpha x = diagPM * x * diagPM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alpha, diagPM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- `alpha` is multiplicative: conjugation by `diag (1, -1)`. -/
theorem alpha_mul (x y : A) : alpha (x * y) = alpha x * alpha y := by
  have key : diagPM * x * y * diagPM = (diagPM * x * diagPM) * (diagPM * y * diagPM) := by
    rw [show (diagPM * x * diagPM) * (diagPM * y * diagPM) =
      diagPM * x * (diagPM * diagPM) * y * diagPM from by noncomm_ring]
    rw [diagPM_mul_self]
    noncomm_ring
  calc alpha (x * y) = diagPM * (x * y) * diagPM := alpha_eq _
    _ = diagPM * x * y * diagPM := by noncomm_ring
    _ = (diagPM * x * diagPM) * (diagPM * y * diagPM) := key
    _ = alpha x * alpha y := by simp only [alpha_eq]

/-- `alpha` is an involution. -/
theorem alpha_involutive : Function.Involutive alpha := by
  intro x
  calc alpha (alpha x) = diagPM * (diagPM * x * diagPM) * diagPM := by rw [alpha_eq, alpha_eq]
    _ = (diagPM * diagPM) * x * (diagPM * diagPM) := by noncomm_ring
    _ = x := by rw [diagPM_mul_self]; simp

def ent (i j : Fin 2) : A →ₗ[K] K where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ent_apply (i j : Fin 2) (x : A) : ent i j x = x i j := rfl

def dec (k : Fin 4) : Fin 2 × Fin 2 :=
  ![(0, 0), (0, 1), (1, 0), (1, 1)] k

noncomputable def coord (k l : Fin 4) : (A ⊗[K] A) →ₗ[K] K :=
  TensorProduct.lift (LinearMap.mk₂ K
    (fun x y => ent (dec k).1 (dec k).2 x * ent (dec l).1 (dec l).2 y)
    (fun x₁ x₂ y => by simp only [map_add, add_mul])
    (fun c x y => by simp only [map_smul, smul_eq_mul, mul_assoc])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun c x y => by simp only [map_smul, smul_eq_mul]; ring))

@[simp] theorem coord_tmul (k l : Fin 4) (x y : A) :
    coord k l (x ⊗ₜ[K] y) = ent (dec k).1 (dec k).2 x * ent (dec l).1 (dec l).2 y := rfl


/-- A `2 × 2` matrix from its four entries. -/
def mat (a b c d : K) : A := !![a, b; c, d]

/-- The left factors of the twelve zero-pair tensors. -/
def xT : Fin 12 → A :=
  ![mat 2 0 1 2, mat 0 1 0 2, mat 2 2 0 2, mat 1 0 2 1, mat 0 0 1 0, mat 0 0 2 2,
    mat 0 1 0 0, mat 2 1 0 0, mat 0 0 0 1, mat 0 2 0 0, mat 2 0 0 0, mat 0 0 1 0]

/-- The right factors of the twelve zero-pair tensors. -/
def yT : Fin 12 → A :=
  ![mat 2 1 2 2, mat 2 2 0 0, mat 1 0 1 1, mat 0 0 2 0, mat 2 0 0 2, mat 1 0 2 0,
    mat 1 2 0 1, mat 0 2 0 2, mat 1 0 0 0, mat 0 2 0 0, mat 0 0 0 1, mat 0 0 1 0]

/-- The first entry index of the twelve pivots. -/
def posK : Fin 12 → Fin 4 := ![2, 3, 3, 0, 2, 2, 1, 1, 3, 1, 0, 2]

/-- The second entry index of the twelve pivots. -/
def posL : Fin 12 → Fin 4 := ![1, 1, 3, 2, 3, 0, 0, 3, 0, 1, 3, 2]

/-- The left inverse of the pivot matrix. -/
def nInv : Matrix (Fin 12) (Fin 12) K :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0;
    2, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0;
    2, 2, 2, 0, 1, 2, 0, 0, 1, 0, 0, 0; 1, 0, 2, 0, 0, 0, 2, 2, 0, 1, 0, 0;
    1, 1, 1, 0, 0, 0, 1, 2, 0, 0, 2, 0; 1, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 1]

/-- The pivot matrix of the twelve tensors. -/
def piv : Matrix (Fin 12) (Fin 12) K :=
  Matrix.of fun i j => ent (dec (posK i)).1 (dec (posK i)).2 (xT j) *
    ent (dec (posL i)).1 (dec (posL i)).2 (yT j)

theorem cert : nInv * piv = 1 := by decide

theorem linearIndependent_of_cert {n : Nat} (v : Fin n → A ⊗[K] A) (pk pl : Fin n → Fin 4)
    (Ninv : Matrix (Fin n) (Fin n) K)
    (h : Ninv * Matrix.of (fun i j => coord (pk i) (pl i) (v j)) = 1) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set M : Matrix (Fin n) (Fin n) K := Matrix.of (fun i j => coord (pk i) (pl i) (v j)) with hM
  have hmul : M.mulVec c = 0 := by
    ext i
    have h1 := congrArg (coord (pk i) (pl i)) hc
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.map_zero] at h1
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using h1
  have hc0 : c = 0 := by
    calc c = (1 : Matrix (Fin n) (Fin n) K).mulVec c := by rw [Matrix.one_mulVec]
      _ = (Ninv * M).mulVec c := by rw [h]
      _ = Ninv.mulVec (M.mulVec c) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  intro i
  exact congrFun hc0 i

theorem linearIndependent_tensors :
    LinearIndependent K (fun j : Fin 12 => xT j ⊗ₜ[K] yT j) := by
  have h : nInv * Matrix.of (fun i j : Fin 12 =>
      coord (posK i) (posL i) (xT j ⊗ₜ[K] yT j)) = 1 := by
    rw [show (Matrix.of fun i j : Fin 12 => coord (posK i) (posL i) (xT j ⊗ₜ[K] yT j)) =
        piv from by ext i j; exact coord_tmul _ _ _ _]
    exact cert
  exact linearIndependent_of_cert _ posK posL nInv h


/-- `diag (1, -1)` as a unit of `M₂(𝔽₃)`; it is its own inverse. -/
def diagUnit : Aˣ where
  val := diagPM
  inv := diagPM
  val_inv := diagPM_mul_self
  inv_val := diagPM_mul_self

/-- The paper's `α` of `prop:matrix` is the inner automorphism of the paper's `rem:inner`: the
conjugation by the unit `diag (1, -1)`. This is what identifies the two proofs of `prop:matrix` in
this repository — the finrank proof below and `ZJpd.determined_matrix2` are both about
`twistMu (conjByUnit diagUnit)`. -/
theorem conjByUnit_diagUnit :
    BraidedSymZpd.conjByUnit (K := K) diagUnit = alphaLM := by
  have hv : (↑diagUnit : A) = diagPM := rfl
  have hi : (↑diagUnit⁻¹ : A) = diagPM := rfl
  refine LinearMap.ext fun x => ?_
  rw [BraidedSymZpd.conjByUnit_apply, hv, hi, ← alpha_eq]
  rfl

/-- The two descriptions of the unit `diag (1, -1)`: this file's and `ZJpd`'s. -/
theorem diagUnit_eq_zjpd : diagUnit = ZJpd.diagUnit := Units.ext rfl

/-- The twisted product of the paper: `μ (x, y) = x * y + α y * α x`. -/
noncomputable def mu : A →ₗ[K] A →ₗ[K] A := ZpdCore.twistMu alphaLM

theorem mu_eq_twistMu_conjByUnit :
    mu = ZpdCore.twistMu (BraidedSymZpd.conjByUnit (K := K) diagUnit) := by
  rw [mu, conjByUnit_diagUnit]

@[simp] theorem mu_apply (x y : A) : mu x y = x * y + alphaLM y * alphaLM x := rfl

/-- The paper's form of the twisted product, `μ_α (x, y) = x * y + α (y * x)`: it agrees with
`twistMu` because `α` is multiplicative. -/
theorem mu_apply_paper (x y : A) : mu x y = x * y + alpha (y * x) := by
  rw [mu_apply]
  show x * y + alpha y * alpha x = x * y + alpha (y * x)
  rw [alpha_mul]

theorem mu_zero (j : Fin 12) : mu (xT j) (yT j) = 0 := by
  fin_cases j <;> simp [mu_apply, alphaLM] <;> decide

theorem tensors_mem : ∀ j : Fin 12, xT j ⊗ₜ[K] yT j ∈ ZpdCore.Zmu mu :=
  fun j => ZpdCore.tmul_mem_Zmu (mu_zero j)


/-- The basis of matrix units, and the induced basis of `A ⊗ A`. -/
noncomputable def bA : Module.Basis (Fin 2 × Fin 2) K A := Matrix.stdBasis K (Fin 2) (Fin 2)

noncomputable def bT : Module.Basis ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) K (A ⊗[K] A) :=
  bA.tensorProduct bA

instance : FiniteDimensional K (A ⊗[K] A) :=
  Module.Basis.finiteDimensional_of_finite bT

theorem finrank_A : Module.finrank K A = 4 := by
  rw [Module.finrank_matrix]
  norm_num

theorem finrank_tensor : Module.finrank K (A ⊗[K] A) = 16 := by
  rw [Module.finrank_tensorProduct, finrank_A]


/-- The four independent elements of the range. -/
def aW : Fin 4 → A := ![mat 1 0 0 0, mat 1 0 0 0, mat 1 0 0 0, mat 0 1 0 0]

def bW : Fin 4 → A := ![mat 1 0 0 0, mat 0 1 0 0, mat 0 0 1 0, mat 0 0 1 0]

def w : Fin 4 → A := ![mat 2 0 0 0, mat 0 1 0 0, mat 0 0 2 0, mat 1 0 0 1]

theorem w_eq (i : Fin 4) : w i = mu (aW i) (bW i) := by
  fin_cases i <;> simp [w, aW, bW, mu_apply, alphaLM] <;> decide

theorem w_indep : LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  decide


theorem twelve_le_finrank_Zmu : 12 ≤ Module.finrank K (ZpdCore.Zmu mu) := by
  have hspan : Submodule.span K (Set.range fun j : Fin 12 => xT j ⊗ₜ[K] yT j) ≤
      ZpdCore.Zmu mu :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr tensors_mem)
  have h1 : Module.finrank K (Submodule.span K (Set.range fun j : Fin 12 =>
      xT j ⊗ₜ[K] yT j)) = 12 := by
    rw [finrank_span_eq_card linearIndependent_tensors]
    simp
  have h2 := Submodule.finrank_mono hspan
  omega

theorem twelve_le_finrank_ker : 12 ≤ Module.finrank K (LinearMap.ker (ZpdCore.muBar mu)) := by
  have h2 := Submodule.finrank_mono (ZpdCore.Zmu_le_ker mu)
  have h1 := twelve_le_finrank_Zmu
  omega

theorem four_le_finrank_range : 4 ≤ Module.finrank K (LinearMap.range (ZpdCore.muBar mu)) := by
  have hspan : Submodule.span K (Set.range w) ≤ LinearMap.range (ZpdCore.muBar mu) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨aW i ⊗ₜ[K] bW i, by rw [ZpdCore.muBar_tmul, w_eq]⟩
  have h := Submodule.finrank_mono hspan
  have h4 : Module.finrank K (Submodule.span K (Set.range w)) = 4 := by
    rw [finrank_span_eq_card w_indep]
    simp
  omega

theorem finrank_range : Module.finrank K (LinearMap.range (ZpdCore.muBar mu)) = 4 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (ZpdCore.muBar mu)
  have h2 := finrank_tensor
  have h3 := twelve_le_finrank_ker
  have h4 := four_le_finrank_range
  omega

theorem finrank_ker : Module.finrank K (LinearMap.ker (ZpdCore.muBar mu)) = 12 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (ZpdCore.muBar mu)
  have h2 := finrank_tensor
  have h3 := finrank_range
  omega

theorem finrank_Zmu : Module.finrank K (ZpdCore.Zmu mu) = 12 := by
  have hle : Module.finrank K (ZpdCore.Zmu mu) ≤
      Module.finrank K (LinearMap.ker (ZpdCore.muBar mu)) :=
    Submodule.finrank_mono (ZpdCore.Zmu_le_ker mu)
  have h1 := twelve_le_finrank_Zmu
  have h3 := finrank_ker
  omega

theorem Zmu_eq_ker : ZpdCore.Zmu mu = LinearMap.ker (ZpdCore.muBar mu) :=
  Submodule.eq_of_le_of_finrank_eq (ZpdCore.Zmu_le_ker mu) (by rw [finrank_Zmu, finrank_ker])

/-- **`prop:matrix`**, as a consequence of the dimension count: `M₂(𝔽₃)` is determined by the
twisted product of the conjugation by `diag (1, -1)`. -/
theorem determined : ZpdCore.Determined mu :=
  (ZpdCore.determined_iff mu).mpr Zmu_eq_ker

/-- **`prop:matrix` again, by the Peirce computation**: the statement of `ZJpd.determined_matrix2`
and the dimension-count statement `determined` are the same statement, so this is a second proof
of `prop:matrix` that does not enumerate the `417` pairs. -/
theorem determined_of_peirce :
    ZpdCore.Determined (ZpdCore.twistMu (BraidedSymZpd.conjByUnit (K := K) ZJpd.diagUnit)) := by
  rw [← diagUnit_eq_zjpd, ← mu_eq_twistMu_conjByUnit]
  exact determined

end M2F3Bridge

end BraidedSymZpd

/-! ## Axiom audit -/

#print axioms BraidedSymZpd.M2F3Bridge.alpha_mul
#print axioms BraidedSymZpd.M2F3Bridge.alpha_involutive
#print axioms BraidedSymZpd.M2F3Bridge.mu_apply_paper
#print axioms BraidedSymZpd.M2F3Bridge.linearIndependent_tensors
#print axioms BraidedSymZpd.M2F3Bridge.w_indep
#print axioms BraidedSymZpd.M2F3Bridge.finrank_range
#print axioms BraidedSymZpd.M2F3Bridge.finrank_ker
#print axioms BraidedSymZpd.M2F3Bridge.Zmu_eq_ker
#print axioms BraidedSymZpd.M2F3Bridge.conjByUnit_diagUnit
#print axioms BraidedSymZpd.M2F3Bridge.mu_eq_twistMu_conjByUnit
#print axioms BraidedSymZpd.M2F3Bridge.determined
#print axioms BraidedSymZpd.M2F3Bridge.determined_of_peirce

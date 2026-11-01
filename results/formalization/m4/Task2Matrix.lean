/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

public import ZpdCore.Zpd
public import Research.BraidedSymZpd.BraidedSymZpd
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
dimension `16 - 4 = 12`, and the `417` pairs `(x, y)` with `μ_α (x, y) = 0` span a subspace of
dimension `12`. Equal dimensions together with `Z_μ ⊆ ker μ̄` give `Z_μ = ker μ̄`, and by the
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


/-- The twisted product of the paper: `μ (x, y) = x * y + α y * α x`. -/
noncomputable def mu : A →ₗ[K] A →ₗ[K] A := ZpdCore.twistMu alphaLM

@[simp] theorem mu_apply (x y : A) : mu x y = x * y + alphaLM y * alphaLM x := rfl

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

end M2F3Bridge

end BraidedSymZpd

/-! ## Axiom audit -/

#print axioms BraidedSymZpd.M2F3Bridge.linearIndependent_tensors
#print axioms BraidedSymZpd.M2F3Bridge.w_indep
#print axioms BraidedSymZpd.M2F3Bridge.finrank_range
#print axioms BraidedSymZpd.M2F3Bridge.finrank_ker
#print axioms BraidedSymZpd.M2F3Bridge.Zmu_eq_ker
#print axioms BraidedSymZpd.M2F3Bridge.determined

/-! ## The paper's own form of `α`, and the reduction to the symmetrised product

`prop:matrix` is stated for the conjugation by `diag (1, -1)`. The linear map `alphaLM` above is
that conjugation: `u = diag (1, -1)` satisfies `u * u = 1`, so `alphaLM x = u * x * u⁻¹`, i.e.
`alphaLM = BraidedSymZpd.conjByUnit D` for the unit `D` with underlying matrix `u`. With
`rem:inner` (`BraidedSymZpd.determined_twist_conj_iff`), the statement for `D` is equivalent to
the statement for the symmetrised (Jordan) product `x * y + y * x`, and hence holds for every
inner conjugation.

The flip identity below records the linearisation of the symmetrised product: it is the product
composed with `id + flip` on `A ⊗[K] A`, where `flip = TensorProduct.comm K A A`. -/

namespace BraidedSymZpd

section Flip

universe v

variable {K : Type v} [Field K] {A : Type v} [Ring A] [Algebra K A]

/-- **The flip identity**: the linearisation of the symmetrised product `x * y + y * x` is the
multiplication composed with `id + flip` on `A ⊗[K] A`, where `flip = TensorProduct.comm K A A`.
Hence `ker μ̄_∘` is the preimage under `id + flip` of `ker ∘̄`. -/
theorem muBar_twist_id_flip (t : A ⊗[K] A) :
    ZpdCore.muBar (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A)) t =
      ZpdCore.muBar (LinearMap.mul K A) t +
        ZpdCore.muBar (LinearMap.mul K A) (TensorProduct.comm K A A t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [ZpdCore.muBar_tmul, ZpdCore.twistMu_apply, LinearMap.id_apply,
      TensorProduct.comm_tmul, LinearMap.mul_apply']
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel

/-- A tensor is killed by the linearisation of the symmetrised product exactly when the product
of the tensor and the product of its flip add up to zero. -/
theorem mem_ker_twist_id_iff (t : A ⊗[K] A) :
    t ∈ LinearMap.ker (ZpdCore.muBar (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A))) ↔
      ZpdCore.muBar (LinearMap.mul K A) t +
        ZpdCore.muBar (LinearMap.mul K A) (TensorProduct.comm K A A t) = 0 := by
  rw [LinearMap.mem_ker, muBar_twist_id_flip]

end Flip

namespace M2F3Bridge

/-- The matrix `diag (1, -1)` of `M₂(𝔽₃)`. -/
def u : A := !![1, 0; 0, -1]

/-- `diag (1, -1)` is the diagonal matrix with entries `1` and `-1`. -/
theorem u_eq_diagonal : u = Matrix.diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u]

/-- `diag (1, -1)` is its own inverse. -/
theorem u_mul_u : u * u = 1 := by decide

/-- `diag (1, -1)` as a unit of `M₂(𝔽₃)`. -/
def D : Aˣ := ⟨u, u, u_mul_u, u_mul_u⟩

@[simp] theorem coe_D : (↑D : A) = u := rfl

@[simp] theorem coe_inv_D : (↑D⁻¹ : A) = u := rfl

/-- Conjugation by `diag (1, -1)` changes the sign of the two off-diagonal entries. -/
theorem alpha_eq_conj (x : A) : alpha x = u * x * u := by
  ext i j
  rw [u_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [alpha]

/-- `alphaLM` is the inner conjugation by the unit `diag (1, -1)`. -/
theorem alphaLM_eq_conjByUnit : conjByUnit (K := K) D = alphaLM := by
  apply LinearMap.ext
  intro x
  rw [conjByUnit_apply, coe_D, coe_inv_D]
  exact (alpha_eq_conj x).symm

end M2F3Bridge

/-- **`prop:matrix`**, in the paper's own form: `M₂(𝔽₃)` is determined by the twisted product
of the conjugation by `diag (1, -1)`, that is by `μ_α (x, y) = x * y + α y * α x` with
`α = conjByUnit diag (1, -1)`. -/
theorem determined_matrix2 :
    ZpdCore.Determined (ZpdCore.twistMu (conjByUnit (K := M2F3Bridge.K) M2F3Bridge.D)) := by
  rw [M2F3Bridge.alphaLM_eq_conjByUnit]
  exact M2F3Bridge.determined

/-- **`rem:inner`**, instantiated: `M₂(𝔽₃)` is determined by the symmetrised (Jordan) product
`x * y + y * x` as well. -/
theorem determined_jordan :
    ZpdCore.Determined (ZpdCore.twistMu
      (LinearMap.id : M2F3Bridge.A →ₗ[M2F3Bridge.K] M2F3Bridge.A)) :=
  (determined_twist_conj_iff (K := M2F3Bridge.K) M2F3Bridge.D).mp determined_matrix2

/-- `prop:matrix` holds for every inner conjugation, not only for `diag (1, -1)`. -/
theorem determined_all_inner (E : M2F3Bridge.Aˣ) :
    ZpdCore.Determined (ZpdCore.twistMu (conjByUnit (K := M2F3Bridge.K) E)) :=
  (determined_twist_conj_iff (K := M2F3Bridge.K) E).mpr determined_jordan

end BraidedSymZpd

/-! ## Axiom audit of the additions -/

#print axioms BraidedSymZpd.muBar_twist_id_flip
#print axioms BraidedSymZpd.mem_ker_twist_id_iff
#print axioms BraidedSymZpd.M2F3Bridge.alphaLM_eq_conjByUnit
#print axioms BraidedSymZpd.determined_matrix2
#print axioms BraidedSymZpd.determined_jordan
#print axioms BraidedSymZpd.determined_all_inner

/-! ## The zero-pair space of the symmetrised product

By definition of the twisted product with `α = id`, the space `Z_∘` of the symmetrised product
`x * y + y * x` is spanned by the tensors `x ⊗ y` whose factors *anticommute*. -/

namespace BraidedSymZpd

section Jordan

universe v

variable {K : Type v} [Field K] {A : Type v} [Ring A] [Algebra K A]

/-- `Z_∘` is spanned by the anticommuting pairs: the pure tensors `x ⊗ y` with
`x * y + y * x = 0`. -/
theorem Zmu_twist_id :
    ZpdCore.Zmu (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A)) =
      Submodule.span K {t : A ⊗[K] A | ∃ x y : A, x * y + y * x = 0 ∧ t = x ⊗ₜ[K] y} := by
  have h : {t : A ⊗[K] A | ∃ x y : A,
        (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A)) x y = 0 ∧ t = x ⊗ₜ[K] y} =
      {t : A ⊗[K] A | ∃ x y : A, x * y + y * x = 0 ∧ t = x ⊗ₜ[K] y} := by
    ext t
    simp only [ZpdCore.twistMu_apply, LinearMap.id_apply]
  rw [ZpdCore.Zmu, h]

end Jordan

end BraidedSymZpd

#print axioms BraidedSymZpd.Zmu_twist_id

/-! ## The flip eigenspaces and `ker μ̄_∘`

The flip `TensorProduct.comm K A A` is an involution, so in characteristic other than `2` every
tensor is the sum of its symmetric part `2⁻¹ • (t + flip t)` and its antisymmetric part
`2⁻¹ • (t - flip t)`. The flip identity then turns `ker μ̄_∘` into a condition on the symmetric
part alone: `μ̄_∘ t = 0` exactly when the product kills `2⁻¹ • (t + flip t)`. This is the
"flip-eigenspace form" of the kernel of the symmetrised product. -/

namespace BraidedSymZpd

section FlipEigenspaces

universe v

variable {K : Type v} [Field K] {A : Type v} [Ring A] [Algebra K A]

/-- The flip is an involution. -/
theorem flip_flip (t : A ⊗[K] A) :
    TensorProduct.comm K A A (TensorProduct.comm K A A t) = t := by
  simp

/-- The symmetrisation `2⁻¹ • (t + flip t)` is flip-invariant. -/
theorem flip_symmetrization (t : A ⊗[K] A) :
    TensorProduct.comm K A A ((2 : K)⁻¹ • (t + TensorProduct.comm K A A t)) =
      (2 : K)⁻¹ • (t + TensorProduct.comm K A A t) := by
  rw [map_smul, map_add, flip_flip]
  congr 1
  abel

/-- The antisymmetrisation `2⁻¹ • (t - flip t)` is anti-invariant. -/
theorem flip_antisymmetrization (t : A ⊗[K] A) :
    TensorProduct.comm K A A ((2 : K)⁻¹ • (t - TensorProduct.comm K A A t)) =
      -((2 : K)⁻¹ • (t - TensorProduct.comm K A A t)) := by
  rw [map_smul, map_sub, flip_flip, smul_sub]
  module

/-- **`ker μ̄_∘` in flip-eigenspace form**: in characteristic other than `2`, a tensor is killed
by the linearisation of the symmetrised product exactly when the product kills its symmetric
part. -/
theorem mem_ker_muBar_twist_id_iff (h2 : (2 : K) ≠ 0) (t : A ⊗[K] A) :
    t ∈ LinearMap.ker (ZpdCore.muBar (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A))) ↔
      ZpdCore.muBar (LinearMap.mul K A)
        ((2 : K)⁻¹ • (t + TensorProduct.comm K A A t)) = 0 := by
  rw [LinearMap.mem_ker, muBar_twist_id_flip, ← map_add, map_smul,
    smul_eq_zero, inv_eq_zero, or_iff_right h2]

/-- The same, as an equality of kernels: `ker μ̄_∘` is the kernel of the product composed with
the symmetrisation `2⁻¹ • (id + flip)`. -/
theorem ker_muBar_twist_id_eq (h2 : (2 : K) ≠ 0) :
    LinearMap.ker (ZpdCore.muBar (ZpdCore.twistMu (LinearMap.id : A →ₗ[K] A))) =
      LinearMap.ker (ZpdCore.muBar (LinearMap.mul K A) ∘ₗ
        ((2 : K)⁻¹ • ((LinearMap.id : (A ⊗[K] A) →ₗ[K] (A ⊗[K] A)) +
          (TensorProduct.comm K A A).toLinearMap))) := by
  ext t
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
  exact mem_ker_muBar_twist_id_iff h2 t

end FlipEigenspaces

end BraidedSymZpd

#print axioms BraidedSymZpd.flip_flip
#print axioms BraidedSymZpd.flip_symmetrization
#print axioms BraidedSymZpd.flip_antisymmetrization
#print axioms BraidedSymZpd.mem_ker_muBar_twist_id_iff
#print axioms BraidedSymZpd.ker_muBar_twist_id_eq

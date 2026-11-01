/-
The dimension-count engine behind `cor:criterion`.

`ZpdCore.determined_iff` characterises `Determined μ` as `Z_μ = ker μ̄`.  This file packages the
two ways that equality is used in practice, so that a concrete instance only has to supply finite
data:

* `ZpdEngine.determined_of_finrank_ker_le`: a lower bound `finrank (ker μ̄) ≤ finrank Z_μ`
  suffices (the reverse inequality is `ZpdCore.Zmu_le_ker`, which is free);
* `ZpdEngine.determined_of_certificates`: if `A ⊗ A` has dimension `k + r`, there are `k`
  linearly independent zero-pair tensors and `r` linearly independent values of `μ` in the range
  of `μ̄`, then `A` is determined by `μ`.

The two inputs are produced by `linearIndependent_tmul_of_leftInverse` (a pivot certificate: a
left inverse of the matrix of tensor coordinates, checked by computation) and by
`Fintype.linearIndependent_iff` on a finite field (checked by `decide`).

Every declaration is checked by Lean's kernel; no axiom is added.
-/
import ZpdCore.Zpd
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import Research.BraidedSymZpd.BraidedSymZpd
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.StdBasis

open TensorProduct
open scoped TensorProduct

namespace ZpdEngine

universe u

variable {K : Type u} [Field K]
variable {A : Type u} [AddCommGroup A] [Module K A]

/-! ## The criterion, in the two forms a concrete instance needs -/

/-- **`cor:criterion`, lower-bound form.** If `finrank Z_μ` reaches `finrank (ker μ̄)` then
`A` is determined by `μ`.  Combined with `ZpdCore.Zmu_le_ker` this is exactly the hypothesis of
the criterion. -/
theorem determined_of_finrank_ker_le (μ : A →ₗ[K] A →ₗ[K] A) [FiniteDimensional K A]
    (h : Module.finrank K (LinearMap.ker (ZpdCore.muBar μ)) ≤
      Module.finrank K (ZpdCore.Zmu μ)) :
    ZpdCore.Determined μ := by
  rw [ZpdCore.determined_iff]
  exact Submodule.eq_of_le_of_finrank_le (ZpdCore.Zmu_le_ker μ) h

/-- **`cor:criterion`, dimension form**: a determined `μ` has `dim Z_μ = dim ker μ̄`. -/
theorem finrank_Zmu_eq_finrank_ker (μ : A →ₗ[K] A →ₗ[K] A)
    (h : ZpdCore.Determined μ) :
    Module.finrank K (ZpdCore.Zmu μ) =
      Module.finrank K (LinearMap.ker (ZpdCore.muBar μ)) := by
  rw [(ZpdCore.determined_iff μ).mp h]

/-! ## Pivot certificates for pure tensors -/

/-- The linear functional `x ⊗ y ↦ p x * q y` on `A ⊗ A`. -/
noncomputable def tensorCoord (p q : A →ₗ[K] K) : A ⊗[K] A →ₗ[K] K :=
  TensorProduct.lift (LinearMap.mk₂ K (fun x y => p x * q y)
    (fun x₁ x₂ y => by simp only [map_add, add_mul])
    (fun c x y => by simp only [map_smul, smul_eq_mul, mul_assoc])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun c x y => by simp only [map_smul, smul_eq_mul]; ring))

@[simp]
theorem tensorCoord_tmul (p q : A →ₗ[K] K) (x y : A) :
    tensorCoord p q (x ⊗ₜ[K] y) = p x * q y := rfl

/-- **Pivot certificate.** A family of pure tensors `v i ⊗ w i` is linearly independent as soon as
the matrix `M i j = p i (v j) * q i (w j)` of tensor coordinates has a left inverse.  The left
inverse is a finite matrix of numerals, so the hypothesis is a kernel-checkable identity. -/
theorem linearIndependent_tmul_of_leftInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : ι → A) (p q : ι → A →ₗ[K] K) (Ninv : Matrix ι ι K)
    (h : Ninv * Matrix.of (fun i j => p i (v j) * q i (w j)) = 1) :
    LinearIndependent K (fun j => v j ⊗ₜ[K] w j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set M : Matrix ι ι K := Matrix.of (fun i j => p i (v j) * q i (w j)) with hM
  have hmul : M.mulVec c = 0 := by
    ext i
    have h1 := congrArg (tensorCoord (p i) (q i)) hc
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.map_zero] at h1
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using h1
  have hc0 : c = 0 := by
    calc c = (1 : Matrix ι ι K).mulVec c := by rw [Matrix.one_mulVec]
      _ = (Ninv * M).mulVec c := by rw [h]
      _ = Ninv.mulVec (M.mulVec c) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  intro i
  exact congrFun hc0 i

/-! ## The two dimension bounds -/

/-- Zero-pair tensors that are linearly independent give a lower bound for `dim Z_μ`. -/
theorem card_le_finrank_Zmu (μ : A →ₗ[K] A →ₗ[K] A) [FiniteDimensional K A]
    {ι : Type*} [Fintype ι]
    (t : ι → A ⊗[K] A) (ht : ∀ i, t i ∈ ZpdCore.Zmu μ)
    (hli : LinearIndependent K t) :
    Fintype.card ι ≤ Module.finrank K (ZpdCore.Zmu μ) := by
  classical
  have hspan : Submodule.span K (Set.range t) ≤ ZpdCore.Zmu μ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr ht)
  have h1 : Module.finrank K (Submodule.span K (Set.range t)) = Fintype.card ι :=
    finrank_span_eq_card hli
  have h2 := Submodule.finrank_mono hspan
  omega

/-- Linearly independent values of `μ` give a lower bound for `dim (range μ̄)`. -/
theorem card_le_finrank_range (μ : A →ₗ[K] A →ₗ[K] A) [FiniteDimensional K A]
    {ι : Type*} [Fintype ι]
    (z : ι → A) (hz : ∀ i, z i ∈ LinearMap.range (ZpdCore.muBar μ))
    (hli : LinearIndependent K z) :
    Fintype.card ι ≤ Module.finrank K (LinearMap.range (ZpdCore.muBar μ)) := by
  classical
  have hspan : Submodule.span K (Set.range z) ≤ LinearMap.range (ZpdCore.muBar μ) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hz)
  have h1 : Module.finrank K (Submodule.span K (Set.range z)) = Fintype.card ι :=
    finrank_span_eq_card hli
  have h2 := Submodule.finrank_mono hspan
  omega

/-! ## The assembled engine -/

/-- **The engine.**  Let `A` be a finite-dimensional `K`-algebra and `μ` a bilinear map.  If `k`
linearly independent zero-pair tensors and `r` linearly independent values of `μ` fill up
`A ⊗ A` (`k + r = finrank (A ⊗ A)`), then `A` is determined by `μ`.

Indeed `k ≤ finrank Z_μ ≤ finrank (ker μ̄)` and `r ≤ finrank (range μ̄)`, while rank-nullity
says `finrank (range μ̄) + finrank (ker μ̄) = finrank (A ⊗ A) = k + r`; so all these inequalities
are equalities, and `determined_of_finrank_ker_le` applies. -/
theorem determined_of_certificates (μ : A →ₗ[K] A →ₗ[K] A) [FiniteDimensional K A]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → A ⊗[K] A) (ht : ∀ i, t i ∈ ZpdCore.Zmu μ) (hli : LinearIndependent K t)
    (z : κ → A) (hz : ∀ i, z i ∈ LinearMap.range (ZpdCore.muBar μ))
    (hli' : LinearIndependent K z)
    (hcard : Fintype.card ι + Fintype.card κ = Module.finrank K (A ⊗[K] A)) :
    ZpdCore.Determined μ := by
  have hk : Fintype.card ι ≤ Module.finrank K (ZpdCore.Zmu μ) := card_le_finrank_Zmu μ t ht hli
  have hr : Fintype.card κ ≤ Module.finrank K (LinearMap.range (ZpdCore.muBar μ)) :=
    card_le_finrank_range μ z hz hli'
  have hzk : Module.finrank K (ZpdCore.Zmu μ) ≤
      Module.finrank K (LinearMap.ker (ZpdCore.muBar μ)) :=
    Submodule.finrank_mono (ZpdCore.Zmu_le_ker μ)
  have hrn := LinearMap.finrank_range_add_finrank_ker (ZpdCore.muBar μ)
  refine determined_of_finrank_ker_le μ ?_
  omega

end ZpdEngine

/-! ## `prop:matrix`: the finrank bridge over `𝔽₃`

The engine above is now instantiated at `A = M₂(𝔽₃)` and `μ = μ_α`, the twisted product
`x * y + α y * α x` of `α` the conjugation by `diag (1, -1)`.  The two certificates are

* twelve pure tensors `x ⊗ y` with `μ x y = 0`, shown independent by a `12 × 12` matrix of
  tensor coordinates with a left inverse checked by `decide`;
* the four values `μ (e₁₁) (e₁₁)`, `μ (e₁₁) (e₁₂)`, `μ (e₁₁) (e₂₁)`, `μ (e₁₂) (e₂₁)` of `μ`,
  shown independent by `decide` over the `81` coefficient vectors.

`12 + 4 = 16 = finrank (A ⊗ A)`, so `ZpdEngine.determined_of_certificates` gives
`BraidedSymZpd.determined_matrix2`.
-/

namespace BraidedSymZpd

open ZpdEngine

instance instFactPrime3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The field `𝔽₃`. -/
abbrev F3 := ZMod 3

/-- `M₂(𝔽₃)`. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) F3

/-- A `2 × 2` matrix from its four entries. -/
def mat (a b c d : F3) : M2 := !![a, b; c, d]

/-! ### The conjugation by `diag (1, -1)` -/

/-- The matrix `diag (1, -1)` over `𝔽₃`, which is its own inverse. -/
def Dm : M2 := mat 1 0 0 (-1)

theorem Dm_mul_self : Dm * Dm = 1 := by decide

/-- `diag (1, -1)` as a unit of `M₂(𝔽₃)`. -/
def Dunit : M2ˣ := ⟨Dm, Dm, Dm_mul_self, Dm_mul_self⟩

/-- The conjugation by `diag (1, -1)`, in the entrywise form used for the computation: the
off-diagonal entries change sign. -/
def alpha (x : M2) : M2 := fun i j => if i = j then x i j else -x i j

/-- `alpha` as a `𝔽₃`-linear map. -/
def alphaLM : M2 →ₗ[F3] M2 where
  toFun := alpha
  map_add' x y := by
    ext i j
    by_cases h : i = j <;> simp [alpha, h, add_comm]
  map_smul' c x := by
    ext i j
    by_cases h : i = j <;> simp [alpha, h]

/-- The entrywise form is the conjugation by `diag (1, -1)`. -/
theorem alpha_eq_conjByUnit (x : M2) : alpha x = conjByUnit (K := F3) Dunit x := by
  simp only [BraidedSymZpd.conjByUnit_apply, Dunit, Units.val_mk, Units.inv_mk, Dm, mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alpha, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply,
      Fin.sum_univ_two]
    <;> ring

/-- The entrywise form is the conjugation by `diag (1, -1)`, as linear maps. -/
theorem alphaLM_eq_conjByUnit : alphaLM = conjByUnit (K := F3) Dunit :=
  LinearMap.ext alpha_eq_conjByUnit

/-- The twisted product `μ_α (x, y) = x * y + α y * α x` of `prop:matrix`. -/
noncomputable def muZero : M2 →ₗ[F3] M2 →ₗ[F3] M2 := ZpdCore.twistMu alphaLM

/-! ### The twelve zero pairs -/

/-- Left factors of twelve pairs `(x, y)` with `μ_α (x, y) = 0`. -/
def xT : Fin 12 → M2 :=
  ![mat 0 0 0 1, mat 0 0 1 0, mat 0 1 0 0, mat 1 0 0 0, mat 0 0 1 0, mat 0 1 0 0,
    mat 1 0 0 1, mat 1 0 0 1, mat 0 0 1 1, mat 0 1 0 1, mat 0 1 1 0, mat 1 0 1 1]

/-- Right factors of the twelve zero pairs. -/
def yT : Fin 12 → M2 :=
  ![mat 1 0 0 0, mat 0 0 1 0, mat 0 1 0 0, mat 0 0 0 1, mat 1 0 0 1, mat 1 0 0 1,
    mat 0 0 1 0, mat 0 1 0 0, mat 1 0 2 0, mat 1 2 0 0, mat 0 1 2 0, mat 1 1 0 1]

theorem mu_zero (j : Fin 12) : muZero (xT j) (yT j) = 0 := by
  fin_cases j <;> simp [muZero, ZpdCore.twistMu_apply, alphaLM, alpha, xT, yT, mat] <;> decide

theorem tensors_mem (j : Fin 12) : xT j ⊗ₜ[F3] yT j ∈ ZpdCore.Zmu muZero :=
  ZpdCore.tmul_mem_Zmu (mu_zero j)

/-! ### The pivot certificate for the twelve tensors -/

/-- The entry functional `x ↦ x i j`. -/
def ent (i j : Fin 2) : M2 →ₗ[F3] F3 where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The row index of the pivot coordinate acting on the left factor. -/
def posK : Fin 12 → Fin 2 := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

/-- The column index of the pivot coordinate acting on the left factor. -/
def posL : Fin 12 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1]

/-- The row index of the pivot coordinate acting on the right factor. -/
def posK2 : Fin 12 → Fin 2 := ![0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0]

/-- The column index of the pivot coordinate acting on the right factor. -/
def posL2 : Fin 12 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0]

/-- The `12 × 12` matrix of tensor coordinates of the twelve tensors at the twelve pivots. -/
def piv : Matrix (Fin 12) (Fin 12) F3 :=
  Matrix.of fun i j => ent (posK i) (posL i) (xT j) * ent (posK2 i) (posL2 i) (yT j)

/-- A left inverse of the pivot matrix, checked below by `decide`. -/
def nInv : Matrix (Fin 12) (Fin 12) F3 :=
  !![2, 0, 0, 0, 2, 0, 0, 1, 2, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 2, 0;
    0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0;
    2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0;
    0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem cert : nInv * piv = 1 := by decide

theorem linearIndependent_tensors : LinearIndependent F3 (fun j : Fin 12 => xT j ⊗ₜ[F3] yT j) :=
  linearIndependent_tmul_of_leftInverse xT yT (fun i => ent (posK i) (posL i))
    (fun i => ent (posK2 i) (posL2 i)) nInv (by simpa [piv] using cert)

/-! ### The four independent values of `μ` -/

/-- Four values of `μ`, at the pairs `(e₁₁, e₁₁)`, `(e₁₁, e₁₂)`, `(e₁₁, e₂₁)`, `(e₁₂, e₂₁)`. -/
def w : Fin 4 → M2 := ![mat 2 0 0 0, mat 0 1 0 0, mat 0 0 2 0, mat 1 0 0 1]

/-- The left arguments of the four values. -/
def aW : Fin 4 → M2 := ![mat 1 0 0 0, mat 1 0 0 0, mat 1 0 0 0, mat 0 1 0 0]

/-- The right arguments of the four values. -/
def bW : Fin 4 → M2 := ![mat 1 0 0 0, mat 0 1 0 0, mat 0 0 1 0, mat 0 0 1 0]

theorem w_eq (i : Fin 4) : w i = muZero (aW i) (bW i) := by
  fin_cases i <;> simp [w, aW, bW, muZero, ZpdCore.twistMu_apply, alphaLM, alpha, mat] <;> decide

theorem w_mem (i : Fin 4) : w i ∈ LinearMap.range (ZpdCore.muBar muZero) :=
  ⟨aW i ⊗ₜ[F3] bW i, by rw [ZpdCore.muBar_tmul, w_eq]⟩

theorem w_indep : LinearIndependent F3 w := by
  rw [Fintype.linearIndependent_iff]
  decide

/-! ### The dimension bookkeeping -/

noncomputable def bA : Module.Basis (Fin 2 × Fin 2) F3 M2 := Matrix.stdBasis F3 (Fin 2) (Fin 2)

noncomputable def bT : Module.Basis ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) F3 (M2 ⊗[F3] M2) :=
  bA.tensorProduct bA

instance : FiniteDimensional F3 (M2 ⊗[F3] M2) :=
  Module.Basis.finiteDimensional_of_finite bT

theorem finrank_M2 : Module.finrank F3 M2 = 4 := by
  rw [Module.finrank_matrix]
  simp

theorem finrank_tensor : Module.finrank F3 (M2 ⊗[F3] M2) = 16 := by
  rw [Module.finrank_tensorProduct]
  simp only [finrank_M2]

/-! ### `prop:matrix` -/

/-- **`prop:matrix`**: `M₂(𝔽₃)` is determined by the twisted product of the conjugation by
`diag (1, -1)`. -/
theorem determined_matrix2 :
    ZpdCore.Determined (ZpdCore.twistMu (BraidedSymZpd.conjByUnit (K := F3) Dunit)) := by
  have h : ZpdCore.Determined muZero :=
    determined_of_certificates muZero (fun j => xT j ⊗ₜ[F3] yT j) tensors_mem
      linearIndependent_tensors w w_mem w_indep (by rw [finrank_tensor]; norm_num)
  simpa [muZero, alphaLM_eq_conjByUnit] using h

/-- **Consequence of `prop:matrix` and `rem:inner`**: `M₂(𝔽₃)` is determined by the Jordan
product `x * y + y * x`, the twisted product of the identity.  This is
`BraidedSymZpd.determined_twist_conj_iff` read in the direction that removes the unit. -/
theorem determined_jordan :
    ZpdCore.Determined (ZpdCore.twistMu (LinearMap.id : M2 →ₗ[F3] M2)) :=
  (determined_twist_conj_iff (K := F3) (D := Dunit)).mp determined_matrix2

/-- **`rem:inner`, the answer for every inner twist**: the statement does not depend on the unit,
so `M₂(𝔽₃)` is determined by the twisted product of the conjugation by *any* unit. -/
theorem determined_twist_conj_all (D : M2ˣ) :
    ZpdCore.Determined (ZpdCore.twistMu (conjByUnit (K := F3) D)) :=
  (determined_twist_conj_iff (K := F3) (D := D)).mpr determined_jordan

end BraidedSymZpd

/-! ## Axiom audit -/

#print axioms ZpdEngine.determined_of_finrank_ker_le
#print axioms ZpdEngine.linearIndependent_tmul_of_leftInverse
#print axioms ZpdEngine.determined_of_certificates
#print axioms BraidedSymZpd.linearIndependent_tensors
#print axioms BraidedSymZpd.w_indep
#print axioms BraidedSymZpd.finrank_tensor
#print axioms BraidedSymZpd.determined_matrix2
#print axioms BraidedSymZpd.determined_jordan
#print axioms BraidedSymZpd.determined_twist_conj_all

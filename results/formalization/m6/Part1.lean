import Mathlib
import ZpdCore.Zpd
import Research.BraidedSymZpd.BraidedSymZpd

/-!
# `prop:matrix`: the finrank bridge from the `𝔽₃` numbers

`A = M₂(𝔽₃)` is determined by the twisted product `μ_α (x, y) = x * y + α (y) * α (x)` for `α`
the conjugation by `diag (1, -1)`.  The proof follows `cor:criterion`: `μ̄_α` is surjective onto
the four-dimensional `A`, so `ker μ̄_α` has dimension `12`; twelve explicit pure zero tensors are
linearly independent, so `Z_μ` also has dimension `12`; hence `Z_μ = ker μ̄_α` and `A` is
determined by `μ_α`.
-/

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace BraidedSymZpd

/-- The field `𝔽₃`. -/
abbrev K := ZMod 3

/-- The algebra `M₂(𝔽₃)`. -/
abbrev A := Matrix (Fin 2) (Fin 2) K

/-- The unit `diag (1, -1)` of `M₂(𝔽₃)`. -/
def D : Aˣ where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- The matrix units of `M₂(𝔽₃)`. -/
def E : Fin 2 → Fin 2 → A
  | 0, 0 => !![1, 0; 0, 0]
  | 0, 1 => !![0, 1; 0, 0]
  | 1, 0 => !![0, 0; 1, 0]
  | 1, 1 => !![0, 0; 0, 1]

theorem E_eq_single (p q : Fin 2) : E p q = Matrix.single p q (1 : K) := by
  fin_cases p <;> fin_cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem E_eq_stdBasis (p q : Fin 2) : E p q = Matrix.stdBasis K (Fin 2) (Fin 2) (p, q) := by
  rw [Matrix.stdBasis_eq_single, E_eq_single]

/-- The twisted product of `prop:matrix`: `μ_α (x, y) = x * y + α (y) * α (x)`. -/
def mu : A →ₗ[K] A →ₗ[K] A := ZpdCore.twistMu (conjByUnit (K := K) D)

theorem mu_def : mu = ZpdCore.twistMu (conjByUnit (K := K) D) := rfl

/-- The `16` values of `μ_α` on pairs of matrix units: all of them are the four matrix units up
to a nonzero scalar, so `μ̄_α` is onto. -/
theorem mu_E : ∀ (p q r s : Fin 2),
    (p, q, r, s) = (0, 0, 0, 0) → mu (E p q) (E r s) = (2 : K) • E 0 0 := by
  decide

end BraidedSymZpd

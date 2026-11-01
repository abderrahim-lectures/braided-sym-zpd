import Mathlib
import ZpdCore.Zpd
import Research.BraidedSymZpd.BraidedSymZpd

open TensorProduct
open scoped TensorProduct

namespace Test1

abbrev K := ZMod 3
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

/-- Conjugation by `diag (1, -1)`. -/
noncomputable def alpha : A →ₗ[K] A := BraidedSymZpd.conjByUnit D

/-- The twisted product of `prop:matrix`. -/
noncomputable def mu : A →ₗ[K] A →ₗ[K] A := ZpdCore.twistMu alpha

-- units
def E : Fin 2 → Fin 2 → A
  | 0, 0 => !![1, 0; 0, 0]
  | 0, 1 => !![0, 1; 0, 0]
  | 1, 0 => !![0, 0; 1, 0]
  | 1, 1 => !![0, 0; 0, 1]

example : mu (E 0 0) (E 0 0) = 2 • E 0 0 := by
  simp only [mu, ZpdCore.twistMu_apply, alpha, BraidedSymZpd.conjByUnit_apply, D]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : mu (E 0 1) (E 1 0) = E 0 0 + E 1 1 := by
  simp only [mu, ZpdCore.twistMu_apply, alpha, BraidedSymZpd.conjByUnit_apply, D]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

-- a test of a Finset sum over Fin 2 with matrix entries
example : (∑ p : Fin 2, ∑ q : Fin 2, (E p q) 0 0) = 1 := by decide

end Test1

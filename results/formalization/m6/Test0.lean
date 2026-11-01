import Mathlib

example : (2 : ZMod 3) * 2 = 1 := by decide
example : (2 : ZMod 3) + 2 = 1 := by decide
example : (2 : ZMod 3) ≠ 0 := by decide

example : (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 0; 0, 2] := rfl

example : (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![1, 0; 0, 2] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

example : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) * !![0, 0; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

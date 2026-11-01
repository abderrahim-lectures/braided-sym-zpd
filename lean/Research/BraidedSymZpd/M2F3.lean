/-
Copyright (c) 2026 The BraidedSymZpd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Open Math OS review pass
-/
module

/-!
# `prop:matrix`: the computation over `𝔽₃`

The paper proves `prop:matrix` — `M₂(𝔽₃)` is determined by the twisted product
`μ_α (x, y) = x * y + α (y * x)` for `α` the conjugation by `diag (1, -1)` — by checking the
criterion `cor:criterion` numerically: `μ̄_α` has rank `4`, so `ker μ̄_α` has dimension
`12`, and the `417` pairs `(x, y)` with `μ_α (x, y) = 0` span a subspace of dimension `12`.

This file recomputes those three numbers. The matrices of `M₂(𝔽₃)` are encoded as four
entries in `{0, 1, 2}`; `rank` is Gaussian elimination over `𝔽₃` on lists of vectors. The three
theorems at the end are proved by `decide`, so the computations are checked by Lean's kernel:
they hold without `native_decide` and without any axiom.

## Main results

* `M2F3.zeroPairs_card`: exactly `417` of the `81 * 81` pairs satisfy `μ_α (x, y) = 0`.
* `M2F3.rank_zeroPairs`: their `417` tensors span a subspace of dimension `12`.
* `M2F3.rankMu`: the linearisation `μ̄_α` has rank `4`, hence kernel dimension `16 - 4 = 12`.
-/

@[expose] public section

namespace M2F3

/-- The field size. -/
def p : Nat := 3

/-- Reduction modulo `3` of a nonnegative integer. -/
def md (n : Nat) : Nat := n % p

/-- `2 * 2` matrices over `𝔽₃`, as quadruples of entries. -/
structure Mat2 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq, Repr

namespace Mat2

/-- The entries of the matrix as a list, in the order `a, b, c, d`. -/
def toList (x : Mat2) : List Nat := [x.a, x.b, x.c, x.d]

/-- The `k`-th entry of the matrix, for `k = 0, 1, 2, 3`. -/
def get (x : Mat2) : Nat → Nat
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | _ => x.d

/-- The product of two matrices over `𝔽₃`. -/
def mul (x y : Mat2) : Mat2 where
  a := md (x.a * y.a + x.b * y.c)
  b := md (x.a * y.b + x.b * y.d)
  c := md (x.c * y.a + x.d * y.c)
  d := md (x.c * y.b + x.d * y.d)

/-- Conjugation by `diag (1, -1)`: the entries `b` and `c` change sign. -/
def alpha (x : Mat2) : Mat2 where
  a := x.a
  b := md (p - x.b)
  c := md (p - x.c)
  d := x.d

/-- The twisted product `x * y + α (y * x)`. -/
def mu (x y : Mat2) : Mat2 where
  a := md ((x.mul y).a + ((y.mul x).alpha).a)
  b := md ((x.mul y).b + ((y.mul x).alpha).b)
  c := md ((x.mul y).c + ((y.mul x).alpha).c)
  d := md ((x.mul y).d + ((y.mul x).alpha).d)

end Mat2

/-- The zero matrix. -/
def zeroMat : Mat2 := ⟨0, 0, 0, 0⟩

/-- All `81` matrices over `𝔽₃`. -/
def allM : List Mat2 :=
  (List.range p).flatMap fun a =>
    (List.range p).flatMap fun b =>
      (List.range p).flatMap fun c => (List.range p).map fun d => ⟨a, b, c, d⟩

/-- The pure tensor `x ⊗ y`, as its `16` coordinates in the basis of matrix units. -/
def tensor (x y : Mat2) : List Nat :=
  (List.range 16).map fun k => md (x.get (k / 4) * y.get (k % 4))

/-- The tensors `x ⊗ y` with `μ_α (x, y) = 0`, in the order of `allM`. -/
def zeroPairs : List (List Nat) :=
  allM.flatMap fun x =>
    allM.filterMap fun y => if x.mu y = zeroMat then some (tensor x y) else none

/-- The inverse in `𝔽₃`. -/
def inv : Nat → Nat
  | 1 => 1
  | 2 => 2
  | _ => 0

/-- Add a multiple of a row to `v` so as to cancel the pivot entry. -/
def cancel (v row : List Nat) (pivot : Nat) : List Nat :=
  let c := v.getD pivot 0
  if c = 0 then v
  else (List.range v.length).map fun j => md (v.getD j 0 + (p - c) * (row.getD j 0))

/-- Gaussian elimination: one step, reducing `v` against the rows already in the basis. -/
def reduceRows (rows : List (List Nat × Nat)) (v : List Nat) : List Nat :=
  rows.foldl (fun v rp => cancel v rp.1 rp.2) v

/-- Gaussian elimination over `𝔽₃`: the rows of a reduced basis, together with their pivots. -/
def echelon : List (List Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | [], basis => basis
  | v :: vs, basis =>
      let r := reduceRows basis v
      match (List.range r.length).find? (fun j => r.getD j 0 != 0) with
      | none => echelon vs basis
      | some j =>
          let c := r.getD j 0
          let r' := r.map fun t => md (t * inv c)
          echelon vs (basis ++ [(r', j)])

/-- The rank over `𝔽₃` of a list of vectors. -/
def rank (rows : List (List Nat)) : Nat := (echelon rows []).length

/-- The four matrix units. -/
def basisE : List Mat2 := [⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The columns of the matrix of `μ̄_α` in the bases of matrix units. -/
def rankMu : Nat :=
  rank (basisE.flatMap fun x => basisE.map fun y => (x.mu y).toList)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- **`prop:matrix`**, first number: exactly `417` of the `6561` pairs have `μ_α (x, y) = 0`. -/
theorem zeroPairs_card : zeroPairs.length = 417 := by decide

/-- **`prop:matrix`**, second number: the `417` tensors span a subspace of dimension `12`. -/
theorem rank_zeroPairs : rank zeroPairs = 12 := by decide

/-- **`prop:matrix`**, third number: `μ̄_α` has rank `4`, so its kernel has dimension `12`. -/
theorem rankMu_eq : rankMu = 4 := by decide

end M2F3

/-! ## Axiom audit

The three numerical facts are proved by kernel evaluation, so no axiom is used. -/

#print axioms M2F3.zeroPairs_card
#print axioms M2F3.rank_zeroPairs
#print axioms M2F3.rankMu_eq

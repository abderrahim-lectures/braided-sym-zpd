import Mathlib

/-!
# A self-contained machine check of the paper's core

This file was written by an independent review pass (Open Math OS), **not** by the author, and is
included so that the paper's main results can be checked without the two modules
(`Research.Zpd.Basic`, `Research.Zpd.DualNumbers`) that the author's Lean development imports and
that are not published. It depends on Mathlib only.

What is checked, over an arbitrary field `K` and an arbitrary bilinear `μ` on a `K`-module `A`:

* `determined_iff` — the criterion of `cor:criterion`: `Determined μ ↔ Z_μ = ker μ̄`, with no
  unitality, associativity, surjectivity or finite-dimensionality;
* `determined_comp_of_right_id` — `thm:zpd-fxy`, with the unit used only through a right identity;
* `determined_of_injective_comp` — `prop:injective`;
* `identity_iff` — `cor:identity` (ii), and `determined_zero` for the characteristic-2 remark;
* `twisted_determined` — `cor:twisted` (with `α` only multiplicative);
* `anti_braiding` and `anti_twisted_determined` — `cor:anti`, with no commutativity;
* `codim_determined`, `codim_determined_of_f_one_zero` — `thm:codim`;
* `jordan_forces_comm`, `twisted_forces_comm` — the two "not of the form `f(xy)`" assertions;
* `braidings_commutative` — the abstract's sentence on the three braidings.

Not checked here: the numerical claims of `prop:matrix` and of the remark after it (417 zero pairs,
rank 4, dimensions 12 and 13). Those are checked in the review report and by the `#guard`s of
`Research/BraidedSymZpd/BraidedSymZpd.lean`.

The thirteen `#print axioms` commands at the end of the file report only `propext`,
`Classical.choice` and `Quot.sound` — there is no `sorry` and no added axiom.
-/

open TensorProduct

namespace ZpdPaper

universe u

variable {K : Type u} [Field K]

section General

variable {A : Type u} [AddCommGroup A] [Module K A]

/-- The linearisation `μ̄ : A ⊗ A → A` of a bilinear map `μ`. -/
noncomputable def muBar (μ : A →ₗ[K] A →ₗ[K] A) : A ⊗[K] A →ₗ[K] A :=
  TensorProduct.lift μ

theorem muBar_tmul (μ : A →ₗ[K] A →ₗ[K] A) (x y : A) :
    muBar μ (x ⊗ₜ[K] y) = μ x y := rfl

/-- `Z_μ`, the span in `A ⊗ A` of the tensors `x ⊗ y` with `μ x y = 0`. -/
noncomputable def Zmu (μ : A →ₗ[K] A →ₗ[K] A) : Submodule K (A ⊗[K] A) :=
  Submodule.span K {t : A ⊗[K] A | ∃ x y : A, μ x y = 0 ∧ t = x ⊗ₜ[K] y}

theorem tmul_mem_Zmu {μ : A →ₗ[K] A →ₗ[K] A} {x y : A} (h : μ x y = 0) :
    x ⊗ₜ[K] y ∈ Zmu μ :=
  Submodule.subset_span ⟨x, y, h, rfl⟩

/-- `Z_μ ⊆ ker μ̄`, as stated in the paper. -/
theorem Zmu_le_ker (μ : A →ₗ[K] A →ₗ[K] A) : Zmu μ ≤ LinearMap.ker (muBar μ) := by
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      rw [LinearMap.mem_ker, muBar_tmul, hab]
  | zero => rw [LinearMap.mem_ker, map_zero]
  | add x y _ _ ihx ihy => rw [LinearMap.mem_ker, map_add, ihx, ihy, add_zero]
  | smul c x _ ih => rw [LinearMap.mem_ker, map_smul, ih, smul_zero]

/-- `def:determined`: every bilinear `φ` vanishing on the pairs with `μ x y = 0` factors
through `μ`, with values in an arbitrary space. -/
def Determined (μ : A →ₗ[K] A →ₗ[K] A) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] (φ : A →ₗ[K] A →ₗ[K] V),
    (∀ x y : A, μ x y = 0 → φ x y = 0) → ∃ ψ : A →ₗ[K] V, ∀ x y : A, φ x y = ψ (μ x y)

/-- The bilinear map `(x, y) ↦ f (m x y)`, i.e. `μ = f ∘ m`. -/
noncomputable def compMu (m : A →ₗ[K] A →ₗ[K] A) (f : A →ₗ[K] A) : A →ₗ[K] A →ₗ[K] A :=
  m.compr₂ f

@[simp] theorem compMu_apply (m : A →ₗ[K] A →ₗ[K] A) (f : A →ₗ[K] A) (x y : A) :
    compMu m f x y = f (m x y) := rfl

/-- Easy half of `cor:criterion`: `ker μ̄ ⊆ Z_μ` implies that `A` is determined by `μ`. -/
theorem determined_of_ker_le (μ : A →ₗ[K] A →ₗ[K] A)
    (h : LinearMap.ker (muBar μ) ≤ Zmu μ) : Determined μ := by
  intro V _ _ φ hφ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A ⊗[K] A →ₗ[K] V, ∀ x y : A, Φ (x ⊗ₜ[K] y) = φ x y :=
    ⟨TensorProduct.lift φ, fun x y => rfl⟩
  have hZ : Zmu μ ≤ LinearMap.ker Φ := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, b, hab, rfl⟩ := hx
        rw [LinearMap.mem_ker, hΦ a b, hφ a b hab]
    | zero => rw [LinearMap.mem_ker, map_zero]
    | add x y _ _ ihx ihy => rw [LinearMap.mem_ker, map_add, ihx, ihy, add_zero]
    | smul c x _ ih => rw [LinearMap.mem_ker, map_smul, ih, smul_zero]
  have hker : LinearMap.ker (muBar μ) ≤ LinearMap.ker Φ := le_trans h hZ
  obtain ⟨q, hq⟩ := (muBar μ).range.exists_isCompl
  let ψ₁ : (A ⊗[K] A ⧸ LinearMap.ker (muBar μ)) →ₗ[K] V := Submodule.liftQ _ Φ hker
  let e : (A ⊗[K] A ⧸ LinearMap.ker (muBar μ)) ≃ₗ[K] (muBar μ).range :=
    LinearMap.quotKerEquivRange (muBar μ)
  let ψ₂ : (muBar μ).range →ₗ[K] V := ψ₁.comp e.symm.toLinearMap
  refine ⟨LinearMap.ofIsCompl hq ψ₂ 0, ?_⟩
  intro x y
  have h3 : ψ₁ (Submodule.Quotient.mk (x ⊗ₜ[K] y) : A ⊗[K] A ⧸ LinearMap.ker (muBar μ))
      = Φ (x ⊗ₜ[K] y) := rfl
  have key : ∀ (hz : muBar μ (x ⊗ₜ[K] y) ∈ (muBar μ).range),
      ψ₂ ⟨muBar μ (x ⊗ₜ[K] y), hz⟩ = φ x y := by
    intro hz
    have h2 : e.symm ⟨muBar μ (x ⊗ₜ[K] y), hz⟩ = Submodule.Quotient.mk (x ⊗ₜ[K] y) :=
      LinearMap.quotKerEquivRange_symm_apply_image (muBar μ) (x ⊗ₜ[K] y) hz
    show ψ₁ (e.symm _) = φ x y
    rw [h2, h3, hΦ]
  have h4 : LinearMap.ofIsCompl hq ψ₂ 0 (μ x y)
      = ψ₂ ⟨muBar μ (x ⊗ₜ[K] y), LinearMap.mem_range_self _ _⟩ := by
    rw [← muBar_tmul μ x y]
    exact LinearMap.ofIsCompl_apply_left hq ⟨muBar μ (x ⊗ₜ[K] y), LinearMap.mem_range_self _ _⟩
  exact (h4.trans (key _)).symm

/-- The other half of `cor:criterion`: a vector of `ker μ̄` not in `Z_μ` is separated from `Z_μ`
by a linear functional, which yields a bilinear `φ` that does not factor. -/
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

/-- `cor:criterion`: `A` is determined by `μ` iff `Z_μ = ker μ̄`.  No unitality and no
surjectivity hypothesis; `K` an arbitrary field. -/
theorem determined_iff (μ : A →ₗ[K] A →ₗ[K] A) :
    Determined μ ↔ Zmu μ = LinearMap.ker (muBar μ) :=
  ⟨fun h => le_antisymm (Zmu_le_ker μ) (ker_le_Zmu_of_determined μ h),
   fun h => determined_of_ker_le μ (le_of_eq h.symm)⟩

/-! ## Products of the form `f(xy)`, and the converse for injective `f` -/

/-- `thm:zpd-fxy`, in the sharper form in which the only property of the unit used is that it is a
*right* identity of `m`.  No associativity and no unit of `m` is needed, only the right identity. -/
theorem determined_comp_of_right_id (m : A →ₗ[K] A →ₗ[K] A) (hm : Determined m)
    (f : A →ₗ[K] A) (e : A) (he : ∀ b : A, m b e = b) :
    Determined (compMu m f) := by
  intro V _ _ φ hφ
  have hzero : ∀ x y : A, m x y = 0 → φ x y = 0 := by
    intro x y hxy
    refine hφ x y ?_
    rw [compMu_apply, hxy, map_zero]
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
  have h4 : LinearMap.ofIsCompl hq ψ₂ 0 (compMu m f x y)
      = ψ₂ ⟨f (m x y), LinearMap.mem_range_self _ _⟩ := by
    rw [compMu_apply]
    exact LinearMap.ofIsCompl_apply_left hq ⟨f (m x y), LinearMap.mem_range_self _ _⟩
  exact (h4.trans (key _)).symm

/-- `prop:injective`: if `f` is injective and `A` is determined by `f ∘ m`, then `A` is
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

/-- The product `μ ≡ 0` determines every algebra (the paper's characteristic `2` remark). -/
theorem determined_zero : Determined (0 : A →ₗ[K] A →ₗ[K] A) := by
  intro V _ _ φ hφ
  refine ⟨0, fun x y => ?_⟩
  rw [show (0 : A →ₗ[K] A →ₗ[K] A) x y = 0 from rfl, hφ x y rfl, map_zero]

/-- `cor:identity` (ii): for `μ x y = 2 • (x * y)` and `char K ≠ 2`, determinedness by `μ` is
equivalent to zpd (i.e. to determinedness by the product itself). -/
theorem identity_iff {A : Type u} [Ring A] [Algebra K A] (h2 : (2 : K) ≠ 0) :
    Determined (compMu (LinearMap.mul K A) ((2 : K) • LinearMap.id)) ↔
      Determined (LinearMap.mul K A) := by
  constructor
  · intro h
    refine determined_of_injective_comp _ ((2 : K) • LinearMap.id) ?_ h
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    have h' : (2 : K) • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
    have h0 : x - y = 0 := by
      rcases (smul_eq_zero.1 h') with h | h
      · exact absurd h h2
      · exact h
    exact sub_eq_zero.1 h0
  · intro h
    have := determined_comp_of_right_id (LinearMap.mul K A) h
      ((2 : K) • LinearMap.id) 1 (fun b => by simp)
    simpa using this

end General

/-! ## The two one-line justifications of the "not of the form f(xy)" assertions -/

section Algebra

variable {A : Type u} [Ring A] [Algebra K A]

/-- Line 292 of the paper: if the Jordan product `x * y + y * x` is `f (x * y)` for a linear
`f`, then `A` is commutative.  This needs no hypothesis on `char K`, so the parenthetical
argument is valid in every characteristic. -/
theorem jordan_forces_comm (f : A →ₗ[K] A)
    (h : ∀ x y : A, f (x * y) = x * y + y * x) : ∀ x y : A, x * y = y * x := by
  intro x y
  have h1 : f (x * y) = x * y + x * y := by
    have := h 1 (x * y)
    simpa using this
  rw [h x y] at h1
  exact (add_left_cancel h1).symm

/-- Line 395 of the paper: if the twisted product `x * y + α y * α x` is `f (x * y)` for a linear
`f`, with `α` a unital, multiplicative, injective map, then `A` is commutative.  (`α.map_one`,
`α.map_mul` and injectivity are exactly what an automorphism provides.) -/
theorem twisted_forces_comm (α : A →+* A) (hα : Function.Injective α) (f : A →ₗ[K] A)
    (h : ∀ x y : A, f (x * y) = x * y + α y * α x) : ∀ x y : A, x * y = y * x := by
  have hgen : ∀ z : A, f z = z + α z := by
    intro z
    have := h z 1
    simpa using this
  intro x y
  have h1 : f (x * y) = x * y + α x * α y := by
    rw [hgen, map_mul]
  rw [h x y] at h1
  have h2 : α x * α y = α y * α x := (add_left_cancel h1).symm
  have h3 : α (y * x) = α (x * y) := by rw [map_mul, map_mul, h2]
  exact (hα h3).symm

/-- The abstract's sentence about the three braidings, in the generality the paper uses: on a
commutative algebra the symmetrized products of the identity braiding, the swap, and the twisted
swap (`α` multiplicative, **not** assumed unital) are all of the form `f(xy)` with `f` linear. -/
theorem braidings_commutative (hcomm : ∀ x y : A, x * y = y * x) (α : A →ₗ[K] A)
    (hα : ∀ x y : A, α (x * y) = α x * α y) (x y : A) :
    (x * y + x * y = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y)) ∧
    (x * y + y * x = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y)) ∧
    (x * y + α y * α x = (LinearMap.id + α : A →ₗ[K] A) (x * y)) := by
  have h2 : x * y + y * x = x * y + x * y := by rw [hcomm y x]
  have hf : x * y + x * y = ((2 : K) • LinearMap.id : A →ₗ[K] A) (x * y) := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, two_smul]
  refine ⟨hf, h2.trans hf, ?_⟩
  rw [LinearMap.add_apply, LinearMap.id_apply, hα, hcomm (α y) (α x)]

end Algebra

section Codim

variable {A : Type u} [Ring A] [Algebra K A]

/-- `thm:codim`, machine-checked: if `ker f` is a two-sided ideal of codimension `1` that does
not contain `1` (`f 1 ≠ 0`), then `A` is determined by `x, y ↦ f (x * y)`, with **no** zpd
hypothesis. -/
theorem codim_determined (f : A →ₗ[K] A)
    (hN : ∀ n : A, f n = 0 → ∀ b : A, f (n * b) = 0 ∧ f (b * n) = 0)
    (hc : ∃ c : A →ₗ[K] K, ∀ x : A, f (x - c x • (1 : A)) = 0)
    (h1 : f 1 ≠ 0) :
    Determined (compMu (LinearMap.mul K A) f) := by
  obtain ⟨c, hc⟩ := hc
  intro V _ _ φ hφ
  have hφ' : ∀ x y : A, f (x * y) = 0 → φ x y = 0 := by
    intro x y h
    exact hφ x y (by simpa using h)
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

/-- When `f 1 = 0`, the remaining hypotheses of `thm:codim` force `f = 0`, hence `μ ≡ 0` and the
conclusion still holds: the hypothesis `f 1 ≠ 0` is used by the proof but is not needed for the
statement. -/
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

/-- The twisted product `(x, y) ↦ x * y + α y * α x` as a bilinear map. -/
noncomputable def twistMu (α : A →ₗ[K] A) : A →ₗ[K] A →ₗ[K] A :=
  LinearMap.mk₂ K (fun x y => x * y + α y * α x)
    (fun x₁ x₂ y => by rw [map_add]; noncomm_ring)
    (fun c x y => by simp [map_smul])
    (fun x y₁ y₂ => by rw [map_add]; noncomm_ring)
    (fun c x y => by simp [map_smul])

end Codim

section Commutative

variable {A : Type u} [CommRing A] [Algebra K A]

/-- `cor:twisted` machine-checked, with `α` only assumed multiplicative (not unital): if `A` is a
commutative algebra determined by its product, it is determined by `x * y + α y * α x`. -/
theorem twisted_determined (hzpd : Determined (LinearMap.mul K A)) (α : A →ₗ[K] A)
    (hα : ∀ x y : A, α (x * y) = α x * α y) :
    Determined (twistMu α) := by
  have heq : twistMu α = compMu (LinearMap.mul K A) (LinearMap.id + α) := by
    ext x y
    show x * y + α y * α x = ((LinearMap.id : A →ₗ[K] A) + α) (x * y)
    rw [LinearMap.add_apply, LinearMap.id_apply, hα x y, mul_comm (α x) (α y)]
  rw [heq]
  exact determined_comp_of_right_id (LinearMap.mul K A) hzpd (LinearMap.id + α) 1
    (fun b => by simp)

end Commutative

section Anti

variable {A : Type u} [Ring A] [Algebra K A]

/-- The key step of `cor:anti` and of the abstract's "the same holds on any algebra when the twist
reverses products": if `α` reverses products then the twisted product is `(id + α)(xy)`.  No
commutativity (this is the section variable slip that the blind-spot review found: the identity
holds over any ring), no unitality of `α`. -/
theorem anti_braiding (α : A →ₗ[K] A) (hα : ∀ x y : A, α (x * y) = α y * α x) (x y : A) :
    x * y + α y * α x = ((LinearMap.id : A →ₗ[K] A) + α) (x * y) := by
  rw [LinearMap.add_apply, LinearMap.id_apply, ← hα]

/-- `cor:anti` machine-checked, with **no** commutativity: if a (possibly noncommutative) algebra
is determined by its product and `α` is linear with `α (xy) = α(y)α(x)`, then it is determined by
the twisted product `x * y + α y * α x`. -/
theorem anti_twisted_determined (hzpd : Determined (LinearMap.mul K A)) (α : A →ₗ[K] A)
    (hα : ∀ x y : A, α (x * y) = α y * α x) :
    Determined (twistMu α) := by
  have heq : twistMu α = compMu (LinearMap.mul K A) (LinearMap.id + α) := by
    ext x y
    exact anti_braiding α hα x y
  rw [heq]
  exact determined_comp_of_right_id (LinearMap.mul K A) hzpd (LinearMap.id + α) 1
    (fun b => mul_one b)

end Anti

end ZpdPaper

/-! ## Axiom audit -/

#print axioms ZpdPaper.determined_iff
#print axioms ZpdPaper.determined_comp_of_right_id
#print axioms ZpdPaper.determined_of_injective_comp
#print axioms ZpdPaper.identity_iff
#print axioms ZpdPaper.jordan_forces_comm
#print axioms ZpdPaper.twisted_forces_comm
#print axioms ZpdPaper.braidings_commutative
#print axioms ZpdPaper.determined_zero
#print axioms ZpdPaper.codim_determined
#print axioms ZpdPaper.codim_determined_of_f_one_zero
#print axioms ZpdPaper.anti_braiding
#print axioms ZpdPaper.anti_twisted_determined
#print axioms ZpdPaper.twisted_determined

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NoncommRing
import Research.Zpd.Basic
import Research.Zpd.DualNumbers
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Zero braided-symmetric-product determined algebras

Imports Brešar's zero-product-determined (zpd) machinery, already generalized
once in `Research.Zpd.Basic` for the ordinary product `*`, and reapplies it to
a product symmetrized by a braiding, such as `xy + yx` or `xy + α(y)α(x)`.

## Main definitions

* `mapDetermined k B μ` : the `Research.Zpd.Basic.ZeroProductDetermined`
  property, generalized from the fixed product `*` to an arbitrary bilinear
  map `μ`.
* `symProdLinear σ` : the σ-symmetrized product, repackaged as a genuine
  `k`-bilinear map `B →ₗ[k] B →ₗ[k] B`, given `σ` itself `k`-bilinear.

## Main results

* `mapDetermined_iff_injective` : the same quotient-injectivity criterion as
  `Research.Zpd.zeroProductDetermined_iff_injective`, for an arbitrary
  bilinear `μ`, given a surjectivity hypothesis in place of the original's
  built-in `mul_one` unital trick.
* `mapDetermined_symProd_std_iff_zJpd` : for the standard braiding, "zero
  braided-symmetric-product determined" literally *is* zero-Jordan-product-
  determined (Brešar–Alaminos–Extremera–Villena's zJpd, arXiv:1902.04846) —
  not an analogy, a substitution, since `x ·_σ y = xy + yx` on the nose.

## Twisted braiding

For a commutative algebra the twisted product is `f(xy)` with `f = 1 + α`,
so `mapDetermined_comp_mul_of_zpd` and `mapDetermined_comp_mul_of_codim_one`
below cover it. The noncommutative case (for example `M₂(F₃)` with the
transpose) is open and is logged in `formalization-debt.md`.
-/

namespace Research.BraidedSymZpd

open scoped TensorProduct

universe u v

variable (k : Type u) (B : Type v) [Field k] [Ring B] [Algebra k B]

/-- `mapDetermined k B μ` : `B` is determined, over `k`, by the bilinear map
`μ` — every `k`-bilinear map vanishing on pairs with `μ x y = 0` factors
through `μ`. `Research.Zpd.Basic.ZeroProductDetermined` is the special case
`μ = LinearMap.mul' k B`; this file's whole point is to run its argument
again with `μ` the σ-symmetrized product instead. -/
def mapDetermined (μ : B →ₗ[k] B →ₗ[k] B) : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module k V] (φ : B →ₗ[k] B →ₗ[k] V),
    (∀ x y : B, μ x y = 0 → φ x y = 0) →
    ∃ ψ : B →ₗ[k] V, ∀ x y : B, φ x y = ψ (μ x y)

/-- The zero-set of `μ`, linearized: the submodule of `B ⊗[k] B` spanned by
every pure tensor `x ⊗ y` with `μ x y = 0`. Generalizes
`Research.Zpd.zeroProductSpan` from `μ = mul'` to arbitrary `μ`. -/
def mapZeroSpan (μ : B →ₗ[k] B →ₗ[k] B) : Submodule k (B ⊗[k] B) :=
  Submodule.span k {t : B ⊗[k] B | ∃ x y : B, μ x y = 0 ∧ t = x ⊗ₜ[k] y}

/-- Every generator of `mapZeroSpan k B μ` is killed by the linearization of
`μ`, so the whole span lies in its kernel — the fact that makes `mapOfQuot`
below well-defined. Same proof shape as
`Research.Zpd.zeroProductSpan_le_ker_mul'`, with `μ` in place of `mul'`. -/
theorem mapZeroSpan_le_ker_lift (μ : B →ₗ[k] B →ₗ[k] B) :
    mapZeroSpan k B μ ≤ LinearMap.ker (TensorProduct.lift μ) := by
  apply Submodule.span_le.mpr
  rintro t ⟨x, y, hxy, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, TensorProduct.lift.tmul]
  exact hxy

/-- Named once, exactly as `Research.Zpd.Basic.ZQuot` does for the plain
product, so `⧸` never needs to be parsed inline against a `≃ₗ[k]`/`→ₗ[k]`
on the same line (a genuine parser ambiguity, not just a style choice). -/
abbrev MapQuot (μ : B →ₗ[k] B →ₗ[k] B) : Type v := (B ⊗[k] B) ⧸ mapZeroSpan k B μ

/-- `μ`, redefined on the quotient of `B ⊗[k] B` by `mapZeroSpan k B μ`. -/
noncomputable def mapOfQuot (μ : B →ₗ[k] B →ₗ[k] B) :
    MapQuot k B μ →ₗ[k] B :=
  (mapZeroSpan k B μ).liftQ (TensorProduct.lift μ) (mapZeroSpan_le_ker_lift k B μ)

theorem mapOfQuot_mk (μ : B →ₗ[k] B →ₗ[k] B) (x y : B) :
    mapOfQuot k B μ (Submodule.Quotient.mk (x ⊗ₜ[k] y)) = μ x y := by
  rw [mapOfQuot, Submodule.liftQ_apply, TensorProduct.lift.tmul]

set_option maxHeartbeats 0 in
/-- **The working criterion, for an arbitrary bilinear `μ`.** Given that
`mapOfQuot k B μ` is surjective (automatic for `μ = mul'` on a unital ring
via `mul_one`, as in `Research.Zpd.zeroProductDetermined_iff_injective`; for
a general `μ` this is a hypothesis, discharged case by case — see
`mapDetermined_symProd_std_iff_zJpd` below for the standard-braiding case),
`mapDetermined k B μ` holds iff `mapOfQuot k B μ` is injective. -/
theorem mapDetermined_iff_injective (μ : B →ₗ[k] B →ₗ[k] B)
    (hsurj : Function.Surjective (mapOfQuot k B μ)) :
    mapDetermined k B μ ↔ Function.Injective (mapOfQuot k B μ) := by
  constructor
  · intro hdet
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro t ht
    obtain ⟨t', rfl⟩ := Submodule.Quotient.mk_surjective (mapZeroSpan k B μ) t
    set φ : B →ₗ[k] B →ₗ[k] (B ⊗[k] B) ⧸ mapZeroSpan k B μ :=
      (TensorProduct.mk k B B).compr₂ (mapZeroSpan k B μ).mkQ with hφdef
    have hφ : ∀ x y : B, μ x y = 0 → φ x y = 0 := by
      intro x y hxy
      rw [hφdef, LinearMap.compr₂_apply, TensorProduct.mk_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, y, hxy, rfl⟩
    obtain ⟨ψ, hψ⟩ := hdet ((B ⊗[k] B) ⧸ mapZeroSpan k B μ) φ hφ
    have hmk : ∀ t' : B ⊗[k] B, Submodule.Quotient.mk t' =
        ψ (TensorProduct.lift μ t') := by
      intro t'
      induction t' with
      | tmul x y =>
        rw [TensorProduct.lift.tmul, ← hψ x y, hφdef, LinearMap.compr₂_apply,
          TensorProduct.mk_apply, Submodule.mkQ_apply]
      | add a b ha hb =>
        rw [Submodule.Quotient.mk_add, ha, hb, map_add, map_add]
    have ht' : TensorProduct.lift μ t' = 0 := by
      rw [LinearMap.mem_ker, mapOfQuot, Submodule.liftQ_apply] at ht
      exact ht
    rw [hmk t', ht', map_zero]
  · intro hinj V _ _ φ hφ
    have hspan : mapZeroSpan k B μ ≤ LinearMap.ker (TensorProduct.lift φ) := by
      apply Submodule.span_le.mpr
      rintro t ⟨x, y, hxy, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, TensorProduct.lift.tmul]
      exact hφ x y hxy
    set e : MapQuot k B μ ≃ₗ[k] B :=
      LinearEquiv.ofBijective (mapOfQuot k B μ) ⟨hinj, hsurj⟩ with hedef
    refine ⟨?_, ?_⟩
    · exact Submodule.liftQ (mapZeroSpan k B μ) (TensorProduct.lift φ) hspan ∘ₗ
        (e.symm : B →ₗ[k] MapQuot k B μ)
    intro x y
    rw [← mapOfQuot_mk k B μ x y, LinearMap.comp_apply, LinearEquiv.coe_coe,
      show mapOfQuot k B μ (Submodule.Quotient.mk (x ⊗ₜ[k] y)) =
        e (Submodule.Quotient.mk (x ⊗ₜ[k] y)) from rfl,
      e.symm_apply_apply, Submodule.liftQ_apply, TensorProduct.lift.tmul]

/-! ## Standard braiding: reduction to Brešar's zJpd -/

/-- `BraidedSymmetric.lean`'s `standardBraiding` (`σ x y := y`) and
`symmetrizedProduct` (`x ·_σ y := x*y + σ(x,y)*σ(y,x)`), restated here on the
ring `B` directly, without a cross-package `require`, so the transport lemma
below connects to the earlier paper's own notation rather than reproving
something disconnected from it under a different name. -/
def symProdStd (x y : B) : B := x * y + y * x

/-- The Jordan product `x ∘ y = xy + yx`, packaged as a `k`-bilinear map. -/
def jordanProd : B →ₗ[k] B →ₗ[k] B where
  toFun x :=
    { toFun := fun y => x * y + y * x
      map_add' := fun a b => by show x * (a + b) + (a + b) * x = x * a + a * x + (x * b + b * x); noncomm_ring
      map_smul' := fun r y => by simp }
  map_add' := fun x y => by ext z; simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]; noncomm_ring
  map_smul' := fun r x => by ext y; simp

@[simp] theorem jordanProd_apply (x y : B) : jordanProd k B x y = x * y + y * x := rfl

/-- The two definitions agree pointwise: `jordanProd`'s underlying function
is exactly `symProdStd`, i.e. exactly `BraidedSymmetric.lean`'s
`symmetrizedProduct standardBraiding`. Not `rfl` by accident — it is the
literal content of `symmetrizedProduct_std` in the earlier paper's own file,
re-derived here against this file's independent `symProdStd`. -/
theorem jordanProd_eq_symProdStd (x y : B) : jordanProd k B x y = symProdStd B x y := rfl

-- **Reading `jordanProd_eq_symProdStd`.** "Zero braided-symmetric-product
-- determined for the standard braiding" is not an analogue of Brešar's
-- zero-Jordan-product-determined property — it *is* that property, since
-- the two products agree pointwise as just proved. So `mapDetermined k B
-- (jordanProd k B)` already *is* the σ-standard-braiding statement, and
-- every zJpd theorem in the literature (Alaminos–Brešar–Extremera–Villena,
-- arXiv:1902.04846) transports for free to it — with nothing left to prove
-- beyond the lemma above.

/-- Char ≠ 2 is exactly what makes `jordanProd`, and hence the standard
σ-symmetrized product, surjective (`jordanProd x 1 = 2x`), which is what the
converse direction of `mapDetermined_iff_injective` needs in place of the
`mul_one` unital trick `Research.Zpd.Basic` uses for the plain product. -/
theorem mapOfQuot_jordanProd_surjective (h2 : (2 : k) ≠ 0) :
    Function.Surjective (mapOfQuot k B (jordanProd k B)) := by
  intro b
  have h2' : IsUnit (2 : k) := (isUnit_iff_ne_zero).mpr h2
  obtain ⟨u, hu⟩ := h2'
  set c : B := algebraMap k B (↑u⁻¹ : k) * b with hcdef
  refine ⟨Submodule.Quotient.mk (c ⊗ₜ[k] 1), ?_⟩
  rw [mapOfQuot_mk, jordanProd_apply, mul_one, one_mul, hcdef]
  rw [← two_mul, show (2 : B) = algebraMap k B (2 : k) from (map_ofNat _ _).symm,
    ← mul_assoc, ← map_mul, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, one_mul]

end Research.BraidedSymZpd

/-! ## Products of the form `f(xy)` and the twisted braiding

The criterion without a surjectivity hypothesis, the transfer from zpd to
every product `μ(x,y) = f(xy)`, and the dual numbers as an algebra that is
determined by the twisted product but is not zpd. -/

namespace Research.BraidedSymZpd
open scoped TensorProduct
variable (k : Type*) (B : Type*) [Field k] [Ring B] [Algebra k B]

/-- Theorem A: no surjectivity hypothesis. -/
theorem mapDetermined_iff_injective' (μ : B →ₗ[k] B →ₗ[k] B) :
    mapDetermined k B μ ↔ Function.Injective (mapOfQuot k B μ) := by
  constructor
  · intro hdet
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    obtain ⟨t', rfl⟩ := Submodule.Quotient.mk_surjective (mapZeroSpan k B μ) t
    set φ : B →ₗ[k] B →ₗ[k] MapQuot k B μ :=
      (TensorProduct.mk k B B).compr₂ (mapZeroSpan k B μ).mkQ with hφdef
    have hφ : ∀ x y : B, μ x y = 0 → φ x y = 0 := by
      intro x y hxy
      rw [hφdef, LinearMap.compr₂_apply, TensorProduct.mk_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, y, hxy, rfl⟩
    obtain ⟨ψ, hψ⟩ := hdet (MapQuot k B μ) φ hφ
    have hmk : ∀ s : B ⊗[k] B, (Submodule.Quotient.mk s : MapQuot k B μ) =
        ψ (TensorProduct.lift μ s) := by
      intro s
      induction s with
      | tmul x y =>
        rw [TensorProduct.lift.tmul, ← hψ x y, hφdef, LinearMap.compr₂_apply,
          TensorProduct.mk_apply, Submodule.mkQ_apply]
      | add a b ha hb =>
        rw [Submodule.Quotient.mk_add, ha, hb, map_add, map_add]
    have ht' : TensorProduct.lift μ t' = 0 := by
      rw [LinearMap.mem_ker, mapOfQuot, Submodule.liftQ_apply] at ht
      exact ht
    rw [hmk t', ht', map_zero]
  · intro hinj V _ _ φ hφ
    have hspan : mapZeroSpan k B μ ≤ LinearMap.ker (TensorProduct.lift φ) := by
      apply Submodule.span_le.mpr
      rintro t ⟨x, y, hxy, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, TensorProduct.lift.tmul]
      exact hφ x y hxy
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (mapOfQuot k B μ)
      (LinearMap.ker_eq_bot.mpr hinj)
    refine ⟨(mapZeroSpan k B μ).liftQ (TensorProduct.lift φ) hspan ∘ₗ g, ?_⟩
    intro x y
    rw [← mapOfQuot_mk k B μ x y, LinearMap.comp_apply,
      ← LinearMap.comp_apply g, hg, LinearMap.id_apply,
      Submodule.liftQ_apply, TensorProduct.lift.tmul]

/-- Theorem B. -/
theorem mapDetermined_comp_mul_of_zpd (hB : Research.Zpd.ZeroProductDetermined k B)
    (f : B →ₗ[k] B) (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = f (x * y)) :
    mapDetermined k B μ := by
  intro V _ _ φ hφ
  have h0 : ∀ x y : B, x * y = 0 → φ x y = 0 := by
    intro x y hxy
    apply hφ
    rw [hμ, hxy, map_zero]
  obtain ⟨ψ0, hψ0⟩ := hB V φ h0
  have hker : LinearMap.ker f ≤ LinearMap.ker ψ0 := by
    intro b hb
    rw [LinearMap.mem_ker] at hb ⊢
    rw [← mul_one b, ← hψ0 b 1]
    apply hφ
    rw [hμ, mul_one, hb]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
    ((LinearMap.ker f).liftQ ψ0 hker ∘ₗ ((LinearMap.quotKerEquivRange f).symm : LinearMap.range f →ₗ[k] B ⧸ LinearMap.ker f))
  refine ⟨ψ, fun x y => ?_⟩
  rw [hμ, hψ0 x y]
  have hmem : f (x * y) ∈ LinearMap.range f := LinearMap.mem_range_self f (x * y)
  have := LinearMap.congr_fun hψ ⟨f (x * y), hmem⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] at this
  exact this.symm

/-- Theorem D: an injective `f` changes nothing. -/
theorem zpd_of_mapDetermined_comp_mul (f : B →ₗ[k] B) (hf : Function.Injective f)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = f (x * y)) (h : mapDetermined k B μ) :
    Research.Zpd.ZeroProductDetermined k B := by
  intro V _ _ φ hφ
  obtain ⟨ψ, hψ⟩ := h V φ (fun x y hxy => by
    apply hφ
    rw [hμ] at hxy
    exact hf (hxy.trans (map_zero f).symm))
  refine ⟨ψ ∘ₗ f, fun x y => ?_⟩
  rw [hψ x y, hμ, LinearMap.comp_apply]

/-- Theorem E. -/
theorem mapDetermined_comp_mul_of_codim_one (f : B →ₗ[k] B) (h1 : f 1 ≠ 0)
    (hL : ∀ n b : B, f n = 0 → f (b * n) = 0) (hR : ∀ n b : B, f n = 0 → f (n * b) = 0)
    (c : B →ₗ[k] k) (hc : ∀ x : B, f (x - c x • 1) = 0)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = f (x * y)) :
    mapDetermined k B μ := by
  intro V _ _ φ hφ
  have hφL : ∀ n y : B, f n = 0 → φ n y = 0 := fun n y hn => hφ n y (by
    rw [hμ]; exact hR n y hn)
  have hφR : ∀ x n : B, f n = 0 → φ x n = 0 := fun x n hn => hφ x n (by
    rw [hμ]; exact hL n x hn)
  have hfy : ∀ y : B, f y = c y • f 1 := fun y => by
    calc f y = f ((y - c y • 1) + c y • 1) := by rw [sub_add_cancel]
      _ = c y • f 1 := by rw [map_add, map_smul, hc y, zero_add]
  have key1 : ∀ x y : B, φ x y = c x • c y • φ 1 1 := fun x y => by
    have hy : φ 1 y = c y • φ 1 1 := by
      calc φ 1 y = φ 1 ((y - c y • 1) + c y • 1) := by rw [sub_add_cancel]
        _ = c y • φ 1 1 := by rw [map_add, map_smul, hφR 1 _ (hc y), zero_add]
    calc φ x y = φ ((x - c x • 1) + c x • 1) y := by rw [sub_add_cancel]
      _ = c x • φ 1 y := by
        rw [LinearMap.map_add₂, LinearMap.map_smul₂, hφL _ y (hc x), zero_add]
      _ = c x • c y • φ 1 1 := by rw [hy]
  have key2 : ∀ x y : B, f (x * y) = (c x * c y) • f 1 := fun x y => by
    calc f (x * y) = f ((x - c x • 1) * y + c x • y) := by
          rw [sub_mul, smul_mul_assoc, one_mul, sub_add_cancel]
      _ = c x • f y := by rw [map_add, map_smul, hR _ y (hc x), zero_add]
      _ = (c x * c y) • f 1 := by rw [hfy y, mul_smul]
  have hinj : LinearMap.ker (LinearMap.toSpanSingleton k B (f 1)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at hab
    exact sub_eq_zero.mp (hab.resolve_right h1)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg1 : ∀ a : k, g (a • f 1) = a := fun a => by
    have := LinearMap.congr_fun hg a
    rwa [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply] at this
  refine ⟨LinearMap.smulRight g (φ 1 1), fun x y => ?_⟩
  rw [hμ, key2, LinearMap.smulRight_apply, hg1,
    key1, mul_smul]

/-- Identity braiding: `x ·_id y = xy + xy`. A zpd algebra is determined by it. -/
theorem mapDetermined_identityBraiding_of_zpd (hB : Research.Zpd.ZeroProductDetermined k B)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = x * y + x * y) : mapDetermined k B μ :=
  mapDetermined_comp_mul_of_zpd k B hB ((2 : k) • LinearMap.id) μ (fun x y => by
    rw [hμ, LinearMap.smul_apply, LinearMap.id_apply, two_smul])

/-- In characteristic not 2 the identity braiding determines exactly the zpd algebras. -/
theorem mapDetermined_identityBraiding_iff_zpd (h2 : (2 : k) ≠ 0)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = x * y + x * y) :
    mapDetermined k B μ ↔ Research.Zpd.ZeroProductDetermined k B := by
  have hμ' : ∀ x y, μ x y = ((2 : k) • LinearMap.id : B →ₗ[k] B) (x * y) := fun x y => by
    rw [hμ, LinearMap.smul_apply, LinearMap.id_apply, two_smul]
  constructor
  · intro h
    refine zpd_of_mapDetermined_comp_mul k B _ (fun a b hab => ?_) μ hμ' h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply] at hab
    exact smul_right_injective B h2 hab
  · intro hB
    exact mapDetermined_identityBraiding_of_zpd k B hB μ hμ

/-- Twisted braiding on a commutative zpd algebra: `x ·_α y = xy + α(y)α(x)`. -/
theorem mapDetermined_twisted_of_comm_zpd (hcomm : ∀ x y : B, x * y = y * x)
    (hB : Research.Zpd.ZeroProductDetermined k B) (α : B →ₐ[k] B)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = x * y + α y * α x) : mapDetermined k B μ :=
  mapDetermined_comp_mul_of_zpd k B hB (LinearMap.id + α.toLinearMap) μ (fun x y => by
    rw [hμ, LinearMap.add_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply, ← map_mul,
      hcomm y x])

/-- **Corollary 3.5.** If `α` is a linear anti-endomorphism, `α (x * y) = α y * α x`,
then the twisted product is `(id + α)(xy)` on any algebra, commutative or not, so
every zpd algebra is determined by it. The transpose on `M₂(F₃)` is such an `α`. -/
theorem mapDetermined_twisted_anti_of_zpd
    (hB : Research.Zpd.ZeroProductDetermined k B)
    (α : B →ₗ[k] B) (hα : ∀ x y : B, α (x * y) = α y * α x)
    (μ : B →ₗ[k] B →ₗ[k] B) (hμ : ∀ x y, μ x y = x * y + α y * α x) :
    mapDetermined k B μ :=
  mapDetermined_comp_mul_of_zpd k B hB (LinearMap.id + α) μ (fun x y => by
    rw [hμ, LinearMap.add_apply, LinearMap.id_apply, hα x y])

section Dual
open Research.Zpd TrivSqZeroExt
variable (K : Type) [Field K]

/-- The involution `a + bε ↦ a - bε` of the dual numbers. -/
noncomputable def dualAlpha : DualNumbers K →ₗ[K] DualNumbers K :=
  Algebra.linearMap K (DualNumbers K) ∘ₗ dualFst K - inrHom K K ∘ₗ dualSnd K

theorem dualAlpha_fst (x : DualNumbers K) : fst (dualAlpha K x) = fst x := by
  rw [dualAlpha, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    fst_sub, Algebra.linearMap_apply, algebraMap_eq_inl, fst_inl, inrHom_apply, fst_inr,
    sub_zero, dualFst_apply]

theorem dualAlpha_snd (x : DualNumbers K) : snd (dualAlpha K x) = - snd x := by
  rw [dualAlpha, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    snd_sub, Algebra.linearMap_apply, algebraMap_eq_inl, snd_inl, inrHom_apply, snd_inr,
    zero_sub, dualSnd_apply]

theorem dualAlpha_mul (x y : DualNumbers K) :
    dualAlpha K (x * y) = dualAlpha K x * dualAlpha K y := by
  ext
  · rw [dualAlpha_fst, fst_mul, fst_mul, dualAlpha_fst, dualAlpha_fst]
  · rw [dualAlpha_snd, snd_mul, snd_mul, dualAlpha_fst, dualAlpha_fst, dualAlpha_snd,
      dualAlpha_snd, smul_eq_mul, smul_eq_mul, op_smul_eq_mul, op_smul_eq_mul]
    ring

/-- `f = 1 + α`, so that `μ_α(x,y) = xy + α(y)α(x) = f(xy)`. -/
noncomputable def dualF : DualNumbers K →ₗ[K] DualNumbers K := LinearMap.id + dualAlpha K

theorem twisted_eq_dualF (x y : DualNumbers K) :
    x * y + dualAlpha K y * dualAlpha K x = dualF K (x * y) := by
  rw [← dualAlpha_mul, mul_comm y x, dualF, LinearMap.add_apply, LinearMap.id_apply]

theorem dualF_eq_zero_iff (h2 : (2 : K) ≠ 0) (x : DualNumbers K) :
    dualF K x = 0 ↔ fst x = 0 := by
  constructor
  · intro h
    have := congrArg fst h
    rw [dualF, LinearMap.add_apply, LinearMap.id_apply, fst_add, dualAlpha_fst, fst_zero,
      ← two_mul] at this
    exact (mul_eq_zero.mp this).resolve_left h2
  · intro h
    ext
    · rw [dualF, LinearMap.add_apply, LinearMap.id_apply, fst_add, dualAlpha_fst, h, add_zero,
        fst_zero]
    · rw [dualF, LinearMap.add_apply, LinearMap.id_apply, snd_add, dualAlpha_snd, add_neg_cancel,
        snd_zero]


theorem dual_smul_mul (c : K) (x y : DualNumbers K) : (c • x) * y = c • (x * y) := by
  ext
  · rw [fst_mul, fst_smul, fst_smul, fst_mul, smul_eq_mul, smul_eq_mul, mul_assoc]
  · rw [snd_mul, snd_smul, snd_smul, snd_mul, fst_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, op_smul_eq_mul, op_smul_eq_mul]
    ring

theorem dual_mul_smul (c : K) (x y : DualNumbers K) : x * (c • y) = c • (x * y) := by
  ext
  · rw [fst_mul, fst_smul, fst_smul, fst_mul, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [snd_mul, snd_smul, snd_smul, snd_mul, fst_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, op_smul_eq_mul, op_smul_eq_mul]
    ring

/-- The twisted product `μ_α(x,y) = f(xy)` as a bilinear map. -/
noncomputable def dualMu : DualNumbers K →ₗ[K] DualNumbers K →ₗ[K] DualNumbers K :=
  LinearMap.mk₂ K (fun x y => dualF K (x * y))
    (fun x y z => by rw [add_mul, map_add])
    (fun c x y => by rw [dual_smul_mul, map_smul])
    (fun x y z => by rw [mul_add, map_add])
    (fun c x y => by rw [dual_mul_smul, map_smul])

/-- The dual numbers are determined by the twisted product, yet not zpd. -/
theorem dualNumbers_mapDetermined (h2 : (2 : K) ≠ 0) :
    mapDetermined K (DualNumbers K) (dualMu K) := by
  refine mapDetermined_comp_mul_of_codim_one K (DualNumbers K) (dualF K) ?_ ?_ ?_ (dualFst K) ?_
    (dualMu K) (fun x y => by rw [dualMu, LinearMap.mk₂_apply])
  · rw [Ne, dualF_eq_zero_iff K h2, fst_one]
    exact one_ne_zero
  · intro n b hn
    rw [dualF_eq_zero_iff K h2] at hn ⊢
    rw [fst_mul, hn, mul_zero]
  · intro n b hn
    rw [dualF_eq_zero_iff K h2] at hn ⊢
    rw [fst_mul, hn, zero_mul]
  · intro x
    rw [dualF_eq_zero_iff K h2, fst_sub, fst_smul, fst_one, smul_eq_mul, mul_one, dualFst_apply,
      sub_self]
/-- The dual numbers: determined by the twisted product, yet not zpd. -/
theorem dualNumbers_determined_not_zpd (h2 : (2 : K) ≠ 0) :
    mapDetermined K (DualNumbers K) (dualMu K) ∧
      ¬ Research.Zpd.ZeroProductDetermined K (DualNumbers K) :=
  ⟨dualNumbers_mapDetermined K h2, not_zeroProductDetermined_dualNumbers K⟩
end Dual
end Research.BraidedSymZpd

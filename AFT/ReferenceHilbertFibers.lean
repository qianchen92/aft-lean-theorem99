import AFT.MixedReferenceCanonicalFibers
import AFT.FiniteExpectationAlgebra

/-! # Reference-centered coefficients with arbitrary remaining Hilbert fibers -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color Fiber : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [Fintype Fiber]
local instance referenceHilbertSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

theorem referenceRestrictedComponent_hilbert_square_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0 < (p slot).weight color) (fiber : FiniteDist Fiber)
    (mass : Fiber → (Slot → Color) → ℝ) (selected : Finset Slot) (comparison : ℝ)
    (hc : 1 ≤ comparison) (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color) :
    fiber.expectation (fun rest => (FiniteDist.independent (fun slot : selected => p slot)).l2Sq
      (referenceRestrictedComponent p r (mass rest) selected)) ≤
    ((2*comparison)^selected.card)^2 * fiber.expectation (fun rest =>
      (FiniteDist.independent p).l2Sq (fun word => mass rest word/(FiniteDist.independent p).weight word)) := by
  rw [← FiniteDist.expectation_const_mul]
  exact Finset.sum_le_sum fun rest _ => mul_le_mul_of_nonneg_left
    (referenceRestrictedComponent_l2Sq_le p r hp (mass rest) selected comparison hc hr) (fiber.nonneg rest)

variable [Nonempty Color]

theorem referenceRestrictedComponent_singleton_hilbert_square_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0 < (p slot).weight color) (fiber : FiniteDist Fiber)
    (mass : Fiber → (Slot → Color) → ℝ) (selected : Finset Slot) (comparison full single : ℝ)
    (hc : 1 ≤ comparison) (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hf : fiber.expectation (fun rest => (FiniteDist.independent p).l2Sq
      (fun word => mass rest word/(FiniteDist.independent p).weight word)) ≤ full)
    (hs : ∀ fixed values, fiber.expectation (fun rest => MixedKernel.fiberSq p
      (fun word => mass rest word/(FiniteDist.independent p).weight word) {fixed} values) ≤ single)
    (fixed : selected) (values : selected → Color) :
    fiber.expectation (fun rest => MixedKernel.fiberSq (fun slot : selected => p slot)
      (referenceRestrictedComponent p r (mass rest) selected) {fixed} values) ≤
      ((2*comparison)^selected.card)^2 * (full+single) := by
  simp_rw [referenceRestrictedComponent_singleton_fiberSq_eq p r hp]
  calc
    _ ≤ fiber.expectation (fun rest => ((2*comparison)^selected.card)^2 *
      ((FiniteDist.independent p).l2Sq (fun word => mass rest word/(FiniteDist.independent p).weight word)+
      MixedKernel.fiberSq p (fun word => mass rest word/(FiniteDist.independent p).weight word)
        {fixed.val} _)) := Finset.sum_le_sum fun rest _ => mul_le_mul_of_nonneg_left
          (MixedKernel.referenceProjection_singleton_fiberSq_le p r hp selected _ comparison hc hr fixed.val _)
          (fiber.nonneg rest)
    _ ≤ _ := by
      rw [FiniteDist.expectation_const_mul,FiniteDist.expectation_add]
      exact mul_le_mul_of_nonneg_left (add_le_add hf (hs _ _)) (sq_nonneg _)

/-- An output supremum retains the entire remaining joint fiber. In
particular this estimate has no cardinality of the remaining alphabet. -/
theorem referenceRestrictedComponent_fixed_hilbert_square_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0 < (p slot).weight color) (fiber : FiniteDist Fiber)
    (mass : Fiber → (Slot → Color) → ℝ) (selected : Finset Slot) (comparison bound : ℝ)
    (hc : 1 ≤ comparison) (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hb : ∀ word, fiber.l2Sq (fun rest => mass rest word/(FiniteDist.independent p).weight word) ≤ bound)
    (values : selected → Color) :
    fiber.l2Sq (fun rest => referenceRestrictedComponent p r (mass rest) selected values) ≤
      ((2*comparison)^selected.card)^2*bound := by
  let extended : Slot → Color := fun slot => if h : slot ∈ selected then values ⟨slot,h⟩ else Classical.choice inferInstance
  have he (rest) : referenceRestrictedComponent p r (mass rest) selected values =
      MixedKernel.referenceProjection p r selected
        (fun word => mass rest word/(FiniteDist.independent p).weight word) extended := by
    rw [← referenceRestrictedComponent_eq p r hp]
    congr 1
    funext slot
    simp only [extended,dif_pos slot.property]
  have hc0 : 0 ≤ comparison := le_trans (by norm_num) hc
  simp_rw [he]
  calc
    _ ≤ ∑ rest,fiber.weight rest*(comparison^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ word,(FiniteDist.independent p).weight word*MixedKernel.projectionMajorant p selected word extended*
        (mass rest word/(FiniteDist.independent p).weight word)^2) :=
      Finset.sum_le_sum fun rest _ => mul_le_mul_of_nonneg_left
        (MixedKernel.referenceProjection_square_majorant p r hp selected _ comparison hc hr extended) (fiber.nonneg rest)
    _ = comparison^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ word,(FiniteDist.independent p).weight word*MixedKernel.projectionMajorant p selected word extended*
        fiber.l2Sq (fun rest => mass rest word/(FiniteDist.independent p).weight word) := by
      simp only [FiniteDist.l2Sq,FiniteDist.expectation,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro word _
      apply Finset.sum_congr rfl
      intro rest _
      ring
    _ ≤ comparison^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ word,(FiniteDist.independent p).weight word*MixedKernel.projectionMajorant p selected word extended*bound := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left (hb word)
        (mul_nonneg (FiniteDist.nonneg _ _) (MixedKernel.projectionMajorant_nonneg _ _ _ _))
    _ = _ := by
      rw [← Finset.sum_mul,MixedKernel.projectionMajorant_source p hp selected extended]
      simp only [mul_pow,pow_mul]
      ring

end
end AFT.LocalTensors

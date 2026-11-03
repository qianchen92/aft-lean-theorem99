import CurrentAFT.CurrentAffineGeometry
import CurrentAFT.CurrentSourceProtection
import CurrentAFT.ActualCalibratedPublic

/-! # Safe baselines and public charge on the actual positive core support -/
namespace CurrentAFT.CurrentPublicSupport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem map_property {Source Target : Type*} [Fintype Source] [Fintype Target]
    (law : FiniteDist Source) (record : Source → Target) (property : Target → Prop)
    (hproperty : ∀ source, law.weight source ≠ 0 → property (record source)) :
    ∀ target, (law.map record).weight target ≠ 0 → property target := by
  intro target hweight
  by_contra hbad
  apply hweight
  rw [FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro source _
  split_ifs with hequal
  · by_contra hsource
    exact hbad (hequal ▸ hproperty source hsource)
  · rfl

theorem safeLaw_support (security : ℕ) (color : Fin (Parameters.modulus security))
    (hweight : (safeLaw security).weight color ≠ 0) : InwardAnchor.SafeColor security color := by
  by_contra hbad
  exact hweight (by rw [safeLaw_weight, if_neg hbad])

def SafeCore (security : ℕ) (core : Core security) : Prop :=
  (∀ leg, InwardAnchor.SafeColor security (core.legs leg).2) ∧
    ∀ point, InwardAnchor.SafeColor security (core.queueBaselines point)

theorem proposal_safe (security : ℕ) (core : Core security)
    (hweight : (proposal security).weight core ≠ 0) : SafeCore security core := by
  unfold proposal at hweight
  apply map_property _ _ (SafeCore security) _ core hweight
  intro draw hdraw
  constructor
  · intro leg
    apply safeLaw_support
    intro hzero
    have hleg : (legCoreLaw security).weight (draw.1.1.1.2 leg) = 0 := by
      change (ActualPublicLegCharge.seedLaw security).weight (draw.1.1.1.2 leg).1 *
        (safeLaw security).weight (draw.1.1.1.2 leg).2 = 0
      rw [hzero, mul_zero]
    have hproduct : (∏ index, (legCoreLaw security).weight (draw.1.1.1.2 index)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ leg) hleg
    apply hdraw
    simp only [FiniteDist.prod_weight, FiniteDist.independent, hproduct, mul_zero, zero_mul]
  · intro point
    apply safeLaw_support
    intro hzero
    have hproduct : (∏ index, (safeLaw security).weight (draw.1.1.2 index)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ point) hzero
    apply hdraw
    simp only [FiniteDist.prod_weight, FiniteDist.independent, hproduct, mul_zero, zero_mul]

theorem positiveCore_support {State : Type*} [Fintype State]
    (reference : FiniteDist State) (weight : State → ℝ) (charge : State → Prop)
    (hpositive : 0 < publicCoreMass reference weight charge) (state : State)
    (hweight : (positivePublicCoreLaw reference weight charge hpositive).weight state ≠ 0) :
    charge state ∧ reference.weight state ≠ 0 := by
  change clippedPublicCoreWeight reference weight charge state /
    (∑ value, clippedPublicCoreWeight reference weight charge value) ≠ 0 at hweight
  have hnumerator := (div_ne_zero_iff.mp hweight).1
  unfold clippedPublicCoreWeight at hnumerator
  by_cases hcharge : charge state
  · rw [if_pos hcharge] at hnumerator
    exact ⟨hcharge, (mul_ne_zero_iff.mp hnumerator).1⟩
  · simp only [if_neg hcharge, ne_eq, not_true_eq_false] at hnumerator

theorem positive_safe (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (core : Core security)
    (hweight : (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).weight core ≠ 0) :
    publicCharge security core ∧ SafeCore security core := by
  have hsupport := positiveCore_support (proposal security) weight (publicCharge security) hpositive core hweight
  exact ⟨hsupport.1, proposal_safe security core hsupport.2⟩

theorem centerAt_safe (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hsafe : SafeCore security core) (vertex : BodyIndex security) :
    (Parameters.safeMargin security : ℤ) ≤ centerAt security layout core vertex ∧
      centerAt security layout core vertex < (Parameters.modulus security : ℤ) - Parameters.safeMargin security := by
  unfold centerAt
  generalize layout.symm vertex = role
  rcases role with center | (point | leg)
  · exact (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.property
  · exact hsafe.2 point
  · exact hsafe.1 leg

theorem body_carry_zero (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hsafe : SafeCore security core) (vertex : BodyIndex security)
    (increment : ℤ) (hbound : |increment| ≤ Parameters.safeMargin security) :
    (centerAt security layout core vertex + increment) / Parameters.modulus security = 0 ∧
      (centerAt security layout core vertex + increment) % Parameters.modulus security =
        centerAt security layout core vertex + increment := by
  have hcenter := centerAt_safe security layout core hsafe vertex
  have hincrement := abs_le.mp hbound
  have hlo : 0 ≤ centerAt security layout core vertex + increment := by omega
  have hhi : centerAt security layout core vertex + increment < Parameters.modulus security := by omega
  exact ⟨Int.ediv_eq_zero_of_lt hlo hhi, Int.emod_eq_of_lt hlo hhi⟩

end
end CurrentAFT.CurrentPublicSupport

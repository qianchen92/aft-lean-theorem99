import CurrentAFT.RootLegFirstCoefficient

/-! One actual pure-primary normalized channel for every unselected physical block. -/

namespace CurrentAFT.RootUnselectedBlockChannel

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock UniformBodyProfiles CycleSelections CycleRootExpansion RootTaggedLocal
  RootTaggedFamilies RootUnselectedChannels RootLegCoefficientBounds RootLegCoefficientLinear
  RootLegFirstCoefficient PrimaryOnlyFamily BackgroundFamilies BackgroundRates BackgroundEvaluation
  ControlCoordinates GradedControlAlgebra GradedControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def channel (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) :
    BlockIndex security → ((Root security → ℝ) →ₗ[ℝ] ActualFamily security order)
  | .inl _ => legChannel security order horder
  | .inr (.inl _) => singletonChannel security order horder .free 0
  | .inr (.inr _) => singletonChannel security order horder .queue queue

def positivePolynomial (security : ℕ) (queue : ℤ) : BlockIndex security → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl _ => LegPolynomialEvaluation.legGenerating security
  | .inr (.inl _) => singleGenerating (uniformReference security).weight (meanLaw security .free 0).weight
  | .inr (.inr _) => singleGenerating (uniformReference security).weight (meanLaw security .queue queue).weight

def numeratorPolynomial (security : ℕ) (queue : ℤ) (input : Root security → ℝ) :
    BlockIndex security → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl _ => centeredGeneratingLinear (uniformReference security).weight (RootTaggedLegHigher.massLinear security input)
  | .inr (.inl _) => profileForm (rootMass security .free 0 input)
  | .inr (.inr _) => profileForm (rootMass security .queue queue input)

theorem channel_physical (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (input : Root security → ℝ) :
    evaluation security order (channel security order horder queue block input) *
      TruncatedOutput.quotientMap order (positivePolynomial security queue block) =
        TruncatedOutput.quotientMap order (numeratorPolynomial security queue input block) := by
  rcases block with leg | singleton
  · exact actual_legChannel_physical security order horder input
  · rcases singleton with center | point
    · exact singletonChannel_physical security order horder .free 0 input
    · exact singletonChannel_physical security order horder .queue queue input

theorem channel_primaryOnly (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (input : Root security → ℝ) :
    PrimaryOnly (primaryLaw security) (bodyReference security) order (channel security order horder queue block input) := by
  rcases block with leg | singleton
  · exact legChannel_primaryOnly security order horder input
  · rcases singleton with center | point
    · exact singletonChannel_primaryOnly security order horder .free 0 input
    · exact singletonChannel_primaryOnly security order horder .queue queue input

def channelConstant : ℝ := 8256 + 2 * RootLegCoefficientBounds.higherConstant

theorem channelConstant_nonneg : 0 ≤ channelConstant := by
  unfold channelConstant RootLegCoefficientBounds.higherConstant
  positivity

theorem raw_first_cost_decay (security : ℕ) :
    primaryFactor security * rootCost security ≤ 4128 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  rw [primaryFactor_eq]
  exact (mul_le_mul_of_nonneg_left (rootCost_decay security) (by positivity)).trans_eq (by field_simp)

theorem combined_cost_decay (security : ℕ) :
    2 * (primaryFactor security * rootCost security + higherCost security) ≤
      channelConstant / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hconstant : 0 ≤ RootLegCoefficientBounds.higherConstant := by
    unfold RootLegCoefficientBounds.higherConstant
    positivity
  have hhigher : higherCost security ≤ RootLegCoefficientBounds.higherConstant / (Parameters.base security : ℝ) ^ 94 :=
    (higherCost_decay security).trans (div_le_div_of_nonneg_left hconstant (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega)))
  exact (mul_le_mul_of_nonneg_left (add_le_add (raw_first_cost_decay security) hhigher) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold channelConstant; ring)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ, ∀ block : BlockIndex security, ∀ input : Root security → ℝ,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (channel security order horder queue block input) ≤
          channelConstant / (Parameters.base security : ℝ) ^ 94 * Real.sqrt ((rootReference security).l2Sq input) := by
  filter_upwards [legChannel_norm_eventually order horder] with security hleg queue block input
  rcases block with leg | singleton
  · exact (hleg input).trans (mul_le_mul_of_nonneg_right (combined_cost_decay security) (Real.sqrt_nonneg _))
  · have hsingle : 2 * primaryFactor security * rootCost security ≤ channelConstant / (Parameters.base security : ℝ) ^ 94 := by
      have hh : 0 ≤ higherCost security := by unfold higherCost; positivity
      exact (by nlinarith : 2 * primaryFactor security * rootCost security ≤
        2 * (primaryFactor security * rootCost security + higherCost security)).trans (combined_cost_decay security)
    rcases singleton with center | point
    · exact (singletonChannel_norm security order horder .free 0 input).trans
        (mul_le_mul_of_nonneg_right hsingle (Real.sqrt_nonneg _))
    · exact (singletonChannel_norm security order horder .queue queue input).trans
        (mul_le_mul_of_nonneg_right hsingle (Real.sqrt_nonneg _))

theorem population_tag_cost (security : ℕ) :
    (Parameters.bodySize security : ℝ) * (channelConstant / (Parameters.base security : ℝ) ^ 94) * currentRootTag security ≤
      (131074 * channelConstant) / (Parameters.base security : ℝ) ^ 13 := by
  have hb := FirstResponse.base_pos security
  have hbodyNat : Parameters.bodySize security ≤ 131074 * Parameters.base security ^ 160 :=
    (Nat.le_add_right _ _).trans (Parameters.dimension_bounds security).2
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast hbodyNat
  rw [currentRootTag_eq]
  calc
    _ ≤ (131074 * (Parameters.base security : ℝ) ^ 160) *
        (channelConstant / (Parameters.base security : ℝ) ^ 94) * (1 / (Parameters.base security : ℝ) ^ 79) := by
      gcongr
      exact div_nonneg channelConstant_nonneg (by positivity)
    _ = _ := by field_simp

end
end CurrentAFT.RootUnselectedBlockChannel

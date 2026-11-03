import CurrentAFT.RootLegReciprocal

/-! Actual normalized unselected root channels, with pure-primary reciprocals. -/

namespace CurrentAFT.RootUnselectedChannels

open AFT DiffuseProfiles ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion
  RootTaggedLocal RootTaggedFamilies RootLegCoefficientFamily RootLegCoefficientLinear RootLegCoefficientBounds
  RootLegReciprocal PrimaryOnlyFamily ControlCoordinates GradedControlAlgebra
  GradedControlNorm GradedControlStability BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem rootFamily_primaryOnly (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) : PrimaryOnly (primaryLaw security) (bodyReference security) order
      (rootFamilyLinear security order horder role queue input) := by
  rw [rootFamilyLinear_apply]
  unfold primaryFamily
  exact primaryOnly_single _ _ _ _ rfl _

theorem rootHigher_primaryOnly (security order : ℕ) (input : Root security → ℝ) :
    PrimaryOnly (primaryLaw security) (bodyReference security) order (rootHigherLinear security order input) := by
  rw [rootHigherLinear_apply]
  unfold rootHigherFamily higherFamily
  apply primaryOnly_sum
  intro selected _
  exact selected_primaryOnly security order _ selected

def singletonChannel (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order where
  toFun input := rootFamilyLinear security order horder role queue input * RootMeanPrimary.positiveInverse security order horder role queue
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar input := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply]

theorem singletonChannel_primaryOnly (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) : PrimaryOnly (primaryLaw security) (bodyReference security) order
      (singletonChannel security order horder role queue input) :=
  primaryOnly_mul _ _ _ _ _ (rootFamily_primaryOnly security order horder role queue input)
    (rootMean_positiveInverse_primaryOnly security order horder role queue)

theorem singletonChannel_mul_positive (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) : singletonChannel security order horder role queue input *
      RootMeanPrimary.positiveFamily security order horder role queue = rootFamilyLinear security order horder role queue input := by
  change (_ * RootMeanPrimary.positiveInverse security order horder role queue) * _ = _
  rw [mul_assoc, RootMeanPrimary.positiveInverse_mul, mul_one]

theorem singletonChannel_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) : familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (singletonChannel security order horder role queue input) ≤
        (2 * primaryFactor security * rootCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_product_le _ _ _ _ _ hp hb _ _).trans
  exact (mul_le_mul (rootFamily_norm security order horder role queue input)
    (RootMeanPrimary.positiveInverse_norm security order horder role queue)
    (familyNorm_nonneg _ _ _ _ _ hp hb _) (by positivity [rootCost_nonneg security])).trans_eq (by ring)

theorem singletonChannel_physical (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    evaluation security order (singletonChannel security order horder role queue input) *
      TruncatedOutput.quotientMap order (AFT.RepresentedPolynomial.singleGenerating
        (LocalReferenceEnergy.uniformReference security).weight (meanLaw security role queue).weight) =
      TruncatedOutput.quotientMap order (AFT.RepresentedPolynomial.profileForm (rootMass security role queue input)) := by
  rw [← RootMeanPrimary.positiveFamily_image security order horder role queue,
    ← map_mul, singletonChannel_mul_positive, rootFamily_image]

def legNumeratorLinear (security order : ℕ) (horder : 1 ≤ order) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  rootFamilyLinear security order horder .attachment 0 + rootHigherLinear security order

def legChannel (security order : ℕ) (horder : 1 ≤ order) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order where
  toFun input := legNumeratorLinear security order horder input * reciprocal security order
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar input := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply]

theorem legChannel_primaryOnly (security order : ℕ) (horder : 1 ≤ order) (input : Root security → ℝ) :
    PrimaryOnly (primaryLaw security) (bodyReference security) order (legChannel security order horder input) := by
  apply primaryOnly_mul _ _ _ _ _ _ (reciprocal_primaryOnly security order)
  exact primaryOnly_add _ _ _ _ _ (rootFamily_primaryOnly security order horder .attachment 0 input)
    (rootHigher_primaryOnly security order input)

theorem legChannel_mul_positive (security order : ℕ) (horder : 1 ≤ order) (input : Root security → ℝ) :
    legChannel security order horder input * positive security order = legNumeratorLinear security order horder input := by
  change (_ * reciprocal security order) * _ = _
  rw [mul_assoc, reciprocal_mul, mul_one]

theorem legNumerator_norm (security order : ℕ) (horder : 1 ≤ order) (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (legNumeratorLinear security order horder input) ≤
        (primaryFactor security * rootCost security + higherCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  change familyNorm _ _ _ _ _ (_ + _) ≤ _
  exact (familyNorm_add_le _ _ _ _ _ hp hb _ _).trans
    ((add_le_add (rootFamily_norm security order horder .attachment 0 input)
      (rootHigher_norm security order input)).trans_eq (by ring))

theorem legChannel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ input : Root security → ℝ,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (legChannel security order horder input) ≤
          2 * (primaryFactor security * rootCost security + higherCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  filter_upwards [reciprocal_norm_eventually order] with security hinverse input
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_product_le _ _ _ _ _ hp hb _ _).trans
  have hcost : 0 ≤ higherCost security := by unfold higherCost; positivity
  exact (mul_le_mul (legNumerator_norm security order horder input) hinverse
    (familyNorm_nonneg _ _ _ _ _ hp hb _) (by positivity [rootCost_nonneg security])).trans_eq (by ring)

end
end CurrentAFT.RootUnselectedChannels

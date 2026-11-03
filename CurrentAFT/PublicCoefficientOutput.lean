import CurrentAFT.PublicOutputBridge
import CurrentAFT.CurrentPhysicalNumbering
import CurrentAFT.SymmetrizedOutputRename

/-! # The literal public coefficient weight produces the constructed mass -/
namespace CurrentAFT.PublicCoefficientOutput
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels PublicOutputExperiment PublicOutputBridge
  ControlCoordinates CoefficientOutputFock ActualFockBound
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

def conditionalFamilyMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  coefficient.1 * BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) word +
    ∑ arity : PositiveArity order,
      (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
        (body_room security order hroom arity)).expectation (fun choice =>
          TaggedOutputFock.conditionalMass security arity.val.1.val arity.val.2.val
            (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation latent
            (coefficient.2 arity).val (word ∘ gather (selection security arity.val.1.val arity.val.2.val choice)))

theorem weightedConditionalMass_eq (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    weightedConditionalMass security order layout queue permutation latent coefficient word =
      conditionalFamilyMass security order hroom layout queue permutation latent coefficient word := by
  have hweight (controls : PublicWord security) : actualWeight security order coefficient controls =
      coefficient.1 + ∑ arity : PositiveArity order,
        (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
          (body_room security order hroom arity)).expectation (fun choice =>
            selectedScore security arity.val.1.val arity.val.2.val (coefficient.2 arity).val
              (controls ∘ placedEmbedding choice)) := by
    unfold actualWeight PhysicalSynthesis.coefficientWeight
    congr 1
    apply Finset.sum_congr rfl
    intro arity _
    exact statistic_choice_average security arity.val.1.val arity.val.2.val
      (primary_room security order hroom arity) (body_room security order hroom arity) (coefficient.2 arity).val controls
  unfold weightedConditionalMass conditionalFamilyMass
  simp_rw [hweight, add_mul, Finset.sum_mul]
  rw [FiniteDist.expectation_add, FiniteDist.expectation_const_mul, positive_public_average,
    FiniteDist.expectation_sum]
  apply congrArg (fun value : ℝ => coefficient.1 *
    BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) word + value)
  apply Finset.sum_congr rfl
  intro arity _
  simp_rw [← FiniteDist.expectation_mul_const]
  rw [FiniteDist.expectation_comm]
  apply congrArg (FiniteDist.expectation _)
  funext choice
  exact placed_weighted_mass security arity.val.1.val arity.val.2.val choice layout queue permutation latent word (coefficient.2 arity).val

def outputLawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (controls : PublicWord security) :
    FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  (FiniteDist.retype (latentLaw security)).mix (fun latent => conditionalLaw security layout queue permutation latent controls)

def physicalFamilyMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (FiniteDist.retype (latentLaw security)).expectation (fun latent => conditionalFamilyMass security order hroom layout queue permutation latent coefficient word)

/-- This is the actual positive protected-source experiment, with its
public coefficient weight outside the entire closed-cycle source average. -/
def weightedPhysicalMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (outputLawGiven security layout queue permutation controls).weight word)

theorem weightedPhysicalMass_eq (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    weightedPhysicalMass security order layout queue permutation coefficient word =
      physicalFamilyMass security order hroom layout queue permutation coefficient word := by
  unfold weightedPhysicalMass outputLawGiven physicalFamilyMass
  simp only [FiniteDist.mix_weight]
  change (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (FiniteDist.retype (latentLaw security)).expectation (fun latent => (conditionalLaw security layout queue permutation latent controls).weight word)) = _
  simp_rw [← FiniteDist.expectation_const_mul]
  rw [FiniteDist.expectation_comm]
  apply congrArg (FiniteDist.expectation _)
  funext latent
  exact weightedConditionalMass_eq security order hroom layout queue permutation latent coefficient word

theorem physicalFamilyMass_formula (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    physicalFamilyMass security order hroom layout queue permutation coefficient word =
      coefficient.1 * (FiniteDist.retype (outputLaw security layout queue permutation)).weight word +
        ∑ arity : PositiveArity order,
          (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
            (body_room security order hroom arity)).expectation (fun choice =>
              TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
                (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation (coefficient.2 arity).val
                (word ∘ gather (selection security arity.val.1.val arity.val.2.val choice))) := by
  have hbaseline : (FiniteDist.retype (latentLaw security)).expectation (fun latent =>
      BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) word) =
      (FiniteDist.retype (outputLaw security layout queue permutation)).weight word := by
    rw [FiniteDist.expectation_retype]
    simp only [outputLaw, FiniteDist.retype_weight, FiniteDist.mix_weight]
    rfl
  unfold physicalFamilyMass conditionalFamilyMass
  rw [FiniteDist.expectation_add, FiniteDist.expectation_const_mul, FiniteDist.expectation_sum, hbaseline]
  congr 1
  apply Finset.sum_congr rfl
  intro arity _
  rw [FiniteDist.expectation_comm]
  apply congrArg (FiniteDist.expectation _)
  funext choice
  rw [FiniteDist.expectation_retype]
  rfl

/-- The arithmetic endpoint numbering is executable. Uniform endpoint
permutations make the resulting distribution invariant under this choice. -/
def flatten (security : ℕ) : Sigma (Slots security) ≃ Fin (Parameters.dimension security) :=
  CurrentPhysicalNumbering.numbering security

theorem symmetrized_physicalFamily_eq (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) :
    HistogramNormalization.symmetrizedMass
      (HistogramNormalization.renamedMass (flatten security)
        (physicalFamilyMass security order hroom layout queue permutation coefficient)) =
      HistogramNormalization.symmetrizedMass (familyMass security order hroom layout queue permutation coefficient) := by
  unfold HistogramNormalization.renamedMass
  simp_rw [physicalFamilyMass_formula]
  unfold familyMass
  rw [SymmetrizedOutputRename.add, SymmetrizedOutputRename.add,
    SymmetrizedOutputRename.smul, SymmetrizedOutputRename.smul,
    SymmetrizedOutputRename.sum, SymmetrizedOutputRename.sum]
  funext word
  apply congrArg₂ (fun first second : ℝ => first + second)
  · apply congrArg (fun value : ℝ => coefficient.1 * value)
    exact congrFun (SymmetrizedOutputRename.renamings (flatten security)
      (Fintype.equivFinOfCardEq (physical_card security))
      (FiniteDist.retype (outputLaw security layout queue permutation)).weight) word
  · apply Finset.sum_congr rfl
    intro arity _
    unfold uMass
    rw [SymmetrizedOutputRename.average, SymmetrizedOutputRename.average]
    apply congrArg (FiniteDist.expectation _)
    funext choice
    have h := SymmetrizedOutputRename.renamings
      ((gather (selection security arity.val.1.val arity.val.2.val choice)).trans (flatten security))
      (outputEquiv (selection security arity.val.1.val arity.val.2.val choice))
      (TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
        (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation (coefficient.2 arity).val)
    exact congrFun h word

end
end CurrentAFT.PublicCoefficientOutput

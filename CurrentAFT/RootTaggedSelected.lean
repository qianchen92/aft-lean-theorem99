import CurrentAFT.RootIndependentBackground
import CurrentAFT.LocalRaisingBounds
import CurrentAFT.RaisingBodySlots
import CurrentAFT.FixedPairedFirst

/-!
# Selected primary groups with their two actual roots

The compensator and attachment roots are integrated together with one
joint primary score. The same protected scalar is used in the leg pair
and attachment. A root tag is an argument of this joint score; two tags
in one group do not duplicate its public-control norm. No root atom is
inverted, so the actual reference may have zero weights.
-/
namespace CurrentAFT.RootTaggedSelected

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev RootPair (security : ℕ) := Root security × Root security
abbrev Sample (security : ℕ) := RootPair security × FirstHistogram.Scalar security

def rootsLaw (security : ℕ) : FiniteDist (RootPair security) :=
  (rootReference security).prod (rootReference security)

def sourceLaw (security : ℕ) : FiniteDist (Sample security) :=
  (rootsLaw security).prod (scalarLaw security)

def inputEnergy (security : ℕ) (score : RootPair security → Palette security → ℝ) : ℝ :=
  (rootsLaw security).expectation (fun roots => (primaryLaw security).l2Sq (score roots))

theorem inputEnergy_nonneg (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    0 ≤ inputEnergy security score :=
  Finset.sum_nonneg (fun roots _ => mul_nonneg ((rootsLaw security).nonneg roots) ((primaryLaw security).l2Sq_nonneg _))

def massLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) :=
  ∑ sample : Sample security, (sourceLaw security).weight sample •
    ((pairedMassLinear security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).comp
      (LinearMap.proj sample.1))

def mass (security : ℕ) (score : RootPair security → Palette security → ℝ) := massLinear security score

theorem mass_eq_joint (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    mass security score = jointPairedMass security (sourceLaw security)
      (fun sample => (sample.1.1.val : ℤ)) (fun sample => (sample.1.2.val : ℤ))
      (fun sample => sample.2) (fun sample => score sample.1) := by
  funext word
  simp only [mass, massLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, pairedMassLinear_apply, jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem source_score_energy (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    (sourceLaw security).expectation (fun sample => (primaryLaw security).l2Sq (score sample.1)) =
      inputEnergy security score := by
  unfold sourceLaw
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]
  rfl

theorem mass_zero (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    (∑ word, mass security score word) = 0 := by
  rw [mass_eq_joint]
  unfold jointPairedMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, fixedMass_sum, hcentered, mul_zero, Finset.sum_const_zero]

/-- This is the same complete paired physical experiment, before any
coefficient extraction or normalization. Both roots use the same score. -/
theorem mass_physical_expectation (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, mass security score word * value word) =
      (sourceLaw security).expectation (fun sample =>
        (groupLaw security).expectation (fun group => pairedChannel security (score sample.1) group *
          (fixedControlLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 group).expectation value)) := by
  rw [mass_eq_joint]
  simp only [jointPairedMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro sample _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact fixedMass_expectation security _ _ sample.2 (score sample.1) value

theorem mass_full_energy (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (mass security score) ≤ (4128 * pairBudget security) * inputEnergy security score := by
  rw [mass_eq_joint]
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  apply (profileSquareNorm_average_le (sourceLaw security) reference.weight reference.nonneg _).trans
  calc
    _ ≤ ∑ sample, (sourceLaw security).weight sample * ((4128 * pairBudget security) *
        (primaryLaw security).l2Sq (score sample.1)) := by
      apply Finset.sum_le_sum
      intro sample _
      exact mul_le_mul_of_nonneg_left (pairedMassAt_energy security _ _ sample.2 (score sample.1))
        ((sourceLaw security).nonneg sample)
    _ = _ := by
      change (sourceLaw security).expectation (fun sample => (4128 * pairBudget security) *
        (primaryLaw security).l2Sq (score sample.1)) = _
      rw [FiniteDist.expectation_const_mul, source_score_energy]

def firstConstant : ℝ := 16 + 1310740 * Real.exp Real.pi

theorem mass_first_energy (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (mass security score) 1) ≤ firstConstant * (Parameters.base security : ℝ) ^ 31 * inputEnergy security score := by
  rw [mass_eq_joint]
  have h := jointPaired_first_polynomial security (sourceLaw security)
    (fun sample => (sample.1.1.val : ℤ)) (fun sample => (sample.1.2.val : ℤ))
    (fun sample => sample.2) (fun sample => score sample.1) (fun sample => hcentered sample.1)
  change _ ≤ firstConstant * (Parameters.base security : ℝ) ^ 31 *
    (sourceLaw security).expectation (fun sample => (primaryLaw security).l2Sq (score sample.1)) at h
  rwa [source_score_energy] at h

def normalizedResponse (security order : ℕ) (score : RootPair security → Palette security → ℝ) : Family security order :=
  NormalizedLocalPolynomial.normalizedFamily security order (independentPositiveLaw security) (mass security score)

theorem normalizedResponse_physical_identity (security order : ℕ) (score : RootPair security → Palette security → ℝ) :
    BackgroundEvaluation.evaluation security order (normalizedResponse security order score) *
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (uniformReference security).weight (independentPositiveLaw security).weight) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (uniformReference security).weight (mass security score)) :=
  normalizedFamily_physical_identity security order _ _ (BackgroundEvaluation.bodyForm security)
    (BackgroundEvaluation.bodyForm_homogeneous security)

theorem normalizedResponse_vanishesBelow_one (security order : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (normalizedResponse security order score) :=
  GradedInverse.vanishesBelow_mul _ _ order 1 0 _ _
    (completeFamily_vanishes_one security order _ (mass_zero security score hcentered))
    (GradedInverse.vanishesBelow_zero _ _ order _)

theorem normalizedResponse_no_body (security order : ℕ) (score : RootPair security → Palette security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0 (normalizedResponse security order score) :=
  RaisingBodySlots.atMost_mul _ _ order 0 0 _ _ (RaisingBodySlots.completeFamily_atMost security order _)
    (RaisingBodySlots.atMost_inverse _ _ order _ (RaisingBodySlots.completeFamily_atMost security order _))

def liftZero (security : ℕ) (score : Palette security → ℝ) : RootPair security → Palette security → ℝ := fun _ => score

def liftCompensator (security : ℕ) (score : Root security → Palette security → ℝ) : RootPair security → Palette security → ℝ :=
  fun roots => score roots.1

def liftAttachment (security : ℕ) (score : Root security → Palette security → ℝ) : RootPair security → Palette security → ℝ :=
  fun roots => score roots.2

theorem inputEnergy_zero (security : ℕ) (score : Palette security → ℝ) :
    inputEnergy security (liftZero security score) = (primaryLaw security).l2Sq score := by
  unfold inputEnergy liftZero
  rw [FiniteDist.expectation_const]

theorem inputEnergy_compensator (security : ℕ) (score : Root security → Palette security → ℝ) :
    inputEnergy security (liftCompensator security score) =
      (rootReference security).expectation (fun root => (primaryLaw security).l2Sq (score root)) := by
  unfold inputEnergy liftCompensator rootsLaw
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]

theorem inputEnergy_attachment (security : ℕ) (score : Root security → Palette security → ℝ) :
    inputEnergy security (liftAttachment security score) =
      (rootReference security).expectation (fun root => (primaryLaw security).l2Sq (score root)) := by
  unfold inputEnergy liftAttachment rootsLaw
  rw [FiniteDist.expectation_prod]
  change (rootReference security).expectation (fun _ =>
    (rootReference security).expectation (fun root => (primaryLaw security).l2Sq (score root))) = _
  rw [FiniteDist.expectation_const]

end
end CurrentAFT.RootTaggedSelected

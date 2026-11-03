import CurrentAFT.RootTaggedSelectedNorm
import CurrentAFT.RaisingPatternBudget

/-! # Actual selected root/control channels on complete joint Hilbert inputs -/
namespace CurrentAFT.RootTaggedSelectedChannel

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert
  RootTaggedSelected RootTaggedSelectedNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := RootPair security × Palette security
abbrev OneInput (security : ℕ) := Root security × Palette security

def inputLaw (security : ℕ) : FiniteDist (Input security) := (rootsLaw security).prod (primaryLaw security)
def oneInputLaw (security : ℕ) : FiniteDist (OneInput security) := (rootReference security).prod (primaryLaw security)

def responseLinear (security order : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := (completeFamilyLinear security order (massLinear security score)) * LocalRaisingBounds.positiveInverse security order
  map_add' first second := by rw [map_add, map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, map_smul, smul_mul_assoc, RingHom.id_apply]

theorem responseLinear_apply (security order : ℕ) (score : RootPair security → Palette security → ℝ) :
    responseLinear security order score = normalizedResponse security order score := rfl

def curryLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (RootPair security → Palette security → ℝ) where
  toFun score roots primary := score (roots, primary)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def controlCenterLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] (RootPair security → Palette security → ℝ) where
  toFun score roots := centerLinear (primaryLaw security) (score roots)
  map_add' first second := by
    funext roots
    exact (centerLinear (primaryLaw security)).map_add (first roots) (second roots)
  map_smul' scalar score := by
    funext roots
    exact (centerLinear (primaryLaw security)).map_smul scalar (score roots)

theorem controlCenter_energy_le (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    inputEnergy security (controlCenterLinear security score) ≤ inputEnergy security score :=
  Finset.sum_le_sum (fun roots _ => mul_le_mul_of_nonneg_left (center_energy_le _ (score roots)) ((rootsLaw security).nonneg roots))

theorem inputEnergy_curry (security : ℕ) (score : Input security → ℝ) :
    inputEnergy security (curryLinear security score) = (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  rfl

/-- Centering acts only on the selected primary control. Its two roots
remain one joint input, and are never divided by their reference atoms. -/
def channel (security order : ℕ) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (responseLinear security order).comp ((controlCenterLinear security).comp (curryLinear security))

theorem channel_on_centered (security order : ℕ) (score : Input security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (fun primary => score (roots, primary)) = 0) :
    channel security order score = normalizedResponse security order (curryLinear security score) := by
  have hequal : controlCenterLinear security (curryLinear security score) = curryLinear security score := by
    funext roots primary
    change score (roots, primary) - (primaryLaw security).expectation (fun color => score (roots, color)) = _
    rw [hcentered, sub_zero]
    rfl
  change responseLinear security order (controlCenterLinear security (curryLinear security score)) = _
  rw [hequal, responseLinear_apply]

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ)) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (channel security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hcentered (roots : RootPair security) :
      (primaryLaw security).expectation (controlCenterLinear security (curryLinear security score) roots) = 0 :=
    center_mean _ _
  have h := normalizedResponse_norm security order horder hlarge
    (controlCenterLinear security (curryLinear security score)) hcentered
  apply h.trans
  have hinput := controlCenter_energy_le security (curryLinear security score)
  rw [inputEnergy_curry] at hinput
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinput)
    (div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _))

theorem channel_vanishesBelow_one (security order : ℕ) (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order score) :=
  normalizedResponse_vanishesBelow_one security order _ (fun _ => center_mean _ _)

theorem channel_no_body (security order : ℕ) (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0 (channel security order score) :=
  normalizedResponse_no_body security order _

theorem channel_fiber_energy (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ))
    (arity : TruncatedArity order) (score : Input security → ℝ) :
    (RaisingChannels.outputReference (primaryLaw security) (bodyReference security) order arity).l2Sq
      ((RaisingChannels.fiberLinear (primaryLaw security) (bodyReference security) order arity).comp (channel security order) score) ≤
      ((selectedConstant / (Parameters.base security : ℝ) ^ 47) /
        ControlNorm.gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
          arity.val.1.val arity.val.2.val) ^ 2 * (inputLaw security).l2Sq score :=
  RaisingChannels.fiber_energy_le (primaryLaw security) (bodyReference security) order _ _
    (RaisingPatternBudget.primaryFactor_pos security) (RaisingPatternBudget.bodyFactor_pos security)
    (inputLaw security) (channel security order) _ (channel_norm security order horder hlarge) arity score

def zeroLiftLinear (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score sample.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def compensatorLiftLinear (security : ℕ) : (OneInput security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score (sample.1.1, sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def attachmentLiftLinear (security : ℕ) : (OneInput security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score (sample.1.2, sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zeroLift_energy (security : ℕ) (score : Palette security → ℝ) :
    (inputLaw security).l2Sq (zeroLiftLinear security score) = (primaryLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  change (rootsLaw security).expectation (fun _ => (primaryLaw security).expectation (fun color => score color ^ 2)) = _
  rw [FiniteDist.expectation_const]

theorem compensatorLift_energy (security : ℕ) (score : OneInput security → ℝ) :
    (inputLaw security).l2Sq (compensatorLiftLinear security score) = (oneInputLaw security).l2Sq score := by
  unfold inputLaw rootsLaw FiniteDist.l2Sq oneInputLaw
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  change (rootReference security).expectation (fun root => (rootReference security).expectation
    (fun _ => (primaryLaw security).expectation (fun color => score (root, color) ^ 2))) = _
  simp only [FiniteDist.expectation_const]
  rw [FiniteDist.expectation_prod]

theorem attachmentLift_energy (security : ℕ) (score : OneInput security → ℝ) :
    (inputLaw security).l2Sq (attachmentLiftLinear security score) = (oneInputLaw security).l2Sq score := by
  unfold inputLaw rootsLaw FiniteDist.l2Sq oneInputLaw
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  change (rootReference security).expectation (fun _ => (rootReference security).expectation
    (fun root => (primaryLaw security).expectation (fun color => score (root, color) ^ 2))) = _
  rw [FiniteDist.expectation_const, FiniteDist.expectation_prod]

/-- Zero, compensator-only, attachment-only and double-root interfaces all
inherit the same physical channel, with exact reference-energy isometries. -/
def zeroChannel (security order : ℕ) := (channel security order).comp (zeroLiftLinear security)
def compensatorChannel (security order : ℕ) := (channel security order).comp (compensatorLiftLinear security)
def attachmentChannel (security order : ℕ) := (channel security order).comp (attachmentLiftLinear security)

theorem zeroChannel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ)) (score : Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (zeroChannel security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt ((primaryLaw security).l2Sq score) := by
  have h := channel_norm security order horder hlarge (zeroLiftLinear security score)
  rwa [zeroLift_energy] at h

theorem compensatorChannel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ)) (score : OneInput security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (compensatorChannel security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt ((oneInputLaw security).l2Sq score) := by
  have h := channel_norm security order horder hlarge (compensatorLiftLinear security score)
  rwa [compensatorLift_energy] at h

theorem attachmentChannel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ)) (score : OneInput security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (attachmentChannel security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt ((oneInputLaw security).l2Sq score) := by
  have h := channel_norm security order horder hlarge (attachmentLiftLinear security score)
  rwa [attachmentLift_energy] at h

end
end CurrentAFT.RootTaggedSelectedChannel

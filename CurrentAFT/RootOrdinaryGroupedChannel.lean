import CurrentAFT.SelectedOrdinaryHybrid
import CurrentAFT.RootCoordinateProjection

/-! # Typed one-root selected ordinary channels

The untagged root is averaged and the tagged root is centered before the
local channel is applied. This gives a degree bound for every input score,
including point masses used in joint tensor assembly.
-/
namespace CurrentAFT.RootOrdinaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Input (security : ℕ) := (Fin 1 → Root security) × SafePalette security

def reference (security : ℕ) : FiniteDist (Input security) :=
  RootCoordinateProjection.reference (rootReference security) (bodyReference security)

def toRaw (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (SelectedOrdinaryRoot.Input security → ℝ) where
  toFun score sample := score ((fun _ => sample.1), sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem oneRoot_expectation (security : ℕ) (value : (Fin 1 → Root security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).expectation value =
      (rootReference security).expectation (fun root => value (fun _ => root)) := by
  unfold FiniteDist.expectation
  change (∑ roots : Fin 1 → Root security, (∏ index, (rootReference security).weight (roots index)) * value roots) = _
  rw [← (Equiv.funUnique (Fin 1) (Root security)).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, Fin.prod_univ_one]
  rfl

theorem toRaw_energy (security : ℕ) (score : Input security → ℝ) :
    (SelectedOrdinaryRoot.inputLaw security).l2Sq (toRaw security score) = (reference security).l2Sq score := by
  unfold reference RootCoordinateProjection.reference SelectedOrdinaryRoot.inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod, oneRoot_expectation]
  rfl

def projector (security : ℕ) (tagged : Bool) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  RootCoordinateProjection.coordinate (rootReference security) (0 : Fin 1) tagged

theorem projector_energy_le (security : ℕ) (tagged : Bool) (score : Input security → ℝ) :
    (reference security).l2Sq (projector security tagged score) ≤ (reference security).l2Sq score :=
  RootCoordinateProjection.coordinate_energy_le (rootReference security) (bodyReference security) 0 tagged score

theorem average_toRaw (security : ℕ) (score : Input security → ℝ) :
    toRaw security (projector security false score) =
      SelectedOrdinaryMean.constantRoot security (SelectedOrdinaryMean.rootMean security (toRaw security score)) := by
  funext sample
  change (rootReference security).expectation (fun root =>
    score (Function.update (fun _ : Fin 1 => sample.1) 0 root, sample.2)) = _
  simp only [Function.update_eq_const_of_subsingleton]
  rfl

theorem center_toRaw (security : ℕ) (score : Input security → ℝ) :
    toRaw security (projector security true score) = SelectedOrdinaryMean.rootCenter security (toRaw security score) := by
  change toRaw security (score - RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) = _
  rw [map_sub]
  rw [show toRaw security (RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) =
    SelectedOrdinaryMean.constantRoot security (SelectedOrdinaryMean.rootMean security (toRaw security score)) from average_toRaw security score]
  rfl

def channel (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) :
    (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (SelectedOrdinaryHybrid.channel security order horder).comp ((toRaw security).comp (projector security tagged))

theorem channel_false (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder false score =
      SelectedOrdinaryHybrid.independentChannel security order horder
        (SelectedOrdinaryMean.rootMean security (toRaw security score)) := by
  change SelectedOrdinaryHybrid.channel security order horder (toRaw security (projector security false score)) = _
  rw [average_toRaw, SelectedOrdinaryHybrid.channel_constant]

theorem channel_true (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder true score =
      SelectedOrdinaryRoot.channel security order horder
        (SelectedOrdinaryMean.rootCenter security (toRaw security score)) := by
  change SelectedOrdinaryHybrid.channel security order horder (toRaw security (projector security true score)) = _
  rw [center_toRaw]
  exact SelectedOrdinaryHybrid.channel_on_centered security order horder _ (SelectedOrdinaryMean.rootCenter_centered security _)

def cost (security : ℕ) (tagged : Bool) : ℝ :=
  if tagged then 48 / (Parameters.base security : ℝ)^63 else 2 * BackgroundRates.bodyFactor security

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order horder tagged score) ≤
      cost security tagged * Real.sqrt ((reference security).l2Sq score) := by
  cases tagged
  · rw [channel_false]
    apply (SelectedOrdinaryHybrid.independentChannel_norm security order horder _).trans
    have h := SelectedOrdinaryMean.rootMean_energy_le security (toRaw security score)
    rw [toRaw_energy] at h
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h)
      (mul_nonneg (by norm_num) (RaisingPatternBudget.bodyFactor_pos security).le)
  · rw [channel_true]
    apply (SelectedOrdinaryRootProperties.channel_norm security order horder _).trans
    have h := SelectedOrdinaryMean.rootCenter_energy_le security (toRaw security score)
    rw [toRaw_energy] at h
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by positivity)

theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder tagged score) :=
  SelectedOrdinaryHybrid.channel_vanishesBelow_one security order horder _

theorem channel_no_new_body (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 1 (channel security order horder tagged score) :=
  SelectedOrdinaryHybrid.channel_no_new_body security order horder _

theorem tagged_channel_no_body (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0 (channel security order horder true score) := by
  rw [channel_true]
  exact SelectedOrdinaryRootProperties.channel_no_body security order horder _

theorem channel_physical_identity (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (channel security order horder tagged score) *
      (1 + TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm (OrdinaryRaising.deviation security))) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (SelectedOrdinaryRoot.rawMass security (SelectedOrdinaryRoot.controlCenterLinear security
          (toRaw security (projector security tagged score))))) :=
  SelectedOrdinaryHybrid.channel_physical_identity security order horder _

end
end CurrentAFT.RootOrdinaryGroupedChannel

import CurrentAFT.RootTaggedSelectedCancellation
import CurrentAFT.RootSelectedZeroTag
import CurrentAFT.RootCoordinateProjection

/-! # The actual selected primary channel on two typed root coordinates

Coordinate zero is the compensator root and coordinate one is the attachment
root. Both roots act on one joint primary-control score. A false mask entry
averages its root; a true entry centers it.
-/
namespace CurrentAFT.RootPrimaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalReferenceEnergy NormalizedLocalPolynomial
  LocalRaisingBounds RootTaggedSelected RootTaggedSelectedNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := (Fin 2 → Root security) × Palette security

def inputLaw (security : ℕ) : FiniteDist (Input security) :=
  RootCoordinateProjection.reference (rootReference security) (primaryLaw security)

/-- The numbering is fixed: compensator first, attachment second. -/
def pairEquiv (security : ℕ) : (Fin 2 → Root security) ≃ RootPair security :=
  finTwoArrowEquiv (Root security)

def pairLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ]
    (RootTaggedSelectedChannel.Input security → ℝ) where
  toFun score sample := score ((pairEquiv security).symm sample.1, sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem expectation_finTwo {Color : Type*} [Fintype Color]
    (law : FiniteDist Color) (value : (Fin 2 → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Fin 2 => law)).expectation value =
      (law.prod law).expectation (fun pair => value ((finTwoArrowEquiv Color).symm pair)) := by
  unfold FiniteDist.expectation
  conv_rhs => rw [← (finTwoArrowEquiv Color).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  change (∏ index : Fin 2, law.weight (word index)) * value word =
    law.weight (word 0) * law.weight (word 1) *
      value ((finTwoArrowEquiv Color).symm ((finTwoArrowEquiv Color) word))
  rw [Fin.prod_univ_two, Equiv.symm_apply_apply]

theorem pairLinear_energy (security : ℕ) (score : Input security → ℝ) :
    (RootTaggedSelectedChannel.inputLaw security).l2Sq (pairLinear security score) =
      (inputLaw security).l2Sq score := by
  unfold RootTaggedSelectedChannel.inputLaw inputLaw RootCoordinateProjection.reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  exact (expectation_finTwo (rootReference security)
    (fun roots => (primaryLaw security).expectation (fun primary => score (roots, primary) ^ 2))).symm

def mask (tagged : Fin 2 → Bool) : List (Fin 2 × Bool) :=
  (Finset.univ : Finset (Fin 2)).toList.map (fun index => (index, tagged index))

def projector (security : ℕ) (tagged : Fin 2 → Bool) :
    (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  RootCoordinateProjection.sequence (rootReference security) (mask tagged)

private theorem sequence_perm {Color Control : Type*} [Fintype Color] [Fintype Control]
    (law : FiniteDist Color) (tagged : Fin 2 → Bool) {first second : List (Fin 2)}
    (hperm : first.Perm second)
    (score : ((Fin 2 → Color) × Control) → ℝ) :
    RootCoordinateProjection.sequence law (first.map (fun index => (index, tagged index))) score =
      RootCoordinateProjection.sequence law (second.map (fun index => (index, tagged index))) score := by
  induction hperm with
  | nil => rfl
  | cons index hperm ih =>
      simp only [List.map_cons, RootCoordinateProjection.sequence, LinearMap.comp_apply, ih]
  | swap first second rest =>
      simp only [List.map_cons, RootCoordinateProjection.sequence, LinearMap.comp_apply]
      by_cases hequal : first = second
      · subst second; rfl
      · exact RootCoordinateProjection.coordinate_commute law second first (Ne.symm hequal)
          (tagged second) (tagged first) _
  | trans first second ihfirst ihsecond => exact ihfirst.trans ihsecond

theorem projector_eq_two (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    projector security tagged score =
      RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
        (RootCoordinateProjection.coordinate (rootReference security) 1 (tagged 1) score) := by
  have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by
    ext index
    fin_cases index <;> simp
  have hperm : (Finset.univ : Finset (Fin 2)).toList.Perm [0, 1] := by
    rw [← huniv]
    exact List.toFinset_toList (by simp)
  exact sequence_perm (rootReference security) tagged hperm score

theorem projector_energy_le (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (projector security tagged score) ≤ (inputLaw security).l2Sq score :=
  RootCoordinateProjection.sequence_energy_le (rootReference security) (primaryLaw security) (mask tagged) score

def projectedScore (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    RootPair security → Palette security → ℝ :=
  RootTaggedSelectedChannel.curryLinear security (pairLinear security (projector security tagged score))

def centeredScore (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    RootPair security → Palette security → ℝ :=
  RootTaggedSelectedChannel.controlCenterLinear security (projectedScore security tagged score)

/-- This is the actual selected paired channel after the explicit two-root mask. -/
def channel (security order : ℕ) (tagged : Fin 2 → Bool) :
    (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (RootTaggedSelectedChannel.channel security order).comp
    ((pairLinear security).comp (projector security tagged))

/-- Equality of coefficient data, before any polynomial evaluation. -/
theorem channel_eq_normalizedResponse (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    channel security order tagged score =
      normalizedResponse security order (centeredScore security tagged score) := rfl

theorem centeredScore_control_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) (roots : RootPair security) :
    (primaryLaw security).expectation (centeredScore security tagged score roots) = 0 :=
  CoefficientHilbert.center_mean _ _

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order tagged score) ≤
      (selectedConstant / (Parameters.base security : ℝ)^47) *
        Real.sqrt ((inputLaw security).l2Sq score) := by
  have h := RootTaggedSelectedChannel.channel_norm security order horder hlarge
    (pairLinear security (projector security tagged score))
  rw [pairLinear_energy] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (projector_energy_le security tagged score))
    (div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)))

theorem channel_vanishesBelow_one (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (channel security order tagged score) :=
  RootTaggedSelectedChannel.channel_vanishesBelow_one security order _

theorem channel_no_body (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    RaisingBodySlots.AtMost (primaryLaw security) (bodyReference security) order 0
      (channel security order tagged score) :=
  RootTaggedSelectedChannel.channel_no_body security order _

theorem channel_physical_identity (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (channel security order tagged score) *
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (uniformReference security).weight
          (independentPositiveLaw security).weight) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (uniformReference security).weight
          (mass security (centeredScore security tagged score))) :=
  normalizedResponse_physical_identity security order _

theorem projector_attachment_average_zero (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ) :
    RootCoordinateProjection.average (rootReference security) 1
      (projector security tagged score) = 0 := by
  rw [projector_eq_two, htag]
  change RootCoordinateProjection.coordinate (rootReference security) 1 false
    (RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
      (RootCoordinateProjection.center (rootReference security) 1 score)) = 0
  rw [RootCoordinateProjection.coordinate_commute (rootReference security) 1 0
    (by intro hequal; exact Nat.one_ne_zero (congrArg Fin.val hequal))]
  change RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
    (RootCoordinateProjection.average (rootReference security) 1
      (RootCoordinateProjection.center (rootReference security) 1 score)) = 0
  rw [RootCoordinateProjection.center_mean_zero, map_zero]

private theorem update_attachment {Color : Type*} (first second value : Color) :
    Function.update (![first, second] : Fin 2 → Color) 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp

theorem projectedScore_attachment_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ)
    (compensator : Root security) (primary : Palette security) :
    (rootReference security).expectation (fun attachment =>
      projectedScore security tagged score (compensator, attachment) primary) = 0 := by
  have h := congrFun (projector_attachment_average_zero security tagged htag score)
    (![compensator, compensator], primary)
  simpa only [RootCoordinateProjection.average_apply, update_attachment, Pi.zero_apply] using h

/-- Primary-control centering commutes with the actual attachment-root mean.
The two roots still share their original one primary score. -/
theorem centeredScore_attachment_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ)
    (compensator : Root security) (primary : Palette security) :
    (rootReference security).expectation (fun attachment =>
      centeredScore security tagged score (compensator, attachment) primary) = 0 := by
  change (rootReference security).expectation (fun attachment =>
    projectedScore security tagged score (compensator, attachment) primary -
      (primaryLaw security).expectation (projectedScore security tagged score (compensator, attachment))) = 0
  rw [FiniteDist.expectation_sub, projectedScore_attachment_mean security tagged htag score,
    FiniteDist.expectation_comm]
  simp only [projectedScore_attachment_mean security tagged htag score, FiniteDist.expectation_const, sub_self]

theorem channel_vanishesBelow_two (security order : ℕ) (horder : 1 ≤ order)
    (tagged : Fin 2 → Bool) (htag : tagged 1 = true) (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (channel security order tagged score) := by
  rw [channel_eq_normalizedResponse]
  exact RootTaggedSelectedCancellation.normalizedResponse_vanishesBelow_two security order horder _
    (centeredScore_control_mean security tagged score)
    (centeredScore_attachment_mean security tagged htag score)

def rootMean (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) where
  toFun score primary := (FiniteDist.independent (fun _ : Fin 2 => rootReference security)).expectation
    (fun roots => score (roots, primary))
  map_add' first second := by funext primary; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext primary; exact FiniteDist.expectation_const_mul _ _ _

private theorem update_both {Color : Type*} (word : Fin 2 → Color) (first second : Color) :
    Function.update (Function.update word 0 first) 1 second = ![first, second] := by
  funext index
  fin_cases index <;> simp

theorem projector_zero (security : ℕ) (score : Input security → ℝ) :
    projector security (fun _ => false) score = fun sample => rootMean security score sample.2 := by
  funext sample
  rw [projector_eq_two]
  simp only [RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false,
    RootCoordinateProjection.average_apply, update_both]
  change _ = (FiniteDist.independent (fun _ : Fin 2 => rootReference security)).expectation
    (fun roots => score (roots, sample.2))
  rw [expectation_finTwo, FiniteDist.expectation_prod]
  rfl

theorem rootMean_energy_le (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).l2Sq (rootMean security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw RootCoordinateProjection.reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro primary _
  exact mul_le_mul_of_nonneg_left
    (BlockFock.mean_square_le (FiniteDist.independent (fun _ : Fin 2 => rootReference security))
      (fun roots => score (roots, primary))) ((primaryLaw security).nonneg primary)

theorem channel_zero (security order : ℕ) (score : Input security → ℝ) :
    channel security order (fun _ => false) score =
      RootTaggedSelectedChannel.zeroChannel security order (rootMean security score) := by
  change RootTaggedSelectedChannel.channel security order
    (pairLinear security (projector security (fun _ => false) score)) =
      RootTaggedSelectedChannel.channel security order
        (RootTaggedSelectedChannel.zeroLiftLinear security (rootMean security score))
  congr 1
  rw [projector_zero]
  rfl

theorem channel_zero_norm_sharp (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (score : Input security → ℝ) :
    coefficientNorm security order (channel security order (fun _ => false) score) ≤
      (2 * BackgroundRates.primaryFactor security) * Real.sqrt ((inputLaw security).l2Sq score) := by
  rw [channel_zero]
  exact (RootSelectedZeroTag.zeroChannel_norm_sharp security order horder hlarge hsmall _).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (rootMean_energy_le security score))
      (mul_nonneg (by norm_num) (RaisingPatternBudget.primaryFactor_pos security).le))

/-- On a slice already obeying the root mask and primary centering, the
typed channel is exactly the original normalized response on that slice. -/
theorem channel_on_fixed (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) (hfixed : projector security tagged score = score)
    (hcontrol : ∀ roots, (primaryLaw security).expectation
      (fun primary => pairLinear security score (roots, primary)) = 0) :
    channel security order tagged score = normalizedResponse security order
      (RootTaggedSelectedChannel.curryLinear security (pairLinear security score)) := by
  change RootTaggedSelectedChannel.channel security order
    (pairLinear security (projector security tagged score)) = _
  rw [hfixed]
  exact RootTaggedSelectedChannel.channel_on_centered security order _ hcontrol

/-- Only a tagged attachment forces an additional output degree. -/
def minimumDegree (tagged : Fin 2 → Bool) : ℕ := if tagged 1 then 2 else 1

theorem channel_vanishesBelow (security order : ℕ) (horder : 1 ≤ order)
    (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order
      (minimumDegree tagged) (channel security order tagged score) := by
  cases htag : tagged 1
  · simpa only [minimumDegree, htag, Bool.false_eq_true, if_false] using
      channel_vanishesBelow_one security order tagged score
  · simpa only [minimumDegree, htag, if_true] using
      channel_vanishesBelow_two security order horder tagged htag score

/-- The root-free selected channel retains its sharp independent-response
cost. Every tagged channel uses the full joint root/control estimate. -/
def cost (security : ℕ) (tagged : Fin 2 → Bool) : ℝ :=
  if tagged 0 || tagged 1 then selectedConstant / (Parameters.base security : ℝ)^47
  else 2 * BackgroundRates.primaryFactor security

theorem cost_nonneg (security : ℕ) (tagged : Fin 2 → Bool) : 0 ≤ cost security tagged := by
  unfold cost
  split
  · exact div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  · exact mul_nonneg (by norm_num) (RaisingPatternBudget.primaryFactor_pos security).le

theorem channel_norm_cost (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order tagged score) ≤
      cost security tagged * Real.sqrt ((inputLaw security).l2Sq score) := by
  by_cases hzero : tagged = fun _ => false
  · subst tagged
    simpa only [cost, Bool.or_self, Bool.false_eq_true, if_false] using
      channel_zero_norm_sharp security order horder hlarge hsmall score
  · have hsome : (tagged 0 || tagged 1) = true := by
      cases hfirst : tagged 0 <;> cases hsecond : tagged 1
      · exfalso
        apply hzero
        funext index
        fin_cases index <;> assumption
      · rfl
      · rfl
      · rfl
    simpa only [cost, hsome, if_true] using channel_norm security order horder hlarge tagged score

end
end CurrentAFT.RootPrimaryGroupedChannel

import CurrentAFT.RootSelectedPhysicalColumns
import CurrentAFT.RootSelectedControlCenter

/-! # Explicit projected linear columns of the true local physical numerator

Both selected roles have the form physicalLinear ∘ controlCenter ∘ rootMask.
The control projector is exactly the one proved to fix the original full
joint coefficient source. No factorization of that source is required.
-/
namespace CurrentAFT.RootSelectedPhysicalLinear
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalCoefficientFamily RootTaggedSelected RootSelectedPhysicalColumns RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryNumeratorLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun := primaryNumerator security
  map_add' first second := by
    simp only [← primaryNumerator_eq]
    exact congrArg (AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight)
      ((massLinear security).map_add first second) |>.trans
        ((AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight).map_add _ _)
  map_smul' scalar score := by
    simp only [← primaryNumerator_eq]
    exact congrArg (AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight)
      ((massLinear security).map_smul scalar score) |>.trans
        ((AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight).map_smul scalar _)

def ordinaryNumeratorLinear (security : ℕ) :
    (SelectedOrdinaryRoot.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun := ordinaryNumerator security
  map_add' first second := by
    simp only [ordinaryNumerator, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' scalar score := by
    simp only [ordinaryNumerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro root _
    apply Finset.sum_congr rfl
    intro center _
    congr 1
    ring

def primaryRaw (security : ℕ) :
    (RootPrimaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (primaryNumeratorLinear security).comp
    ((RootTaggedSelectedChannel.curryLinear security).comp (RootPrimaryGroupedChannel.pairLinear security))

def ordinaryRaw (security : ℕ) :
    (RootOrdinaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (ordinaryNumeratorLinear security).comp (RootOrdinaryGroupedChannel.toRaw security)

def primaryProjected (security : ℕ) (tagged : Fin 2 → Bool) :
    (RootPrimaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (primaryRaw security).comp ((RootSelectedControlCenter.centerControl (primaryLaw security)).comp
    (RootPrimaryGroupedChannel.projector security tagged))

def ordinaryProjected (security : ℕ) (tagged : Bool) :
    (RootOrdinaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (ordinaryRaw security).comp ((RootSelectedControlCenter.centerControl (bodyReference security)).comp
    (RootOrdinaryGroupedChannel.projector security tagged))

theorem primaryProjected_apply (security : ℕ) (tagged : Fin 2 → Bool) (score : RootPrimaryGroupedChannel.Input security → ℝ) :
    primaryProjected security tagged score = primaryNumerator security (RootPrimaryGroupedChannel.centeredScore security tagged score) := rfl

theorem ordinaryProjected_apply (security : ℕ) (tagged : Bool) (score : RootOrdinaryGroupedChannel.Input security → ℝ) :
    ordinaryProjected security tagged score = ordinaryNumerator security (SelectedOrdinaryRoot.controlCenterLinear security
      (RootOrdinaryGroupedChannel.toRaw security (RootOrdinaryGroupedChannel.projector security tagged score))) := rfl

theorem primary_physical (security order : ℕ) (tagged : Fin 2 → Bool) (score : RootPrimaryGroupedChannel.Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootPrimaryGroupedChannel.channel security order tagged score) *
      TruncatedOutput.quotientMap order (primaryPolynomial security) =
      TruncatedOutput.quotientMap order (primaryProjected security tagged score) :=
  primary_channel_physical security order tagged score

theorem ordinary_physical (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : RootOrdinaryGroupedChannel.Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootOrdinaryGroupedChannel.channel security order horder tagged score) *
      TruncatedOutput.quotientMap order (ordinaryPolynomial security) =
      TruncatedOutput.quotientMap order (ordinaryProjected security tagged score) :=
  ordinary_channel_physical security order horder tagged score

theorem primary_column (security : ℕ) (tagged : Fin 2 → Bool) (sample : RootPrimaryGroupedChannel.Input security) :
    primaryProjected security tagged (Pi.single sample 1) = primaryColumn security tagged sample := rfl

theorem ordinary_column (security : ℕ) (tagged : Bool) (sample : RootOrdinaryGroupedChannel.Input security) :
    ordinaryProjected security tagged (Pi.single sample 1) = ordinaryColumn security tagged sample := rfl

end
end CurrentAFT.RootSelectedPhysicalLinear

import CurrentAFT.RootLocalDenominators
import CurrentAFT.RootPrimaryGroupedChannel
import CurrentAFT.PairedRootCentering

/-! # Literal physical columns of the selected normalized channels

Every numerator below is a finite weighted generating function of the
actual local law. The selected primary score is used once in the paired
channel, and its compensator and attachment retain the same leg scalar.
-/
namespace CurrentAFT.RootSelectedPhysicalColumns
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootBackgroundPolynomial BackgroundPolynomialEvaluation
  CycleRootExpansion LocalCoefficientFamily RootLocalDenominators
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryNumerator (security : ℕ) (score : RootPair security → Palette security → ℝ) : MvPolynomial (Palette security) ℝ :=
  ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
    ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security (score sample.1) group) •
      blockGenerating security (fixedControlLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 group)

theorem pairedMass_generating (security : ℕ) (comp attach : ℤ) (scalar : FirstHistogram.Scalar security)
    (score : Palette security → ℝ) :
    centeredGeneratingLinear (uniformReference security).weight (pairedMassAt security comp attach scalar score) =
      ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security score group) •
        blockGenerating security (fixedControlLaw security comp attach scalar group) := by
  have hmass : pairedMassAt security comp attach scalar score =
      ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security score group) •
        (fixedControlLaw security comp attach scalar group).weight := by
    rw [← pairedMassLinear_apply]
    funext word
    simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      fixedControlLaw_weight]
  rw [hmass, map_sum]
  simp only [map_smul, generating_eq_block]

theorem primaryNumerator_eq (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    centeredGeneratingLinear (uniformReference security).weight (mass security score) = primaryNumerator security score := by
  have hmass : mass security score =
      ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
        pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 (score sample.1) := by
    funext word
    simp only [mass_eq_joint, jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, pairedMass_generating]
  rfl

def primaryColumn (security : ℕ) (tagged : Fin 2 → Bool) (sample : RootPrimaryGroupedChannel.Input security) :
    MvPolynomial (Palette security) ℝ :=
  primaryNumerator security (RootPrimaryGroupedChannel.centeredScore security tagged (Pi.single sample 1))

theorem primary_channel_physical (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : RootPrimaryGroupedChannel.Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootPrimaryGroupedChannel.channel security order tagged score) *
      TruncatedOutput.quotientMap order (primaryPolynomial security) =
      TruncatedOutput.quotientMap order (primaryNumerator security (RootPrimaryGroupedChannel.centeredScore security tagged score)) := by
  rw [← independentPositive_generating]
  rw [RootPrimaryGroupedChannel.channel_physical_identity, primaryNumerator_eq]

theorem primary_column_physical (security order : ℕ) (tagged : Fin 2 → Bool)
    (sample : RootPrimaryGroupedChannel.Input security) :
    BackgroundEvaluation.evaluation security order (RootPrimaryGroupedChannel.channel security order tagged (Pi.single sample 1)) *
      TruncatedOutput.quotientMap order (primaryPolynomial security) = TruncatedOutput.quotientMap order (primaryColumn security tagged sample) :=
  primary_channel_physical security order tagged _

def ordinaryNumerator (security : ℕ) (score : SelectedOrdinaryRoot.Input security → ℝ) : MvPolynomial (Palette security) ℝ :=
  ∑ root : Root security, (rootReference security).weight root •
    ∑ center : SafePalette security, ((bodyReference security).weight center * score (root, center)) •
      centeredFactor (uniformReference security).weight (SelectedOrdinaryRoot.rootEmbedding security root center)

theorem push_generating {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : FiniteDist Source) (embedding : Source → Output) (reference : Output → ℝ) (score : Source → ℝ) :
    singleGenerating reference (SelectedOrdinaryRoot.pushLinear law embedding score) =
      ∑ source, (law.weight source * score source) • centeredFactor reference (embedding source) := by
  unfold singleGenerating SelectedOrdinaryRoot.pushLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    MvPolynomial.smul_eq_C_mul]

theorem ordinaryNumerator_eq (security : ℕ) (score : SelectedOrdinaryRoot.Input security → ℝ)
    (hmass : ∑ color, SelectedOrdinaryRoot.rawMass security score color = 0) :
    profileForm (SelectedOrdinaryRoot.rawMass security score) = ordinaryNumerator security score := by
  rw [← singleGenerating_mass_zero (uniformReference security).weight _ hmass]
  have hmassEq : SelectedOrdinaryRoot.rawMass security score =
      ∑ root : Root security, (rootReference security).weight root •
        SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root) (fun center => score (root, center)) := by
    funext color
    simp only [SelectedOrdinaryRoot.rawMass_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmassEq]
  unfold singleGenerating
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  change MvPolynomial.C ((rootReference security).weight root) *
    singleGenerating (uniformReference security).weight
      (SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root) (fun center => score (root, center))) = _
  rw [push_generating, MvPolynomial.smul_eq_C_mul]

def ordinaryColumn (security : ℕ) (tagged : Bool) (sample : RootOrdinaryGroupedChannel.Input security) : MvPolynomial (Palette security) ℝ :=
  ordinaryNumerator security (SelectedOrdinaryRoot.controlCenterLinear security
    (RootOrdinaryGroupedChannel.toRaw security (RootOrdinaryGroupedChannel.projector security tagged (Pi.single sample 1))))

theorem ordinary_channel_physical (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool)
    (score : RootOrdinaryGroupedChannel.Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootOrdinaryGroupedChannel.channel security order horder tagged score) *
      TruncatedOutput.quotientMap order (ordinaryPolynomial security) =
      TruncatedOutput.quotientMap order (ordinaryNumerator security (SelectedOrdinaryRoot.controlCenterLinear security
        (RootOrdinaryGroupedChannel.toRaw security (RootOrdinaryGroupedChannel.projector security tagged score)))) := by
  rw [ordinaryPolynomial_eq, map_add, map_one, RootOrdinaryGroupedChannel.channel_physical_identity,
    ordinaryNumerator_eq security _ (SelectedOrdinaryRoot.centeredMass_zero security _)]

theorem ordinary_column_physical (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool)
    (sample : RootOrdinaryGroupedChannel.Input security) :
    BackgroundEvaluation.evaluation security order (RootOrdinaryGroupedChannel.channel security order horder tagged (Pi.single sample 1)) *
      TruncatedOutput.quotientMap order (ordinaryPolynomial security) = TruncatedOutput.quotientMap order (ordinaryColumn security tagged sample) :=
  ordinary_channel_physical security order horder tagged _

end
end CurrentAFT.RootSelectedPhysicalColumns

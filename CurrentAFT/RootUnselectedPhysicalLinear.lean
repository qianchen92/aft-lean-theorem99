import CurrentAFT.TypedRolePolynomial
import CurrentAFT.RootUnselectedGrouped

/-! # Complete unselected physical numerators as root-centered linear maps -/
namespace CurrentAFT.RootUnselectedPhysicalLinear
open AFT AFT.RepresentedPolynomial ActualBlockFock CycleRootExpansion DiffuseProfiles
  ProposalPrimary ActualControls LocalReferenceEnergy RootTaggedLocal UniformBodyProfiles
  RootUnselectedGrouped RootUnselectedBlockChannel RootIndependentBackground
  RootLocalDenominators BodyRootAverages
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw rootReference

abbrev Palette (security : ℕ) := ActualControls.Palette security

def positiveAt (security : ℕ) (queue : ℤ) : BlockIndex security → Root security → MvPolynomial (Palette security) ℝ
  | .inl _, root => RootBackgroundPolynomial.blockGenerating security (primaryLawAt security root.val)
  | .inr (.inl _), root => singleGenerating (uniformReference security).weight (shiftedLaw security .free 0 root).weight
  | .inr (.inr _), root => singleGenerating (uniformReference security).weight (shiftedLaw security .queue queue root).weight

theorem positiveAt_eq_actual (security : ℕ) (queue : ℤ) (block : BlockIndex security) (root : Root security) :
    positiveAt security queue block root = RootBackgroundPolynomial.blockGenerating security
      (TypedTaggedPhysical.blockLaw security queue (fun _ => root.val) block) := by
  rcases block with leg | (center | point)
  · rfl
  · change singleGenerating (uniformReference security).weight (shiftedLaw security .free 0 root).weight =
      RootBackgroundPolynomial.blockGenerating security
        (singletonLaw ((centerLaw security).map (shiftEquiv security root.val)))
    rw [RootIndependentBackground.singleton_blockGenerating, ← uniformReference_eq]
    rfl
  · change singleGenerating (uniformReference security).weight (shiftedLaw security .queue queue root).weight =
      RootBackgroundPolynomial.blockGenerating security
        (singletonLaw ((safeLaw security).map (shiftEquiv security (root.val + queue))))
    rw [RootIndependentBackground.singleton_blockGenerating, ← uniformReference_eq]
    congr 1
    unfold shiftedLaw preRootLaw
    rw [shiftLaw_add, add_comm queue]

def rawRoot (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (Root security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun input := ∑ root, ((rootReference security).weight root * input root) • positiveAt security queue block root
  map_add' first second := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro root _
    congr 1
    ring

private theorem covariance_center {Color : Type*} [Fintype Color]
    (law : FiniteDist Color) (input value : Color → ℝ) :
    (∑ point, law.weight point * TensorChannel.center law input point * value point) =
      ∑ point, law.weight point * input point * (value point - law.expectation value) := by
  calc
    _ = law.expectation (fun point => input point * value point) - law.expectation input * law.expectation value := by
      simp only [TensorChannel.center_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · unfold FiniteDist.expectation
        apply Finset.sum_congr rfl
        intro point _
        ring
      · unfold FiniteDist.expectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro point _
        ring
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [FiniteDist.expectation, mul_assoc]

private def singletonMass (security : ℕ) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) (color : Palette security) : ℝ :=
  ∑ root, (rootReference security).weight root * input root * (shiftedLaw security role queue root).weight color

private theorem singletonMass_center (security : ℕ) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    singletonMass security role queue (TensorChannel.center (rootReference security) input) =
      rootMass security role queue input := by
  funext color
  have hh := covariance_center (rootReference security) input
    (fun root => (shiftedLaw security role queue root).weight color)
  simpa only [singletonMass, rootMass, LinearMap.coe_mk, AddHom.coe_mk,
    deviationProfile, Pi.sub_apply, meanLaw, FiniteDist.mix_weight, FiniteDist.expectation] using hh

private theorem singletonMass_sum (security : ℕ) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    (∑ color, singletonMass security role queue input color) = (rootReference security).expectation input := by
  unfold singletonMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  rfl

private theorem singletonMass_generating (security : ℕ) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    singleGenerating (uniformReference security).weight (singletonMass security role queue input) =
      ∑ root, ((rootReference security).weight root * input root) •
        singleGenerating (uniformReference security).weight (shiftedLaw security role queue root).weight := by
  unfold singleGenerating singletonMass
  simp only [map_sum, map_mul, Finset.sum_mul, MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro color _
  ring

private theorem singleton_numerator (security : ℕ) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    profileForm (rootMass security role queue input) =
      ∑ root, ((rootReference security).weight root * TensorChannel.center (rootReference security) input root) •
        singleGenerating (uniformReference security).weight (shiftedLaw security role queue root).weight := by
  rw [← singletonMass_center]
  rw [← singleGenerating_mass_zero (uniformReference security).weight _
    ((singletonMass_sum security role queue _).trans (TensorChannel.center_mean _ _)), singletonMass_generating]

/-- Every unselected numerator is its complete actual local PGF averaged
against the root-centered input. This includes the full same-scalar triple. -/
theorem numerator_eq_raw_center (security : ℕ) (queue : ℤ) (block : BlockIndex security)
    (input : Root security → ℝ) :
    numeratorPolynomial security queue input block =
      rawRoot security queue block (TensorChannel.center (rootReference security) input) := by
  rcases block with leg | (center | point)
  · change centeredGeneratingLinear (uniformReference security).weight
      (RootTaggedLegHigher.rawMassLinear security (TensorChannel.center (rootReference security) input)) = _
    have hmass : RootTaggedLegHigher.rawMassLinear security (TensorChannel.center (rootReference security) input) =
        ∑ root, ((rootReference security).weight root * TensorChannel.center (rootReference security) input root) •
          (primaryLawAt security root.val).weight := by
      funext word
      simp only [RootTaggedLegHigher.rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hmass, map_sum]
    simp only [map_smul, RootLocalDenominators.generating_eq_block, rawRoot, positiveAt,
      LinearMap.coe_mk, AddHom.coe_mk]
  · exact singleton_numerator security .free 0 input
  · exact singleton_numerator security .queue queue input

def raw (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (RootUnselectedGrouped.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (rawRoot security queue block).comp (extractLinear security)

def projected (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (RootUnselectedGrouped.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (raw security queue block).comp (RootCoordinateProjection.center (rootReference security) (0 : Fin 1))

theorem extract_center (security : ℕ) (score : RootUnselectedGrouped.Input security → ℝ) :
    extractLinear security (RootCoordinateProjection.center (rootReference security) (0 : Fin 1) score) =
      TensorChannel.center (rootReference security) (extractLinear security score) := by
  funext root
  change score ((inputEquiv security).symm root) - (rootReference security).expectation
    (fun value => score (Function.update ((inputEquiv security).symm root).1 0 value,
      ((inputEquiv security).symm root).2)) = _
  congr 1
  apply congrArg (rootReference security).expectation
  funext value
  congr 1
  apply Prod.ext
  · funext index
    rw [Fin.eq_zero index]
    simp only [Function.update_self]
    rfl
  · rfl

theorem projected_apply (security : ℕ) (queue : ℤ) (block : BlockIndex security)
    (score : RootUnselectedGrouped.Input security → ℝ) :
    projected security queue block score = numeratorPolynomial security queue (extractLinear security score) block := by
  change rawRoot security queue block (extractLinear security (RootCoordinateProjection.center (rootReference security) 0 score)) = _
  rw [extract_center, numerator_eq_raw_center]

theorem channel_physical (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : RootUnselectedGrouped.Input security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootUnselectedGrouped.channel security order horder queue block score) *
      TruncatedOutput.quotientMap order (positivePolynomial security queue block) =
        TruncatedOutput.quotientMap order (projected security queue block score) := by
  rw [projected_apply]
  exact RootUnselectedGrouped.channel_physical security order horder queue block score

end
end CurrentAFT.RootUnselectedPhysicalLinear

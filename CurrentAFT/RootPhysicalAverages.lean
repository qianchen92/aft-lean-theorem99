import CurrentAFT.RootSelectedPhysicalLinear
import CurrentAFT.RootPolynomialTensor
import CurrentAFT.TypedRolePolynomial

/-! # The actual selected physical numerators are genuine root averages -/
namespace CurrentAFT.RootPhysicalAverages
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootSelectedPhysicalLinear RootSelectedPhysicalColumns
  CycleRootExpansion TaggedPhysicalFock OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (ActualControls.SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryAt (security : ℕ) (roots : Fin 2 → Root security) :
    (Palette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (centeredGeneratingLinear (uniformReference security).weight).comp
    (averagedPairedChannel security ((roots 0).val : ℤ) ((roots 1).val : ℤ))

def ordinaryAt (security : ℕ) (roots : Fin 1 → Root security) :
    (ActualControls.SafePalette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (centeredGeneratingLinear (uniformReference security).weight).comp
    (bodyChannel security ((roots 0).val : ℤ))

theorem primaryRaw_eq_average (security : ℕ) :
    primaryRaw security = RootPolynomialTensor.averagedChannel
      (Index := Unit) (fun _ => FiniteDist.independent (fun _ : Fin 2 => rootReference security))
      (fun _ => primaryAt security) () := by
  apply LinearMap.ext
  intro score
  change primaryNumerator security
    (RootTaggedSelectedChannel.curryLinear security (RootPrimaryGroupedChannel.pairLinear security score)) = _
  rw [← primaryNumerator_eq]
  have hmass : mass security (RootTaggedSelectedChannel.curryLinear security (RootPrimaryGroupedChannel.pairLinear security score)) =
      ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
        pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2
          (fun color => score ((RootPrimaryGroupedChannel.pairEquiv security).symm sample.1, color)) := by
    funext word
    simp only [mass_eq_joint, jointPairedMass, RootTaggedSelectedChannel.curryLinear,
      RootPrimaryGroupedChannel.pairLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    primaryAt, averagedPairedChannel_apply, map_sum, map_smul]
  conv_rhs => rw [← (RootPrimaryGroupedChannel.pairEquiv security).symm.sum_comp]
  simp only [sourceLaw, rootsLaw, Fintype.sum_prod_type, FiniteDist.prod_weight, FiniteDist.independent,
    Fin.prod_univ_two, RootPrimaryGroupedChannel.pairEquiv, finTwoArrowEquiv,
    Equiv.coe_fn_symm_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.smul_sum, smul_smul]

theorem oneGenerating {Color : Type*} [Fintype Color] (reference profile : Color → ℝ) :
    centeredGeneratingLinear reference (fun word : Fin 1 → Color => profile (word 0)) = singleGenerating reference profile := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, MvPolynomial.smul_eq_C_mul, singleGenerating]

theorem safeMass_eq_profile (security : ℕ) (score : ActualControls.SafePalette security → ℝ) :
    BodyChannelEvaluation.safeMass security score = OrdinaryPhysicalFock.profile security score := by
  have h := BodyChannelEvaluation.safeMass_full security (extendDensity security score)
  simpa only [extendDensity_safe, OrdinaryPhysicalFock.profile] using h

theorem ordinaryAt_eq (security : ℕ) (roots : Fin 1 → Root security) (score : ActualControls.SafePalette security → ℝ) :
    ordinaryAt security roots score = singleGenerating (uniformReference security).weight
      (SelectedOrdinaryRoot.pushLinear (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security (roots 0)) score) := by
  change centeredGeneratingLinear (uniformReference security).weight
    (fun word : Fin 1 → Palette security => translatedProfile security ((roots 0).val : ℤ) score (word 0)) = _
  rw [oneGenerating]
  congr 1
  funext color
  rw [SelectedOrdinaryMean.push_root, safeMass_eq_profile]
  rfl

theorem ordinaryRaw_eq_average (security : ℕ) :
    ordinaryRaw security = RootPolynomialTensor.averagedChannel
      (Index := Unit) (fun _ => FiniteDist.independent (fun _ : Fin 1 => rootReference security))
      (fun _ => ordinaryAt security) () := by
  apply LinearMap.ext
  intro score
  change ordinaryNumerator security (RootOrdinaryGroupedChannel.toRaw security score) = _
  simp only [RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [ordinaryAt_eq, push_generating]
  rw [← (Equiv.funUnique (Fin 1) (Root security)).symm.sum_comp]
  simp only [FiniteDist.independent, Fin.prod_univ_one, Equiv.funUnique_symm_apply, uniqueElim_const]
  rfl

end
end CurrentAFT.RootPhysicalAverages

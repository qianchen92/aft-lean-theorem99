import CurrentAFT.RootTaggedSelectedChannel

/-! # A tagged attachment forces a second selected-group output -/
namespace CurrentAFT.RootTaggedSelectedCancellation

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  LocalCoefficientFamily LocalRaisingFirst NormalizedLocalPolynomial LocalReferenceEnergy
  PairedReferenceEnergy FixedPairedFirst CompleteFirstCoefficient RootTaggedSelected
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem fixed_first_attachment_irrelevant (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1 =
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot 0 scalar score) 1 := by
  have hmass (root : ℤ) : (∑ word, pairedMassAt security compensatorRoot root scalar score word) = 0 := by
    rw [fixedMass_sum, hcentered, mul_zero]
  funext word
  have hword : word = (fun _ => word 0) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword, LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
      (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
      _ (hmass attachmentRoot),
    LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
      (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
      _ (hmass 0)]
  rw [fixedMass_first_formula security compensatorRoot attachmentRoot scalar score hcentered,
    fixedMass_first_formula security compensatorRoot 0 scalar score hcentered]

theorem mass_first_tensor_zero_of_attachment_centered (security : ℕ)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security) (mass security score) 1 = 0 := by
  have hmass : mass security score = ∑ sample : Sample security, (sourceLaw security).weight sample •
      pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 (score sample.1) := by
    rw [mass_eq_joint]
    funext word
    simp only [jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
  simp only [map_smul, LocalTensors.degreeTensorLinear_apply]
  simp_rw [fixed_first_attachment_irrelevant security _ _ _ _ (hcontrol _)]
  simp only [sourceLaw, rootsLaw, FiniteDist.prod_weight, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro comp _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scalar _
  let channel := localDegreeLinear security (comp.val : ℤ) 0 scalar 1
  have hscore : (∑ attach : Root security, (rootReference security).weight attach • score (comp, attach)) = 0 := by
    funext primary
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, FiniteDist.expectation] using hattachment comp primary
  have hsum : (∑ attach : Root security, (rootReference security).weight attach • channel (score (comp, attach))) = 0 := by
    have h := congrArg channel hscore
    simpa only [map_sum, map_smul, map_zero] using h
  have hchannel (input : Palette security → ℝ) : LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security (comp.val : ℤ) 0 scalar input) 1 = channel input := by
    simp only [channel, localDegreeLinear, LinearMap.comp_apply, LocalTensors.degreeTensorLinear_apply,
      pairedMassLinear_apply]
  simp_rw [hchannel]
  calc
    _ = ((rootReference security).weight comp * (scalarLaw security).weight scalar) •
        ∑ attach : Root security, (rootReference security).weight attach • channel (score (comp, attach)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro attach _
      rw [smul_smul]
      congr 1
      ring
    _ = 0 := by rw [hsum, smul_zero]

theorem mass_count_zero_of_attachment_centered (security : ℕ)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    LocalTensors.signedColorCount (mass security score) = 0 := by
  funext color
  have h := congrFun (mass_first_tensor_zero_of_attachment_centered security score hcontrol hattachment) (fun _ => color)
  rw [LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
    (fun output => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    _ (mass_zero security score hcontrol)] at h
  change LocalTensors.signedColorCount (mass security score) color / Real.sqrt ((uniformReference security).weight color) = 0 at h
  have hsqrt : Real.sqrt ((uniformReference security).weight color) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    rw [uniformReference_weight]
    exact one_div_pos.mpr (FirstResponse.modulus_pos security)
  field_simp [hsqrt] at h
  simpa only [Pi.zero_apply, mul_zero] using h

theorem firstFamily_zero_of_attachment_centered (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    CompleteFirstCoefficient.firstFamily security order horder (mass security score) = 0 := by
  have hcount := mass_count_zero_of_attachment_centered security score hcontrol hattachment
  have hscore : CompleteFirstCoefficient.firstScore security order horder (mass security score) = 0 := by
    rw [CompleteFirstCoefficient.firstScore, completeFamily_primary_centered security order horder _
      (mass_zero security score hcontrol), hcount]
    simp only [Pi.zero_apply, zero_div]
    change PrimaryTensorInverse.densityInverse security (0 : Palette security → ℝ) = 0
    exact map_zero _
  unfold CompleteFirstCoefficient.firstFamily BackgroundFamilies.primaryFamily
  have hkernel : BackgroundFamilies.primaryKernel (primaryLaw security) (bodyReference security)
      (CompleteFirstCoefficient.firstScore security order horder (mass security score))
      (firstScore_centered security order horder (mass security score)) = 0 := by
    apply Subtype.ext
    funext colors centers
    change CompleteFirstCoefficient.firstScore security order horder (mass security score) (colors 0) = 0
    rw [hscore]
    rfl
  rw [hkernel, Pi.single_zero]

/-- In particular a group with both of its roots tagged has no scalar or
first-degree response. It still consumes its one original control score. -/
theorem normalizedResponse_vanishesBelow_two (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (normalizedResponse security order score) := by
  unfold normalizedResponse NormalizedLocalPolynomial.normalizedFamily
  rw [complete_eq_first_add_higher security order horder _ (mass_zero security score hcontrol),
    firstFamily_zero_of_attachment_centered security order horder score hcontrol hattachment, zero_add]
  exact vanishesBelow_mul _ _ order 2 0 _ _ (higherFamily_vanishesBelow security order _) (vanishesBelow_zero _ _ order _)

end
end CurrentAFT.RootTaggedSelectedCancellation

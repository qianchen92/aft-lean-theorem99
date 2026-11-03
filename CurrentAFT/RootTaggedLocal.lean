import CurrentAFT.RootIndependentBackground
import CurrentAFT.PrimaryMassFamilies

/-!
# Actual unselected singleton root-tag channels

The root coordinate is centered before the actual primary mass inverse is
applied. The source law may have zero atoms; no root atom is ever divided by.
-/

namespace CurrentAFT.RootTaggedLocal

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootBackgroundPolynomial PrimaryTensorInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

def shiftedLaw (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    FiniteDist (ActualControls.Palette security) :=
  (preRootLaw security role queue).map (shiftEquiv security root.val)

def meanLaw (security : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (ActualControls.Palette security) :=
  (rootReference security).mix (shiftedLaw security role queue)

def deviationProfile (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ActualControls.Palette security → ℝ :=
  (shiftedLaw security role queue root).weight - (meanLaw security role queue).weight

theorem deviationProfile_mass (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    (∑ color, deviationProfile security role queue root color) = 0 := by
  simp only [deviationProfile, Pi.sub_apply, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]

theorem deviationProfile_root_mean (security : ℕ) (role : BodyRole) (queue : ℤ) (color : ActualControls.Palette security) :
    (rootReference security).expectation (fun root => deviationProfile security role queue root color) = 0 := by
  simp only [FiniteDist.expectation, deviationProfile, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, FiniteDist.sum_one, one_mul, meanLaw, FiniteDist.mix_weight, sub_self]

theorem shiftedLaw_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ‖uniformVector security (shiftedLaw security role queue root).weight‖ ≤ deviation security := by
  rw [shiftedLaw, uniformVector_map_equiv_norm]
  exact preRootLaw_norm_le security role queue

theorem meanLaw_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) :
    ‖uniformVector security (meanLaw security role queue).weight‖ ≤ deviation security :=
  uniformVector_mix_norm_le security _ _ _ (shiftedLaw_uniform_norm security role queue)

theorem deviationProfile_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (deviationProfile security role queue root)‖ ≤
      2 * deviation security := by
  have hsplit : ProfileHilbert.whiten (uniformReference security).weight (deviationProfile security role queue root) =
      uniformVector security (shiftedLaw security role queue root).weight - uniformVector security (meanLaw security role queue).weight := by
    unfold uniformVector
    rw [← map_sub]
    congr 1
    funext color
    simp only [deviationProfile, Pi.sub_apply]
    ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans ((add_le_add (shiftedLaw_uniform_norm security role queue root)
    (meanLaw_uniform_norm security role queue)).trans_eq (by ring))

theorem uniform_to_primary_energy (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight profile ≤
      2 * profileSquareNorm (uniformReference security).weight profile := by
  have hq := FirstResponse.modulus_pos security
  have hprimary (color : ActualControls.Palette security) :
      1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security color
  unfold profileSquareNorm
  calc
    _ ≤ ∑ color, profile color ^ 2 / (1 / (2 * (Parameters.modulus security : ℝ))) := by
      apply Finset.sum_le_sum
      intro color _
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hprimary color)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      rw [uniformReference_weight]
      field_simp

theorem deviationProfile_primary_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    profileSquareNorm (primaryLaw security).weight (deviationProfile security role queue root) ≤
      8 * deviation security ^ 2 := by
  have hn := deviationProfile_uniform_norm security role queue root
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg] at hn2
  exact (uniform_to_primary_energy security _).trans
    ((mul_le_mul_of_nonneg_left hn2 (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

def rootMass (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) where
  toFun input := fun color => ∑ root, (rootReference security).weight root * input root * deviationProfile security role queue root color
  map_add' first second := by
    funext color
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

theorem rootMass_mass (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (∑ color, rootMass security role queue input color) = 0 := by
  unfold rootMass
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, deviationProfile_mass, mul_zero, Finset.sum_const_zero]

theorem rootMass_constant (security : ℕ) (role : BodyRole) (queue : ℤ) :
    rootMass security role queue (fun _ => 1) = 0 := by
  funext color
  simpa only [rootMass, LinearMap.coe_mk, AddHom.coe_mk, mul_one, FiniteDist.expectation, Pi.zero_apply] using
    deviationProfile_root_mean security role queue color

theorem rootMass_physical (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ)
    (hcentered : (rootReference security).expectation input = 0) (color : ActualControls.Palette security) :
    rootMass security role queue input color =
      ∑ root, (rootReference security).weight root * input root * (shiftedLaw security role queue root).weight color := by
  change (∑ root, (rootReference security).weight root * input root *
    ((shiftedLaw security role queue root).weight color - (meanLaw security role queue).weight color)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ - (rootReference security).expectation input * _ = _
  rw [hcentered, zero_mul, sub_zero]

theorem weighted_pair_cauchy {Index : Type*} [Fintype Index] (law : FiniteDist Index)
    (first second : Index → ℝ) :
    (∑ index, law.weight index * first index * second index) ^ 2 ≤
      (∑ index, law.weight index * first index ^ 2) * ∑ index, law.weight index * second index ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro index _
    exact mul_nonneg (law.nonneg index) (sq_nonneg _)
  · intro index _
    exact mul_nonneg (law.nonneg index) (sq_nonneg _)
  · intro index _
    ring

theorem rootMass_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (rootMass security role queue input) ≤
      8 * deviation security ^ 2 * (rootReference security).l2Sq input := by
  have he (color : ActualControls.Palette security) := weighted_pair_cauchy (rootReference security) input
    (fun root => deviationProfile security role queue root color)
  unfold profileSquareNorm
  calc
    _ ≤ ∑ color, ((rootReference security).l2Sq input *
        ∑ root, (rootReference security).weight root * deviationProfile security role queue root color ^ 2) /
          (primaryLaw security).weight color := by
      apply Finset.sum_le_sum
      intro color _
      exact div_le_div_of_nonneg_right (he color) (primaryReference_positive security color).le
    _ = (rootReference security).l2Sq input * ∑ root, (rootReference security).weight root *
        profileSquareNorm (primaryLaw security).weight (deviationProfile security role queue root) := by
      simp only [profileSquareNorm, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (rootReference security).l2Sq input * ∑ root, (rootReference security).weight root * (8 * deviation security ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ ((rootReference security).l2Sq_nonneg input)
      exact Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left
        (deviationProfile_primary_energy security role queue root) ((rootReference security).nonneg root)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one]; ring

theorem rootMass_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    Real.sqrt (profileSquareNorm (primaryLaw security).weight (rootMass security role queue input)) ≤
      2 * Real.sqrt 2 * deviation security * Real.sqrt ((rootReference security).l2Sq input) := by
  have hd := deviation_nonneg security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt ((rootReference security).l2Sq_nonneg input)]
  exact (rootMass_energy security role queue input).trans_eq (by ring)

def profileDensity (security : ℕ) :
    (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  diagonal (fun color => ((primaryLaw security).weight color)⁻¹)

theorem profileDensity_apply (security : ℕ) (profile : ActualControls.Palette security → ℝ) (color : ActualControls.Palette security) :
    profileDensity security profile color = profile color / (primaryLaw security).weight color := by
  change ((primaryLaw security).weight color)⁻¹ * profile color = _
  ring

theorem profileDensity_mean (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    (primaryLaw security).expectation (profileDensity security profile) = ∑ color, profile color := by
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro color _
  rw [profileDensity_apply]
  field_simp [(primaryReference_positive security color).ne']

theorem profileDensity_energy (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    (primaryLaw security).l2Sq (profileDensity security profile) = profileSquareNorm (primaryLaw security).weight profile := by
  unfold FiniteDist.l2Sq FiniteDist.expectation profileSquareNorm
  apply Finset.sum_congr rfl
  intro color _
  change (primaryLaw security).weight color * (profileDensity security profile color) ^ 2 = _
  rw [profileDensity_apply]
  field_simp [(primaryReference_positive security color).ne']

/-- The actual calibrated first-response inverse, as one genuine local
linear map on the whole root Hilbert space. -/
def rootLift (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (densityInverse security).comp ((profileDensity security).comp (rootMass security role queue))

theorem rootLift_apply (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    rootLift security role queue input = densityInverse security (profileDensity security (rootMass security role queue input)) := rfl

theorem rootLift_mean (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).expectation (rootLift security role queue input) = 0 := by
  rw [rootLift_apply, densityInverse_mean, profileDensity_mean, rootMass_mass, mul_zero]

theorem rootLift_constant (security : ℕ) (role : BodyRole) (queue : ℤ) :
    rootLift security role queue (fun _ => 1) = 0 := by
  rw [rootLift_apply, rootMass_constant, map_zero, map_zero]

theorem rootLift_leading (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ)
    (color : ActualControls.Palette security) :
    (primaryLaw security).weight color * densityResponse security (rootLift security role queue input) color =
      rootMass security role queue input color := by
  rw [rootLift_apply, densityResponse_inverse, profileDensity_apply]
  field_simp [(primaryReference_positive security color).ne']

theorem rootLift_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).l2Sq (rootLift security role queue input) ≤
      32 * deviation security ^ 2 / activation security ^ 2 * (rootReference security).l2Sq input := by
  rw [rootLift_apply]
  calc
    _ ≤ (2 / activation security) ^ 2 * (primaryLaw security).l2Sq
        (profileDensity security (rootMass security role queue input)) := densityInverse_energy security _
    _ = (2 / activation security) ^ 2 * profileSquareNorm (primaryLaw security).weight (rootMass security role queue input) := by
      rw [profileDensity_energy]
    _ ≤ (2 / activation security) ^ 2 * (8 * deviation security ^ 2 * (rootReference security).l2Sq input) :=
      mul_le_mul_of_nonneg_left (rootMass_energy security role queue input) (sq_nonneg _)
    _ = _ := by ring

def rootCost (security : ℕ) : ℝ := 4 * Real.sqrt 2 * deviation security / activation security

theorem rootCost_nonneg (security : ℕ) : 0 ≤ rootCost security := by
  unfold rootCost
  have := deviation_nonneg security
  have := activation_pos security
  positivity

theorem rootCost_square (security : ℕ) :
    rootCost security ^ 2 = 32 * deviation security ^ 2 / activation security ^ 2 := by
  rw [rootCost, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem rootLift_energy_le_cost (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).l2Sq (rootLift security role queue input) ≤
      rootCost security ^ 2 * (rootReference security).l2Sq input := by
  rw [rootCost_square]
  exact rootLift_energy security role queue input

/-- The same scalar estimate applies to every joint root input, without
decomposing it into products of one-coordinate functions. -/
theorem joint_rootLift_energy (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin count => primaryLaw security)).l2Sq
        (TensorChannel.apply count (fun index => rootLift security (roles index) (queues index)) input) ≤
      (rootCost security ^ count) ^ 2 *
        (FiniteDist.independent (fun _ : Fin count => rootReference security)).l2Sq input := by
  have h := TensorChannel.energy_le count (fun _ => rootReference security) (fun _ => primaryLaw security)
    (fun index => rootLift security (roles index) (queues index)) (fun _ => rootCost security)
    (fun index => rootLift_energy_le_cost security (roles index) (queues index)) input
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

theorem rootLift_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    Real.sqrt ((primaryLaw security).l2Sq (rootLift security role queue input)) ≤
      rootCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (rootCost_nonneg security) (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt ((rootReference security).l2Sq_nonneg input)]
  exact rootLift_energy_le_cost security role queue input

theorem rootCost_decay (security : ℕ) : rootCost security ≤ 4128 / (Parameters.base security : ℝ) ^ 30 := by
  have hb := FirstResponse.base_pos security
  have hd := deviation_nonneg security
  have ha := activation_pos security
  have hinv : 1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ)))
      (FirstResponse.activation_lower_simple security)
    simpa only [one_div_one_div] using h
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  calc
    _ = 4 * Real.sqrt 2 * deviation security * (1 / activation security) := by unfold rootCost; ring
    _ ≤ 4 * 2 * deviation security * (4 * (Parameters.base security : ℝ)) := by gcongr
    _ = _ := by unfold deviation; field_simp; ring

/-- Retained coordinates are averaged only after the full fiberwise map.
The joint input need not split between the root and retained coordinate. -/
theorem retained_rootLift_energy {Retained : Type*} [Fintype Retained] (security : ℕ)
    (role : BodyRole) (queue : ℤ) (retained : FiniteDist Retained)
    (input : Root security → Retained → ℝ) :
    (∑ rest, retained.weight rest * (primaryLaw security).l2Sq
      (rootLift security role queue (fun root => input root rest))) ≤
      rootCost security ^ 2 * ∑ rest, retained.weight rest *
        (rootReference security).l2Sq (fun root => input root rest) := by
  calc
    _ ≤ ∑ rest, retained.weight rest * (rootCost security ^ 2 *
        (rootReference security).l2Sq (fun root => input root rest)) :=
      Finset.sum_le_sum fun rest _ => mul_le_mul_of_nonneg_left
        (rootLift_energy_le_cost security role queue _) (retained.nonneg rest)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rest _
      ring

theorem joint_rootLift_canonical (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Fin count => rootReference security) Finset.univ input) :
    Hoeffding.Canonical (fun _ : Fin count => primaryLaw security) Finset.univ
      (TensorChannel.apply count (fun index => rootLift security (roles index) (queues index)) input) := by
  letI : DecidableEq (Root security) := Classical.decEq _
  let matrix : Fin count → Root security → ActualControls.Palette security → ℝ :=
    fun index point => rootLift security (roles index) (queues index) (Pi.single point 1)
  have hmean (index : Fin count) (point : Root security) :
      (primaryLaw security).expectation (matrix index point) = 0 * (rootReference security).weight point := by
    rw [zero_mul]
    exact rootLift_mean security _ _ _
  have h := MixedKernel.matrixApply_canonical (fun _ : Fin count => rootReference security)
    (fun _ : Fin count => primaryLaw security) matrix (fun _ => 0) hmean input hcanonical
  have heq : MixedKernel.matrixApply matrix input =
      TensorChannel.apply count (fun index => rootLift security (roles index) (queues index)) input := by
    funext output
    simpa only [MixedKernel.matrixApply, matrix] using
      (TensorChannel.apply_formula_instance count (fun index => rootLift security (roles index) (queues index)) input output).symm
  rw [heq] at h
  exact h

theorem rootLift_massLeading (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    activation security • FirstResponse.response security
      (fun color => (primaryLaw security).weight color * rootLift security role queue input color) =
        rootMass security role queue input := by
  funext color
  have h := rootLift_leading security role queue input color
  rw [densityResponse_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    _ = (primaryLaw security).weight color *
        (activation security * FirstResponse.response security
          (fun point => (primaryLaw security).weight point * rootLift security role queue input point) color /
            (primaryLaw security).weight color) := by field_simp [(primaryReference_positive security color).ne']
    _ = _ := h

end

end CurrentAFT.RootTaggedLocal

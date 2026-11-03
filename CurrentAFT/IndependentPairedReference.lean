import CurrentAFT.PairedReferenceEnergy
import AFT.SignedFirstCoefficient
import AFT.ResponseEnergy

/-!
# The complete independent-root paired reference and its exact first coefficient

The second scalar is sampled once by the genuine joint reference. Its
value enters the attachment channel after the off-body pair has been
drawn. The distinct compensator uses its own independent comparison root.
The signed mass is the literal expectation of the public paired score.
-/

namespace CurrentAFT.IndependentPairedReference

open AFT DiffuseProfiles ProposalPrimary FirstHistogram PairedResponse PhysicalSynthesis
open LocalReferenceEnergy PairedReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFourDecidableEq : DecidableEq (Fin 4) := Classical.decEq _
local instance classicalOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw actualSeedLaw

private theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

private theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

private theorem indicator_eq_atom {Color : Type*} [DecidableEq Color]
    (first second : Color) (decision : Decidable (first = second)) :
    @ite ℝ (first = second) decision 1 0 = atom first second := by
  by_cases hequal : first = second <;> simp only [atom, hequal, if_true, if_false]

def attachmentBlurAt (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (actualSeedLaw security).mix (fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + scalar.val)))

theorem attachmentBlurAt_mean (security : ℕ) (output : Palette security) :
    (scalarLaw security).expectation (fun scalar => (attachmentBlurAt security scalar).weight output) =
      (bodyLaw security true).weight output := by
  unfold attachmentBlurAt bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight, if_true]
  change (scalarLaw security).expectation (fun scalar => (actualSeedLaw security).expectation (fun seed =>
      (safeLaw security).weight ((shiftEquiv security (actualBlur security seed + scalar.val)).symm output))) =
    (actualSeedLaw security).expectation (fun seed => (safeLaw security).weight
      ((shiftEquiv security (actualBlur security seed + actualSecond security seed)).symm output))
  rw [FiniteDist.expectation_comm]
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  conv_rhs => rw [FiniteDist.expectation_prod]
  simp only [actualBlur, actualSecond, FiniteDist.expectation_const]

def independentControlLaw (security : ℕ) (group : Group security) : FiniteDist (Fin 4 → Palette security) :=
  (referenceLaw security group.1).mix (fun sample =>
    ((compensatorBodyLaw security group.2).prod (attachmentBlurAt security sample.1)).map
      (fun outputs => PhysicalBlockTensors.quadrupleEquiv.symm (outputs.1, (sample.2, outputs.2))))

/-- The attachment marginal is the actual smoothed safe body law. It
does not depend on either selected public control. -/
theorem independentControlLaw_histogram (security : ℕ) (group : Group security) (output : Palette security) :
    (independentControlLaw security group).expectation (fun word => ∑ index, atom (word index) output) =
      endpointHistogram security (referenceLaw security group.1) output +
        (compensatorBodyLaw security group.2).weight output + (bodyLaw security true).weight output := by
  unfold independentControlLaw
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def]
  have hcount (sample : JointOutput security) (outputs : Palette security × Palette security) :
      (∑ index : Fin 4, atom ((PhysicalBlockTensors.quadrupleEquiv.symm (outputs.1, (sample.2, outputs.2))) index) output) =
        atom outputs.1 output + (atom sample.2.1 output + atom sample.2.2 output) + atom outputs.2 output := by
    rw [Fin.sum_univ_four]
    simp only [PhysicalBlockTensors.quadrupleEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hcount, FiniteDist.expectation_prod, FiniteDist.expectation_add, FiniteDist.expectation_const,
    expectation_atom]
  rw [reference_attachment_expectation security group.1
    (fun scalar => (attachmentBlurAt security scalar).weight output), attachmentBlurAt_mean]
  unfold endpointHistogram
  rw [FiniteDist.expectation_add]
  ring

def independentSignedMass (security : ℕ) (score : Palette security → ℝ)
    (word : Fin 4 → Palette security) : ℝ :=
  ∑ group, (groupLaw security).weight group * pairedChannel security score group *
    (independentControlLaw security group).weight word

theorem independentSigned_expectation (security : ℕ) (score : Palette security → ℝ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, independentSignedMass security score word * value word) =
      (groupLaw security).expectation (fun group => pairedChannel security score group *
        (independentControlLaw security group).expectation value) := by
  simp only [independentSignedMass, FiniteDist.expectation, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem independentSigned_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ word, independentSignedMass security score word) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have h := independentSigned_expectation security score (fun _ => 1)
  simp only [mul_one, FiniteDist.expectation_const] at h
  rw [h, pairedChannel_mean]

theorem independentSigned_mass_zero (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    (∑ word, independentSignedMass security score word) = 0 := by
  rw [independentSigned_mass, hcentered, mul_zero]

theorem independentSigned_first_profile (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) (output : Palette security) :
    LocalTensors.signedColorCount (independentSignedMass security score) output =
      activation security * FirstResponse.response security (scoreProfile security score) output := by
  unfold LocalTensors.signedColorCount
  simp_rw [indicator_eq_atom]
  change (∑ word, independentSignedMass security score word * ∑ index, atom (word index) output) = _
  rw [independentSigned_expectation]
  simp_rw [independentControlLaw_histogram]
  have hcomplete : (groupLaw security).expectation (fun group => pairedChannel security score group *
      (endpointHistogram security (referenceLaw security group.1) output +
        (compensatorBodyLaw security group.2).weight output + (bodyLaw security true).weight output)) =
      completeHistogramResponse security score (bodyLaw security true).weight output := by
    simp only [groupLaw, FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type,
      pairedChannel, completeHistogramResponse]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  rw [hcomplete]
  exact completeHistogramResponse_eq_activation_response security score hcentered _ output

/-- The complete first tensor preserves cancellation between all four
physical outputs; it is exactly the profile norm of the true first
response, rather than an assumed local operator. -/
theorem independentSigned_first_energy_identity (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (independentSignedMass security score) 1) =
      profileSquareNorm (uniformReference security).weight
        (fun output => activation security * FirstResponse.response security (scoreProfile security score) output) := by
  rw [LocalTensors.degreeTensor_one_energy_zero_mass (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (independentSignedMass security score) (independentSigned_mass_zero security score hcentered)]
  congr 1
  funext output
  exact independentSigned_first_profile security score hcentered output

private theorem signProfile_uniform_energy (security : ℕ) :
    profileSquareNorm (uniformReference security).weight (signProfile security) ≤ 1 := by
  have hq := FirstResponse.modulus_pos security
  have hd := Nat.cast_le (α := ℝ).mpr (FirstResponse.two_deletion_le_modulus security)
  push_cast at hd
  have hden : 0 < (Parameters.modulus security : ℝ) - deletion security := by linarith
  have hmajorant (color : Palette security) : |signProfile security color| ≤ 2 * (uniformReference security).weight color := by
    rw [uniformReference_weight]
    apply (signProfile_upper security color).trans
    rw [mul_one_div]
    apply (div_le_div_iff₀ hden hq).mpr
    linarith
  have h := signProfile_square_bound (uniformReference security).weight (signProfile security) 2
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr hq) hmajorant
  have hl1 := FirstResponse.signProfile_l1_le_half_activation security
  have ha := activation_le_half security
  linarith

private theorem profileEnergy_add (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (uniformReference security).weight (first + second) ≤
      2 * profileSquareNorm (uniformReference security).weight first +
        2 * profileSquareNorm (uniformReference security).weight second := by
  simp only [profileSquareNorm, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro color _
  have h : (first color + second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
    nlinarith [sq_nonneg (first color - second color)]
  exact (div_le_div_of_nonneg_right h ((uniformReference security).nonneg color)).trans_eq (by ring)

theorem independentSigned_first_energy (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (independentSignedMass security score) 1) ≤
        (2 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 2) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  rw [independentSigned_first_energy_identity security score hcentered]
  have hq := FirstResponse.modulus_pos security
  have hp := ActualControls.primaryReference_positive security
  have hu (color : Palette security) : 0 < (uniformReference security).weight color := by
    rw [uniformReference_weight]; exact one_div_pos.mpr hq
  have hdiagonal := profileSquareNorm_reference_comparison (primaryLaw security).weight
    (uniformReference security).weight (scoreProfile security score)
    ((Parameters.modulus security : ℝ) * primaryMaximum security) hp hu (fun color => by
      have hupper := GaussianHeights.primaryLaw_upper security color
      rw [uniformReference_weight]
      exact hupper.trans_eq (by unfold primaryMaximum; field_simp))
  change _ ≤ _ * profileSquareNorm (primaryLaw security).weight
    (fun color => (primaryLaw security).weight color * score color) at hdiagonal
  rw [profileSquareNorm_weight_mul] at hdiagonal
  have hsignal := mul_le_mul_of_nonneg_left hdiagonal (sq_nonneg (activation security))
  have hsign := signFunctional_sq_le (primaryLaw security).weight (FirstResponse.anchorSign security)
    (scoreProfile security score) hp (primaryLaw security).sum_one (FirstResponse.anchorSign_abs_le_one security)
  change _ ≤ profileSquareNorm (primaryLaw security).weight
    (fun color => (primaryLaw security).weight color * score color) at hsign
  rw [profileSquareNorm_weight_mul] at hsign
  have hresponseSign := mul_le_mul_of_nonneg_left (signProfile_uniform_energy security)
    (sq_nonneg (signFunctional (FirstResponse.anchorSign security) (scoreProfile security score)))
  have hformula : (fun output => activation security * FirstResponse.response security (scoreProfile security score) output) =
      activation security • scoreProfile security score +
        signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) • signProfile security := by
    funext output
    simp only [FirstResponse.response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change activation security * (scoreProfile security score output +
      ((activation security)⁻¹ * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score)) *
        signProfile security output) = _
    field_simp [(activation_pos security).ne']
  rw [hformula]
  have hsum := profileEnergy_add security (activation security • scoreProfile security score)
    (signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) • signProfile security)
  simp only [profileSquareNorm_smul] at hsum
  change _ ≤ activation security ^ 2 * ((Parameters.modulus security : ℝ) * primaryMaximum security *
    (primaryLaw security).expectation (fun primary => score primary ^ 2)) at hsignal
  change _ ≤ (primaryLaw security).expectation (fun primary => score primary ^ 2) at hsign
  nlinarith only [hsum, hsignal, hsign, hresponseSign]

theorem independentSigned_first_polynomial (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (independentSignedMass security score) 1) ≤
        ((2 + 131074 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := independentSigned_first_energy security score hcentered
  have hmax := activated_primaryMaximum security
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hpower : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 31 := one_le_pow₀ hb
  have hbudget : 2 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 2 ≤
      (2 + 131074 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by nlinarith only [hmax, hpower]
  exact h.trans (mul_le_mul_of_nonneg_right hbudget ((primaryLaw security).l2Sq_nonneg score))

end

end CurrentAFT.IndependentPairedReference

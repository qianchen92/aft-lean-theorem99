import CurrentAFT.RationalMassLiftProgram

/-! # A finite rational matrix tensor for the actual primary mass lift -/
namespace CurrentAFT.RationalMassLiftTensorProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def entry (security bits source output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (fun color => if color = source then 1 else 0) output

def current (security bits degree : ℕ) (profile : (Fin degree → ℕ) → ℚ) (output : Fin degree → ℕ) : ℚ :=
  ∑ source : Fin degree → Fin (PublicParameterProgram.modulus security).count,
    profile (fun index => (source index).val) * ∏ index, entry security bits (source index).val (output index)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw PublicParameterProgram.modulus

theorem actual_entry (security : ℕ) (source output : Palette security) :
    RationalMassLiftProgram.actual security (Pi.single source 1) output =
      PrimaryTensorInverse.densityInverse security (Pi.single source 1) output / (primaryLaw security).weight source := by
  have hprofile : RootTaggedLocal.profileDensity security (Pi.single source 1) =
      ((primaryLaw security).weight source)⁻¹ • (Pi.single source 1 : Palette security → ℝ) := by
    funext color
    simp only [RootTaggedLocal.profileDensity_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : color = source
    · subst color; simp
    · simp [h]
  rw [RationalMassLiftProgram.actual, LinearMap.comp_apply, hprofile, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem actual_formula (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ)
    (output : Fin degree → Palette security) :
    PrimaryTensorInverse.massLift security degree profile output =
      ∑ source : Fin degree → Palette security,
        profile source * ∏ index, RationalMassLiftProgram.actual security (Pi.single (source index) 1) (output index) := by
  change TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security)
    (PrimaryTensorInverse.massDensity security degree profile) output = _
  rw [TensorChannel.apply_formula_instance]
  apply Finset.sum_congr rfl
  intro source _
  simp only [actual_entry, Finset.prod_div_distrib, PrimaryTensorInverse.massDensity,
    PrimaryTensorInverse.referenceWeight]
  ring

theorem current_cast (security bits degree : ℕ) (profile : (Fin degree → ℕ) → ℚ) (output : Fin degree → Palette security) :
    (current security bits degree profile (fun index => (output index).val) : ℝ) =
      ∑ source : Fin degree → Palette security,
        (profile (fun index => (source index).val) : ℝ) *
          ∏ index, (entry security bits (source index).val (output index).val : ℝ) := by
  unfold current
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  rfl

theorem entry_error (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤
      RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := RationalMassLiftProgram.current_error security bits
    (fun color => if color = source.val then 1 else 0) 1 (by norm_num)
    (by intro color; dsimp only; split_ifs <;> norm_num) hfirst hprecision hbudget output
  have hp : (fun color : Palette security => ((if color.val = source.val then 1 else 0 : ℚ) : ℝ)) = Pi.single source 1 := by
    funext color
    by_cases h : color = source
    · subst color; simp
    · have hv : color.val ≠ source.val := fun heq => h (Fin.ext heq)
      simp [h, hv]
  rw [hp] at h
  simpa only [entry, mul_one] using h

def factorBound (security : ℕ) : ℝ :=
  1 + RationalTensorInverseProgram.actualBound security + RationalMassLiftProgram.errorConstant security

theorem factorBound_one_le (security : ℕ) : 1 ≤ factorBound security := by
  unfold factorBound
  linarith [RationalTensorInverseProgram.actualBound_nonneg security, RationalMassLiftProgram.errorConstant_nonneg security]

theorem entry_bounds (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ)| ≤ factorBound security ∧
      |RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤ factorBound security := by
  have hactual : |RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤ RationalTensorInverseProgram.actualBound security := by
    simpa only [mul_one] using RationalMassLiftProgram.actual_bound security (Pi.single source 1) 1 (by norm_num)
      (by intro color; simp only [Pi.single_apply]; split_ifs <;> norm_num) output
  have herror : |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| ≤
      RationalMassLiftProgram.errorConstant security :=
    (entry_error security bits source output hfirst hprecision hbudget).trans (by
      have hepsilon : 1 / (2 : ℝ)^bits ≤ 1 := by
        rw [one_div]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hepsilon
        (RationalMassLiftProgram.errorConstant_nonneg security))
  have hq : |(entry security bits source.val output.val : ℝ)| ≤
      |(entry security bits source.val output.val : ℝ) - RationalMassLiftProgram.actual security (Pi.single source 1) output| +
      |RationalMassLiftProgram.actual security (Pi.single source 1) output| := by
    simpa only [sub_zero] using abs_sub_le (entry security bits source.val output.val : ℝ)
      (RationalMassLiftProgram.actual security (Pi.single source 1) output) 0
  unfold factorBound
  constructor <;> linarith [RationalTensorInverseProgram.actualBound_nonneg security,
    RationalMassLiftProgram.errorConstant_nonneg security]

def errorConstant (security degree : ℕ) (bound profileError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^degree *
    (bound * degree * RationalMassLiftProgram.errorConstant security + profileError) * (factorBound security)^degree

theorem current_error (security bits degree : ℕ) (computed : (Fin degree → ℕ) → ℚ)
    (profile : (Fin degree → Palette security) → ℝ) (bound profileError : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ profileError)
    (hcomputed : ∀ source : Fin degree → Palette security, |(computed (fun index => (source index).val) : ℝ)| ≤ bound)
    (hdiff : ∀ source : Fin degree → Palette security,
      |(computed (fun index => (source index).val) : ℝ) - profile source| ≤ profileError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : Fin degree → Palette security) :
    |(current security bits degree computed (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.massLift security degree profile output| ≤
      errorConstant security degree bound profileError * (1 / (2 : ℝ)^bits) := by
  rw [current_cast, actual_formula, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hfactor : 0 ≤ factorBound security := (by norm_num : (0 : ℝ) ≤ 1).trans (factorBound_one_le security)
  have heps : 0 ≤ 1 / (2 : ℝ)^bits := by positivity
  have hmass := RationalMassLiftProgram.errorConstant_nonneg security
  calc
    _ ≤ ∑ _source : Fin degree → Palette security,
        (bound * degree * RationalMassLiftProgram.errorConstant security + profileError) *
          (factorBound security)^degree * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro source _
      let first := fun index : Fin degree => (entry security bits (source index).val (output index).val : ℝ)
      let second := fun index : Fin degree => RationalMassLiftProgram.actual security (Pi.single (source index) 1) (output index)
      have hprod := RationalTensorInverseProgram.product_difference_bound Finset.univ first second
        (factorBound security) (RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits))
        (factorBound_one_le security) (by positivity)
        (fun index _ => (entry_bounds security bits _ _ hfirst hprecision hbudget).1)
        (fun index _ => (entry_bounds security bits _ _ hfirst hprecision hbudget).2)
        (fun index _ => entry_error security bits _ _ hfirst hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_fin] at hprod
      have habs : |∏ index, second index| ≤ (factorBound security)^degree := by
        rw [Finset.abs_prod]
        exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun index _ => (entry_bounds security bits _ _ hfirst hprecision hbudget).2)).trans_eq (by simp)
      calc
        _ = |(computed (fun index => (source index).val) : ℝ) * ((∏ index, first index) - ∏ index, second index) +
            ((computed (fun index => (source index).val) : ℝ) - profile source) * ∏ index, second index| := by
          congr 1
          dsimp only [first, second]
          ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ bound * ((degree : ℝ) * (RationalMassLiftProgram.errorConstant security * (1 / (2 : ℝ)^bits)) *
              (factorBound security)^degree) +
            (profileError * (1 / (2 : ℝ)^bits)) * (factorBound security)^degree := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (hcomputed source) hprod (abs_nonneg _) hb)
            (mul_le_mul (hdiff source) habs (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold errorConstant
      push_cast
      ring

end
end CurrentAFT.RationalMassLiftTensorProgram

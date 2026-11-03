import CurrentAFT.CurrentFlagFiniteResponse

/-! A polynomial bound for the actual all-line right-hand side. -/

namespace CurrentAFT.CurrentFlagTargetNorm

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

theorem affine_target_norm (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hbudget : affineDeletionBudget allowed ≤ δ) (atom : ℚ)
    (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (markedDensityQ inputs allowed mark))‖ ≤ 1 + 2 * Fintype.card I := by
  have hδ1 : δ < 1 := by linarith
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  have hspike : realVector (markedDensityQ inputs allowed mark) = AffineFlagCalibration.uniformDensity marked :=
    markedDensityQ_cast inputs allowed mark hsurvival
  have hsallowed (index : I) (hi : ¬ (inputs index).1 = 0) (chart : Chart F)
      (hc : affineFeatures inputs index chart ∉ allowed index) : AffineFlagCalibration.uniformDensity marked chart = 0 := by
    have hz := markedChartLaw_support inputs allowed mark hsurvival chart
      (by rintro ⟨_, _, _, hh⟩; exact hc (hh index hi))
    simp only [marked, AffineFlagCalibration.uniformDensity, hz, mul_zero]
  have hsbound (index : I) (hi : ¬ (inputs index).1 = 0) (color : F) :
      conditional (FiniteDist.uniform (Chart F)) (affineFeatures inputs index) (AffineFlagCalibration.uniformDensity marked) color ≤
        1 / (1 - δ) := markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival index hi color
  have hd := (offLineDefect_bounds (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed
    (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked) (AffineFlagCalibration.uniformDensity_mean marked)
    (AffineFlagCalibration.uniformDensity_nonneg marked) hsallowed δ hδ0 hδ1 hsbound).1
  have hodds0 : 0 ≤ (atom : ℝ) / (1 - (atom : ℝ)) := div_nonneg ha0 (by linarith)
  have hodds1 : (atom : ℝ) / (1 - (atom : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - (atom : ℝ)), one_mul]
    linarith
  have ht : realVector (1 - (atom / (1 - atom)) • offLineDefectQ (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (markedDensityQ inputs allowed mark)) =
      1 - ((atom : ℝ) / (1 - (atom : ℝ))) • offLineDefect (FiniteDist.uniform (Chart F))
        (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked) := by
    have hc := offLineDefectQ_cast (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0)
      (markedDensityQ inputs allowed mark)
    rw [hspike] at hc
    funext chart
    have hh := congrFun hc chart
    simp only [realVector, Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_div, Rat.cast_one] at hh ⊢
    rw [hh]
  rw [ht]
  apply (norm_sub_le _ _).trans
  rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hodds0]
  have hden : (Fintype.card I : ℝ) / (1 - δ) ≤ 2 * Fintype.card I := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
    nlinarith [mul_le_mul_of_nonneg_left hδhalf (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)]
  have ho := mul_le_mul_of_nonneg_right hodds1
    (norm_nonneg (offLineDefect (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked)))
  nlinarith

local instance targetNormPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

theorem current_target_norm (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ
      (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      (fun index => (protectedInputs (Parameters.sourceCutoff security - 1)
        (Parameters.modulus security) index).1 = 0)
      (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark))‖ ≤
      1 + 2 * ((2 * (Parameters.sourceCutoff security - 1) + 1) ^ 2 : ℕ) := by
  have hb := leg_budget_conditions security
  have hhalf : legDeletionUpper security ≤ 1 / 2 := by
    have hn : (0 : ℝ) ≤ Fintype.card (ProtectedInput security) := Nat.cast_nonneg _
    have hh := hb.2.2.1
    nlinarith [mul_nonneg hn hb.1]
  simpa only [protectedInputs_card] using affine_target_norm
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark (legDeletionUpper security) hb.1 hhalf
    (protectedPalette_current_budget security baseline hbaseline) atom ha0 haHalf

theorem quarter_budget (inputs bits : ℕ) :
    (1 / 4 : ℝ) ^ (bits + (4 * inputs + 4)) * ((4 / 3) * (1 + 2 * inputs)) ≤ 1 / (2 : ℝ) ^ bits := by
  let extra := 4 * inputs + 4
  have hcoeff : (4 / 3 : ℝ) * (1 + 2 * inputs) ≤ extra := by dsimp [extra]; push_cast; nlinarith
  have hpower : (extra : ℝ) ≤ (2 : ℝ) ^ extra := by exact_mod_cast (Nat.lt_two_pow_self (n := extra)).le
  calc
    (1 / 4 : ℝ) ^ (bits + extra) * ((4 / 3) * (1 + 2 * inputs)) ≤
        (1 / 4 : ℝ) ^ (bits + extra) * (2 : ℝ) ^ extra :=
      mul_le_mul_of_nonneg_left (hcoeff.trans hpower) (by positivity)
    _ = (1 / 4 : ℝ) ^ bits * (1 / 2 : ℝ) ^ extra := by
      rw [pow_add, mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 4 : ℝ) ^ bits := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    _ ≤ (1 / 2 : ℝ) ^ bits := pow_le_pow_left₀ (by norm_num) (by norm_num) bits
    _ = 1 / (2 : ℝ) ^ bits := by simp only [div_pow, one_pow]

def precisionSteps (cutoff bits : ℕ) : ℕ := bits + (4 * (2 * cutoff + 1) ^ 2 + 4)

theorem current_precision_error (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) (bits : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(CurrentFlagFiniteResponse.currentRegular security baseline mark atom
        (precisionSteps (Parameters.sourceCutoff security - 1) bits) point : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤ 1 / (2 : ℝ) ^ bits := by
  apply (CurrentFlagFiniteResponse.currentRegular_error security baseline hbaseline mark atom
    (precisionSteps (Parameters.sourceCutoff security - 1) bits) point).trans
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (current_target_norm security baseline hbaseline mark atom ha0 haHalf)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)) (by positivity))
  exact quarter_budget ((2 * (Parameters.sourceCutoff security - 1) + 1) ^ 2) bits

end
end CurrentAFT.CurrentFlagTargetNorm

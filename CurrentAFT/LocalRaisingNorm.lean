import CurrentAFT.LocalRaisingLinear
import CurrentAFT.LocalCoefficientNorm
import CurrentAFT.GradedInverseNorm

/-! # Actual higher local coefficients and their graded finite norm -/
namespace CurrentAFT.LocalRaisingNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  LocalCoefficientFamily LocalCoefficientNorm NormalizedLocalPolynomial LocalRaisingFirst BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem independentComplete_eq_primary_add_higher (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    completeFamily security order (IndependentPairedReference.independentSignedMass security score) =
      primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered +
        higherFamily security order (IndependentPairedReference.independentSignedMass security score) := by
  funext arity
  change completeFamily security order (IndependentPairedReference.independentSignedMass security score) arity =
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered arity +
      higherFamily security order (IndependentPairedReference.independentSignedMass security score) arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [higherFamily_vanishesBelow security order _ arity hsmall, add_zero]
    exact sub_eq_zero.mp (independentComplete_sub_primary_raises security order horder score hcentered arity hsmall)
  · have hprimary : primaryFamily (primaryLaw security) (bodyReference security)
        order horder score hcentered arity = 0 := by
      unfold primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hprimary, zero_add]
    unfold completeFamily higherFamily
    simp only [IndependentPairedReference.independentSigned_mass_zero security score hcentered,
      zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl

def higherEnvelope (security : ℕ) (primaryFactor : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
    (8 * primaryFactor / activation security) ^ selected.card

theorem higherFamily_norm (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (higherFamily security order mass) ≤
        higherEnvelope security primaryFactor * Real.sqrt (primaryMassEnergy security mass) := by
  unfold higherFamily higherEnvelope
  apply (familyNorm_sum_le _ _ order primaryFactor bodyFactor hprimary hbody _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro selected _
  apply (selectedFamily_norm security order mass selected primaryFactor bodyFactor hprimary).trans_eq
  calc
    _ = (primaryFactor * (2 / activation security) * 4) ^ selected.card *
        Real.sqrt (primaryMassEnergy security mass) := by rw [mul_pow, mul_pow]; ring
    _ = _ := by congr 1; congr 1; ring

theorem higherEnvelope_nonneg (security : ℕ) (primaryFactor : ℝ) (hprimary : 0 ≤ primaryFactor) :
    0 ≤ higherEnvelope security primaryFactor := by
  unfold higherEnvelope
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg (by positivity) (activation_pos security).le) _)

theorem higherEnvelope_le (security : ℕ) (primaryFactor : ℝ) (hprimary : 0 ≤ primaryFactor)
    (hsmall : 8 * primaryFactor / activation security ≤ 1) :
    higherEnvelope security primaryFactor ≤ 16 * (8 * primaryFactor / activation security) ^ 2 := by
  have ht : 0 ≤ 8 * primaryFactor / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hprimary) (activation_pos security).le
  unfold higherEnvelope
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
        (8 * primaryFactor / activation security) ^ 2 := by
      apply Finset.sum_le_sum
      intro selected hselected
      exact pow_le_pow_of_le_one ht hsmall (Finset.mem_filter.mp hselected).2
    _ = ((Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card)).card *
        (8 * primaryFactor / activation security) ^ 2 := by simp
    _ ≤ 16 * (8 * primaryFactor / activation security) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 4))).filter
        (fun selected => 2 ≤ selected.card)).card ≤ 16 by
          calc
            _ ≤ Fintype.card (Finset (Fin 4)) := Finset.card_le_univ _
            _ = 16 := by simp)

def nonemptyEnvelope (security : ℕ) (primaryFactor : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    (8 * primaryFactor / activation security) ^ selected.card

theorem positiveFamily_defect_norm (security order : ℕ) (law : FiniteDist (Fin 4 → Palette security))
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (positiveFamily security order law - 1) ≤
        nonemptyEnvelope security primaryFactor * Real.sqrt (primaryMassEnergy security law.weight) := by
  have hequal : positiveFamily security order law - 1 =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        selectedFamily security order law.weight selected := by
    unfold positiveFamily completeFamily
    rw [law.sum_one, one_smul]
    abel
  rw [hequal]
  apply (familyNorm_sum_le _ _ order primaryFactor bodyFactor hprimary hbody _ _).trans
  unfold nonemptyEnvelope
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro selected _
  apply (selectedFamily_norm security order law.weight selected primaryFactor bodyFactor hprimary).trans_eq
  calc
    _ = (primaryFactor * (2 / activation security) * 4) ^ selected.card *
        Real.sqrt (primaryMassEnergy security law.weight) := by rw [mul_pow, mul_pow]; ring
    _ = _ := by congr 1; congr 1; ring

theorem nonemptyEnvelope_le (security : ℕ) (primaryFactor : ℝ) (hprimary : 0 ≤ primaryFactor)
    (hsmall : 8 * primaryFactor / activation security ≤ 1) :
    nonemptyEnvelope security primaryFactor ≤ 16 * (8 * primaryFactor / activation security) := by
  have ht : 0 ≤ 8 * primaryFactor / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hprimary) (activation_pos security).le
  unfold nonemptyEnvelope
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        (8 * primaryFactor / activation security) := by
      apply Finset.sum_le_sum
      intro selected hselected
      have hcard : 1 ≤ selected.card := by
        have hne := (Finset.mem_erase.mp hselected).1
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        omega
      simpa only [pow_one] using pow_le_pow_of_le_one ht hsmall hcard
    _ = ((Finset.univ : Finset (Finset (Fin 4))).erase ∅).card *
        (8 * primaryFactor / activation security) := by simp
    _ ≤ 16 * (8 * primaryFactor / activation security) := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 4))).erase ∅).card ≤ 16 by
        calc
          _ ≤ Fintype.card (Finset (Fin 4)) := Finset.card_le_univ _
          _ = 16 := by simp)

theorem actual_channel_factor (security : ℕ) :
    8 * BackgroundRates.primaryFactor security / activation security ≤
      32 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by
    rw [BackgroundRates.primaryFactor_eq]
    positivity
  calc
    _ = (8 * BackgroundRates.primaryFactor security) * (1 / activation security) := by ring
    _ ≤ (8 * BackgroundRates.primaryFactor security) * (4 * (Parameters.base security : ℝ)) :=
      mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (by positivity)
    _ = _ := by
      rw [BackgroundRates.primaryFactor_eq, show 64 = 63 + 1 by omega, pow_succ]
      field_simp [hb.ne']
      ring

theorem actual_channel_factor_le_one (security : ℕ) :
    8 * BackgroundRates.primaryFactor security / activation security ≤ 1 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have h5 : (32 : ℝ) ≤ (Parameters.base security : ℝ) ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb2 5
    norm_num only [show (2 : ℝ) ^ 5 = 32 by norm_num] at h
    exact h
  have hpower : (Parameters.base security : ℝ) ^ 5 ≤ (Parameters.base security : ℝ) ^ 63 :=
    pow_le_pow_right₀ hb1 (by omega)
  exact (actual_channel_factor security).trans ((div_le_one (pow_pos hb _)).mpr (h5.trans hpower))

theorem actual_higherEnvelope (security : ℕ) :
    higherEnvelope security (BackgroundRates.primaryFactor security) ≤
      16384 / (Parameters.base security : ℝ) ^ 126 := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have ht : 0 ≤ 8 * BackgroundRates.primaryFactor security / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hp) (activation_pos security).le
  calc
    _ ≤ 16 * (8 * BackgroundRates.primaryFactor security / activation security) ^ 2 :=
      higherEnvelope_le security _ hp (actual_channel_factor_le_one security)
    _ ≤ 16 * (32 / (Parameters.base security : ℝ) ^ 63) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (actual_channel_factor security) 2) (by norm_num)
    _ = _ := by rw [div_pow, ← pow_mul]; norm_num; ring

theorem actual_nonemptyEnvelope (security : ℕ) :
    nonemptyEnvelope security (BackgroundRates.primaryFactor security) ≤
      512 / (Parameters.base security : ℝ) ^ 63 := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  exact (nonemptyEnvelope_le security _ hp (actual_channel_factor_le_one security)).trans
    ((mul_le_mul_of_nonneg_left (actual_channel_factor security) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end
end CurrentAFT.LocalRaisingNorm

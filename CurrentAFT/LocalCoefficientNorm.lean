import CurrentAFT.LocalCoefficientFamily
import CurrentAFT.GradedControlNorm
import CurrentAFT.BackgroundFamilies

/-! # Genuine local coefficient norm budgets after the actual primary inverse -/

namespace CurrentAFT.LocalCoefficientNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
open LocalCoefficientFamily LocalReferenceEnergy PairedReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

private theorem blockEnergy_no_body {Primary Body Index : Type*}
    [Fintype Primary] [Fintype Body] [Fintype Index]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (kernel : (Index → Primary) → ℝ) :
    blockEnergy primary body (fun colors (_ : Fin 0 → Body) => kernel colors) =
      (FiniteDist.independent (fun _ : Index => primary)).l2Sq kernel := by
  unfold blockEnergy FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]

def primaryMassEnergy (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : ℝ :=
  profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight mass

theorem selectedDensity_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (selectedDensity security degree mass selected hdegree) ≤
        ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  let raw : Kernel (Primary := Palette security) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
      (fun _ : Fin 4 => uniformReference security) mass selected colors
  rw [← blockEnergy_no_body (primaryLaw security) (FiniteDist.uniform Unit)]
  change blockEnergy (primaryLaw security) (FiniteDist.uniform Unit)
    (reindexKernel (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw) ≤ _
  rw [blockEnergy_reindex, blockEnergy_no_body]
  have h := LocalTensors.referenceRestrictedComponent_l2Sq_le (fun _ : Fin 4 => primaryLaw security)
    (fun _ : Fin 4 => uniformReference security) (fun _ => primaryReference_positive security) mass selected 2 (by norm_num)
    (fun _ color => by
      rw [uniformReference_weight]
      have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
        simpa only [primaryLaw] using primaryProfile_atom_lower security color
      have hq := FirstResponse.modulus_pos security
      have hidentity : (1 / (Parameters.modulus security : ℝ)) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
      rw [hidentity]
      exact mul_le_mul_of_nonneg_left hlower (by norm_num))
  change _ ≤ ((2 * (2 : ℝ)) ^ selected.card) ^ 2 * densitySquareNorm
    (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight
    (fun word => mass word / (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight word) at h
  rw [densityScore_square] at h
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, primaryMassEnergy] using h

theorem normalizedSelectedDensity_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (normalizedSelectedDensity security degree mass selected hdegree) ≤
        ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  have h := PrimaryTensorInverse.tensorInverse_energy security degree (selectedDensity security degree mass selected hdegree)
  exact h.trans ((mul_le_mul_of_nonneg_left (selectedDensity_energy security degree mass selected hdegree)
    (sq_nonneg _)).trans_eq (by ring))

theorem selectedKernel_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    blockEnergy (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  change blockEnergy (primaryLaw security) (bodyReference security)
    (symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
      normalizedSelectedDensity security degree mass selected hdegree colors)) ≤ _
  apply (blockEnergy_symmetrize_le _ _ _).trans
  rw [blockEnergy_no_body]
  exact normalizedSelectedDensity_energy security degree mass selected hdegree

theorem primaryMassEnergy_uniform_le (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    primaryMassEnergy security mass ≤
      16 * profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight mass := by
  let primary := FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)
  let uniform := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hu (word : Fin 4 → Palette security) : 0 < uniform.weight word := by
    change 0 < ∏ index : Fin 4, (uniformReference security).weight (word index)
    exact Finset.prod_pos (fun _ _ => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
  have hcompare (word : Fin 4 → Palette security) : uniform.weight word ≤ 16 * primary.weight word := by
    have h := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
      (fun index _ => (uniformReference security).nonneg (word index))
      (fun index _ => show (uniformReference security).weight (word index) ≤ 2 * (primaryLaw security).weight (word index) by
        rw [uniformReference_weight]
        have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight (word index) := by
          simpa only [primaryLaw] using primaryProfile_atom_lower security (word index)
        have hidentity : 1 / (Parameters.modulus security : ℝ) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
        rw [hidentity]
        exact mul_le_mul_of_nonneg_left hlower (by norm_num))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (2 : ℝ) ^ 4 = 16 by norm_num] using h
  unfold primaryMassEnergy profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  have hlower : uniform.weight word / 16 ≤ primary.weight word := (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr (by
    simpa only [mul_comm] using hcompare word)
  exact (div_le_div_of_nonneg_left (sq_nonneg (mass word)) (div_pos (hu word) (by norm_num)) hlower).trans_eq (by ring)

theorem selectedKernel_paired_energy (security degree : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    blockEnergy (primaryLaw security) (bodyReference security)
      (selectedKernel security degree
        (pairedMassAt security compensatorRoot attachmentRoot scalar score) selected hdegree).val ≤
      (((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * 16 *
        (4128 * pairBudget security)) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := selectedKernel_energy security degree (pairedMassAt security compensatorRoot attachmentRoot scalar score) selected hdegree
  have hreference := primaryMassEnergy_uniform_le security (pairedMassAt security compensatorRoot attachmentRoot scalar score)
  have hphysical := pairedMassAt_energy security compensatorRoot attachmentRoot scalar score
  have hmass := hreference.trans (mul_le_mul_of_nonneg_left hphysical (by norm_num : (0 : ℝ) ≤ 16))
  exact h.trans ((mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (by ring))

theorem selectedKernel_norm (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card * Real.sqrt (primaryMassEnergy security mass) := by
  let coefficient := (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg (pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _) (by positivity)
  have h := Real.sqrt_le_sqrt (selectedKernel_energy security degree mass selected hdegree)
  change blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤ _ at h
  have hrewrite : ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass =
      coefficient ^ 2 * primaryMassEnergy security mass := by dsimp only [coefficient]; ring
  rw [hrewrite, Real.sqrt_mul (sq_nonneg coefficient), Real.sqrt_sq_eq_abs, abs_of_nonneg hcoefficient] at h
  exact h

theorem selectedFamily_norm (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (primaryFactor bodyFactor : ℝ) (hprimaryFactor : 0 ≤ primaryFactor) :
    GradedControlNorm.familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (selectedFamily security order mass selected) ≤
        primaryFactor ^ selected.card * ((2 / activation security) ^ selected.card * (4 : ℝ) ^ selected.card *
          Real.sqrt (primaryMassEnergy security mass)) := by
  unfold selectedFamily
  split_ifs with hdegree
  · rw [BackgroundFamilies.familyNorm_single]
    change gradeWeight primaryFactor bodyFactor selected.card 0 *
      blockL2 (primaryLaw security) (bodyReference security)
        (selectedKernel security selected.card mass selected (by simp)).val ≤ _
    simp only [gradeWeight, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (selectedKernel_norm security selected.card mass selected (by simp))
      (pow_nonneg hprimaryFactor _)
  · rw [GradedControlStability.familyNorm_zero]
    apply mul_nonneg (pow_nonneg hprimaryFactor _)
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _
      · positivity
    · exact Real.sqrt_nonneg _

end

end CurrentAFT.LocalCoefficientNorm

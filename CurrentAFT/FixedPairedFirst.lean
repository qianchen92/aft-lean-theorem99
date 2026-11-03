import CurrentAFT.FixedDiffuseProfiles
import CurrentAFT.PairedReferenceEnergy
import AFT.SignedFirstCoefficient
import AFT.ResponseEnergy

/-! # Sharp first coefficient of the actual paired group at fixed roots -/

namespace CurrentAFT.FixedPairedFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstHistogram PairedResponse PhysicalSynthesis
open LocalReferenceEnergy PairedReferenceEnergy ReferenceMarginals FixedDiffuseProfiles
open scoped BigOperators Classical

noncomputable section

local instance classicalFourDecidableEq : DecidableEq (Fin 4) := Classical.decEq _
local instance classicalOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

private theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

private theorem indicator_eq_atom {Color : Type*} [DecidableEq Color]
    (first second : Color) (decision : Decidable (first = second)) :
    @ite ℝ (first = second) decision 1 0 = atom first second := by
  by_cases hequal : first = second <;> simp only [atom, hequal, if_true, if_false]

private theorem pair_first_expectation {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    law.expectation (fun pair => atom pair.1 color) = ∑ second, law.weight (color, second) := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, atom]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem pair_second_expectation {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    law.expectation (fun pair => atom pair.2 color) = ∑ first, law.weight (first, color) := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, atom, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

def pointLaw (security : ℕ) (color : Palette security) : FiniteDist (Palette security) :=
  (FiniteDist.uniform Unit).map (fun _ => color)

theorem pointLaw_weight (security : ℕ) (color output : Palette security) :
    (pointLaw security color).weight output = atom color output := by
  classical
  simp only [pointLaw, FiniteDist.map_weight, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, atom]

def fixedControlLaw (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) : FiniteDist (Fin 4 → Palette security) :=
  ((pointLaw security (shiftEquiv security compensatorRoot group.2)).prod
    ((pairAt security group.1 scalar).prod (attachmentAt security attachmentRoot scalar))).map
      PhysicalBlockTensors.quadrupleEquiv.symm

theorem fixedControlLaw_weight (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) (word : Fin 4 → Palette security) :
    (fixedControlLaw security compensatorRoot attachmentRoot scalar group).weight word =
      controlMass security compensatorRoot attachmentRoot scalar group word := by
  rw [fixedControlLaw, FiniteDist.map_equiv_weight]
  change (pointLaw security (shiftEquiv security compensatorRoot group.2)).weight (word 0) *
    ((pairAt security group.1 scalar).weight (word 1, word 2) *
      (attachmentAt security attachmentRoot scalar).weight (word 3)) = _
  rw [pointLaw_weight]
  unfold controlMass
  by_cases hequal : shiftEquiv security compensatorRoot group.2 = word 0 <;>
    simp only [atom, hequal, if_true, if_false] <;> ring

theorem fixedControlLaw_histogram (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) (output : Palette security) :
    (fixedControlLaw security compensatorRoot attachmentRoot scalar group).expectation
        (fun word => ∑ index, atom (word index) output) =
      ((∑ second, (pairAt security group.1 scalar).weight (output, second)) +
        (∑ first, (pairAt security group.1 scalar).weight (first, output))) +
      atom (shiftEquiv security compensatorRoot group.2) output +
        (attachmentAt security attachmentRoot scalar).weight output := by
  unfold fixedControlLaw
  rw [FiniteDist.expectation_map]
  have hcount (draw : Palette security × ((Palette security × Palette security) × Palette security)) :
      (∑ index : Fin 4, atom (PhysicalBlockTensors.quadrupleEquiv.symm draw index) output) =
        atom draw.1 output + (atom draw.2.1.1 output + atom draw.2.1.2 output) + atom draw.2.2 output := by
    rw [Fin.sum_univ_four]
    simp only [PhysicalBlockTensors.quadrupleEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp only [Function.comp_def]
  simp_rw [hcount, FiniteDist.expectation_prod, FiniteDist.expectation_add, FiniteDist.expectation_const,
    expectation_atom, pointLaw_weight, pair_first_expectation, pair_second_expectation]
  ring

theorem fixedMass_expectation (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word * value word) =
      (groupLaw security).expectation (fun group => pairedChannel security score group *
        (fixedControlLaw security compensatorRoot attachmentRoot scalar group).expectation value) := by
  rw [← pairedMassLinear_apply]
  simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    fixedControlLaw_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem fixedMass_sum (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have h := fixedMass_expectation security compensatorRoot attachmentRoot scalar score (fun _ => 1)
  simp only [mul_one, FiniteDist.expectation_const] at h
  rw [h, pairedChannel_mean]

private theorem paired_histogram_decomposition {Primary Center : Type*} [Fintype Primary] [Fintype Center]
    (primary : FiniteDist Primary) (center : FiniteDist Center) (score : Primary → ℝ) (compensator : Center → ℝ)
    (hscore : primary.expectation score = 0) (hcompensator : center.expectation compensator = 0)
    (leg : Primary → ℝ) (body : Center → ℝ) (other : ℝ) :
    (primary.prod center).expectation (fun group =>
      (score group.1 - compensator group.2) * (leg group.1 + body group.2 + other)) =
      primary.expectation (fun color => score color * leg color) -
        center.expectation (fun color => compensator color * body color) := by
  rw [FiniteDist.expectation_prod]
  have hexpand (first : Primary) (second : Center) :
      (score first - compensator second) * (leg first + body second + other) =
        score first * leg first + score first * body second + score first * other -
          compensator second * leg first - compensator second * body second - compensator second * other := by ring
  simp only [hexpand, FiniteDist.expectation_add, FiniteDist.expectation_sub,
    FiniteDist.expectation_const_mul, FiniteDist.expectation_mul_const, FiniteDist.expectation_const,
    hscore, hcompensator]
  ring

theorem fixedMass_histogram_decomposition (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) (output : Palette security) :
    LocalTensors.signedColorCount (pairedMassAt security compensatorRoot attachmentRoot scalar score) output =
      (primaryLaw security).expectation (fun primary => score primary *
        ((∑ second, (pairAt security primary scalar).weight (output, second)) +
          (∑ first, (pairAt security primary scalar).weight (first, output)))) -
        signedCompensatorAt security compensatorRoot score output := by
  unfold LocalTensors.signedColorCount
  simp_rw [indicator_eq_atom]
  rw [fixedMass_expectation]
  simp_rw [fixedControlLaw_histogram]
  change ((primaryLaw security).prod (centerLaw security)).expectation (fun group =>
    (score group.1 - compensatorScore security score group.2) * _) = _
  have hcomp : (centerLaw security).expectation (compensatorScore security score) = 0 := by
    change (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0
    rw [compensatorScore_mass]
    change activation security * (primaryLaw security).expectation score = 0
    rw [hcentered, mul_zero]
  rw [paired_histogram_decomposition (primaryLaw security) (centerLaw security) score
    (compensatorScore security score) hcentered hcomp
    (fun primary => (∑ second, (pairAt security primary scalar).weight (output, second)) +
      (∑ first, (pairAt security primary scalar).weight (first, output)))
    (fun center => atom (shiftEquiv security compensatorRoot center) output)
    ((attachmentAt security attachmentRoot scalar).weight output)]
  rw [signedCompensatorAt_channel]
  congr 1
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro center _
  by_cases hequal : shiftEquiv security compensatorRoot center = output <;>
    simp only [atom, hequal, if_true, if_false] <;> ring

def compensatorAnchorAt (security : ℕ) (root : ℤ) (primary : Palette security) : FiniteDist (Palette security) :=
  (InwardAnchor.smoothedAnchorLaw security primary).map (shiftEquiv security root)

theorem compensatorAnchorAt_primary_height (security : ℕ) (root : ℤ) (output : Palette security) :
    (∑ primary, (primaryLaw security).weight primary * (compensatorAnchorAt security root primary).weight output) ≤
      2 * primaryMaximum security := by
  have hmaximum : 0 ≤ primaryMaximum security :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  simp only [compensatorAnchorAt, FiniteDist.map_equiv_weight]
  calc
    _ ≤ primaryMaximum security * ∑ primary,
        (InwardAnchor.smoothedAnchorLaw security primary).weight ((shiftEquiv security root).symm output) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro primary _
      exact mul_le_mul_of_nonneg_right (GaussianHeights.primaryLaw_upper security primary)
        ((InwardAnchor.smoothedAnchorLaw security primary).nonneg _)
    _ ≤ primaryMaximum security * 2 := mul_le_mul_of_nonneg_left
      (InwardAnchor.smoothedAnchorLaw_row_sum_le_two security _) hmaximum
    _ = _ := by ring

theorem signedCompensatorAt_anchor (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) :
    signedCompensatorAt security root score output = activation security *
      applyAnchor (fun primary center => (compensatorAnchorAt security root primary).weight center)
        (scoreProfile security score) output := by
  unfold signedCompensatorAt
  rw [center_weight_compensator]
  simp only [anchorWeightedScore, compensatorAnchorAt, FiniteDist.map_equiv_weight,
    applyAnchor, scoreProfile, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem fixedMass_first_formula (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    LocalTensors.signedColorCount (pairedMassAt security compensatorRoot attachmentRoot scalar score) =
      activation security • scoreProfile security score +
        signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) • fixedSignProfile security scalar +
        activation security • applyAnchor (fun primary output => (markedCompanionAt security primary scalar).weight output)
          (scoreProfile security score) -
        activation security • applyAnchor (fun primary output => (compensatorAnchorAt security compensatorRoot primary).weight output)
          (scoreProfile security score) := by
  funext output
  rw [fixedMass_histogram_decomposition security compensatorRoot attachmentRoot scalar score hcentered,
    signedCompensatorAt_anchor]
  simp_rw [pairAt_histogram]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold FiniteDist.expectation
  simp only [← mul_assoc]
  change (∑ primary, scoreProfile security score primary * _) = _
  calc
    _ = activation security * (∑ primary, scoreProfile security score primary * atom primary output) +
        activation security * (∑ primary, (markedCompanionAt security primary scalar).weight output * scoreProfile security score primary) +
        (2 * (1 - activation security) * fixedMean security scalar output) * (∑ primary, scoreProfile security score primary) +
        fixedSignProfile security scalar output *
          (∑ primary, FirstResponse.anchorSign security primary * scoreProfile security score primary) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      have hzero : (∑ primary, scoreProfile security score primary) = 0 := hcentered
      have hatom : (∑ primary, scoreProfile security score primary * atom primary output) = scoreProfile security score output := by
        simp only [atom, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hatom, hzero, mul_zero, add_zero]
      unfold applyAnchor signFunctional
      ring

/-- The complete signed histogram has zero total mass and the exact
four-channel response at every fixed attachment and compensator root. -/
theorem fixedPaired_first_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1) ≤
        (20 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 16) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hmass : (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word) = 0 := by
    rw [fixedMass_sum, hcentered, mul_zero]
  have hq := FirstResponse.modulus_pos security
  have hu (color : Palette security) : 0 < (uniformReference security).weight color := by
    rw [uniformReference_weight]; exact one_div_pos.mpr hq
  have hfirstAnchor (output : Palette security) :
      applyAnchor (fun primary color => (markedCompanionAt security primary scalar).weight color)
        (primaryLaw security).weight output ≤ 2 * primaryMaximum security := by
    unfold applyAnchor
    simpa only [mul_comm] using markedCompanionAt_primary_height security scalar output
  have hsecondAnchor (output : Palette security) :
      applyAnchor (fun primary color => (compensatorAnchorAt security compensatorRoot primary).weight color)
        (primaryLaw security).weight output ≤ 2 * primaryMaximum security := by
    unfold applyAnchor
    simpa only [mul_comm] using compensatorAnchorAt_primary_height security compensatorRoot output
  rw [LocalTensors.degreeTensor_one_energy_zero_mass (uniformReference security) hu _ hmass,
    fixedMass_first_formula security compensatorRoot attachmentRoot scalar score hcentered]
  have h := four_channel_response_energy (primaryLaw security).weight (uniformReference security).weight
    (FirstResponse.anchorSign security) (fixedSignProfile security scalar)
    (fun primary output => (markedCompanionAt security primary scalar).weight output)
    (fun primary output => (compensatorAnchorAt security compensatorRoot primary).weight output)
    (activation security) ((Parameters.modulus security : ℝ) * primaryMaximum security) 2 2
    (2 * (Parameters.modulus security : ℝ) * primaryMaximum security)
    (primaryReference_positive security) (primaryLaw security).sum_one hu
    (fun color => by
      rw [uniformReference_weight]
      exact (GaussianHeights.primaryLaw_upper security color).trans_eq (by unfold primaryMaximum; field_simp))
    (FirstResponse.anchorSign_abs_le_one security) (by norm_num)
    (fun color => by rw [uniformReference_weight, mul_one_div]; exact fixedSignProfile_height security scalar color)
    (fixedSignProfile_l1 security scalar)
    (fun primary output => (markedCompanionAt security primary scalar).nonneg output)
    (fun primary output => (compensatorAnchorAt security compensatorRoot primary).nonneg output)
    (fun primary => (markedCompanionAt security primary scalar).sum_one)
    (fun primary => (compensatorAnchorAt security compensatorRoot primary).sum_one)
    (fun output => by
      rw [uniformReference_weight]
      exact (hfirstAnchor output).trans_eq (by field_simp))
    (fun output => by
      rw [uniformReference_weight]
      exact (hsecondAnchor output).trans_eq (by field_simp))
    (scoreProfile security score)
  change _ ≤ _ * profileSquareNorm (primaryLaw security).weight
    (fun primary => (primaryLaw security).weight primary * score primary) at h
  rw [profileSquareNorm_weight_mul] at h
  exact h.trans_eq (by change _ = _ * (primaryLaw security).l2Sq score; ring)

theorem fixedPaired_first_polynomial (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1) ≤
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := fixedPaired_first_energy security compensatorRoot attachmentRoot scalar score hcentered
  have hmax := activated_primaryMaximum security
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hpower : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 31 := one_le_pow₀ hb
  have hbudget : 20 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 16 ≤
      (16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by nlinarith only [hmax, hpower]
  exact h.trans (mul_le_mul_of_nonneg_right hbudget ((primaryLaw security).l2Sq_nonneg score))

theorem jointPaired_first_polynomial {Root : Type*} [Fintype Root]
    (security : ℕ) (source : FiniteDist Root) (compensatorRoot attachmentRoot : Root → ℤ)
    (scalar : Root → Scalar security) (score : Root → Palette security → ℝ)
    (hcentered : ∀ root, (primaryLaw security).expectation (score root) = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (jointPairedMass security source compensatorRoot attachmentRoot scalar score) 1) ≤
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          source.expectation (fun root => (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
  have hmass : jointPairedMass security source compensatorRoot attachmentRoot scalar score =
      ∑ root, source.weight root • pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) := by
    funext word
    simp only [jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hlinear : LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (jointPairedMass security source compensatorRoot attachmentRoot scalar score) 1 =
      ∑ root, source.weight root • LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
        (pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root)) 1 := by
    rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
    simp only [map_smul, LocalTensors.degreeTensorLinear_apply]
  rw [hlinear]
  have havg := profileSquareNorm_average_le source (fun _ : Fin 1 → Palette security => (1 : ℝ))
    (fun _ => by norm_num) (fun root => LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root)) 1)
  simp only [profileSquareNorm, div_one] at havg
  simp only [BlockFock.tensorEnergy, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply havg.trans
  calc
    _ ≤ ∑ root, source.weight root * (((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
        (primaryLaw security).expectation (fun primary => score root primary ^ 2)) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left
        (fixedPaired_first_polynomial security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) (hcentered root))
        (source.nonneg root))
    _ = _ := by
      change (∑ root, source.weight root * (((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
        (primaryLaw security).expectation (fun primary => score root primary ^ 2))) =
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          ∑ root, source.weight root * (primaryLaw security).expectation (fun primary => score root primary ^ 2)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro root _
      ring

theorem joint_retained_paired_first_polynomial {Root Retained : Type*} [Fintype Root] [Fintype Retained]
    (security : ℕ) (source : FiniteDist Root) (retained : FiniteDist Retained)
    (compensatorRoot attachmentRoot : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Retained → Palette security → ℝ)
    (hcentered : ∀ root coordinate, (primaryLaw security).expectation (score root coordinate) = 0) :
    (∑ coordinate, retained.weight coordinate *
      BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
        (jointPairedMass security source compensatorRoot attachmentRoot scalar (fun root => score root coordinate)) 1)) ≤
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          source.expectation (fun root => retained.expectation (fun coordinate =>
            (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) := by
  calc
    _ ≤ ∑ coordinate, retained.weight coordinate *
        (((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          source.expectation (fun root => (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) :=
      Finset.sum_le_sum (fun coordinate _ => mul_le_mul_of_nonneg_left
        (jointPaired_first_polynomial security source compensatorRoot attachmentRoot scalar
          (fun root => score root coordinate) (fun root => hcentered root coordinate)) (retained.nonneg coordinate))
    _ = _ := by
      simp only [FiniteDist.expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro root _
      apply Finset.sum_congr rfl
      intro coordinate _
      apply Finset.sum_congr rfl
      intro primary _
      ring

end

end CurrentAFT.FixedPairedFirst

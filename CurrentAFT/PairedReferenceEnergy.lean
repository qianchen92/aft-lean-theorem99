import CurrentAFT.LocalReferenceEnergy
import CurrentAFT.PhysicalSynthesis
import AFT.LocalCoefficientLinear

/-!
# The genuine four-output paired group

The signed mass is obtained by the actual primary score minus its actual
compensator score. The two terms below are exactly the corresponding
finite control sums. The triple retains its same-source scalar; its
attachment center is safe-uniform, while the distinct compensator center
uses the constructed free-center law.
-/

namespace CurrentAFT.PairedReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary PairedResponse FirstHistogram LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base primaryLaw centerLaw activation

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

def compensatorAt (security : ℕ) (root : ℤ) : FiniteDist (Palette security) :=
  (centerLaw security).map (shiftEquiv security root)

def signedCompensatorAt (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) : ℝ :=
  (centerLaw security).weight ((shiftEquiv security root).symm output) *
    compensatorScore security score ((shiftEquiv security root).symm output)

theorem signedCompensatorAt_channel (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) :
    signedCompensatorAt security root score output =
      ∑ center, (centerLaw security).weight center * compensatorScore security score center *
        atom (shiftEquiv security root center) output := by
  classical
  have hequal (center : Palette security) : shiftEquiv security root center = output ↔
      center = (shiftEquiv security root).symm output := (Equiv.eq_symm_apply _).symm
  simp only [atom, hequal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    signedCompensatorAt]

theorem compensatorAt_energy (security : ℕ) (root : ℤ) :
    profileSquareNorm (uniformReference security).weight (compensatorAt security root).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (compensatorAt security root).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr hq)
    (compensatorAt security root).nonneg (fun color => by
      rw [compensatorAt, FiniteDist.map_equiv_weight, uniformReference_weight]
      exact (centerLaw_height security _).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

theorem signedCompensatorAt_energy (security : ℕ) (root : ℤ) (score : Palette security → ℝ) :
    profileSquareNorm (uniformReference security).weight (signedCompensatorAt security root score) ≤
      1024 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hq := FirstResponse.modulus_pos security
  have hfirst : profileSquareNorm (uniformReference security).weight (signedCompensatorAt security root score) ≤
      4 * ∑ center, (centerLaw security).weight center * compensatorScore security score center ^ 2 := by
    unfold profileSquareNorm
    rw [← (shiftEquiv security root).sum_comp]
    simp only [signedCompensatorAt, Equiv.symm_apply_apply, uniformReference_weight]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro center _
    have hheight := centerLaw_height security center
    have hnonneg := (centerLaw security).nonneg center
    have hpoint := mul_le_mul_of_nonneg_right hheight
      (mul_nonneg hnonneg (sq_nonneg (compensatorScore security score center)))
    apply (div_le_iff₀ (one_div_pos.mpr hq)).mpr
    convert hpoint using 1 <;> ring
  rw [PhysicalSynthesis.compensator_square_mean] at hfirst
  have hcomp := compensator_energy_le security score
  change activation security ^ 2 * profileSquareNorm (centerLaw security).weight
    (anchorWeightedScore security score) ≤
      256 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2) at hcomp
  calc
    _ ≤ 4 * (activation security ^ 2 * profileSquareNorm (centerLaw security).weight
        (anchorWeightedScore security score)) := hfirst
    _ ≤ 4 * (256 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
      mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = _ := by ring

def pairedMassAt (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (word : Fin 4 → Palette security) : ℝ :=
  PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score) word -
    PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word

theorem pairBudget_nonneg (security : ℕ) : 0 ≤ pairBudget security := by
  unfold pairBudget primaryMaximum
  have hmark := (markMass_pos security).le
  positivity

private theorem profileEnergy_sub_le {Output : Type*} [Fintype Output]
    (reference first second : Output → ℝ) (href : ∀ output, 0 ≤ reference output) :
    profileSquareNorm reference (fun output => first output - second output) ≤
      2 * profileSquareNorm reference first + 2 * profileSquareNorm reference second := by
  simp only [profileSquareNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  have h : (first output - second output) ^ 2 ≤ 2 * first output ^ 2 + 2 * second output ^ 2 := by
    nlinarith [sq_nonneg (first output + second output)]
  exact (div_le_div_of_nonneg_right h (href output)).trans_eq (by ring)

/-- All four coordinates are present in the same signed mass. The two
terms arise from the actual paired numerator, not separate control laws. -/
theorem pairedMassAt_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤
        (4128 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hfirst := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar score)
  have hsecond := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (signedCompensatorAt security compensatorRoot score) (tripleMassAt security attachmentRoot scalar (fun _ => 1))
  change densitySquareNorm reference.weight (fun word =>
    PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score) word / reference.weight word) = _ at hfirst
  rw [densityScore_square] at hfirst
  change densitySquareNorm reference.weight (fun word =>
    PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word / reference.weight word) = _ at hsecond
  rw [densityScore_square] at hsecond
  have hfirst' : profileSquareNorm reference.weight
      (PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar score)) ≤
      16 * pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
    rw [hfirst]
    have htriple := tripleMassAt_energy security attachmentRoot scalar score
    have hcomp := compensatorAt_energy security compensatorRoot
    have hnonnegative := profileSquareNorm_nonneg (uniformReference security).weight
      (compensatorAt security compensatorRoot).weight (uniformReference security).nonneg
    have hinput := (primaryLaw security).l2Sq_nonneg score
    calc
      _ ≤ profileSquareNorm (uniformReference security).weight (compensatorAt security compensatorRoot).weight *
          ((4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_left htriple hnonnegative
      _ ≤ 4 * ((4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_right hcomp (by
          change 0 ≤ (4 * pairBudget security) * (primaryLaw security).l2Sq score
          exact mul_nonneg (mul_nonneg (by norm_num) (pairBudget_nonneg security)) hinput)
      _ = _ := by ring
  have hsecond' : profileSquareNorm reference.weight
      (PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
        (tripleMassAt security attachmentRoot scalar (fun _ => 1))) ≤
      2048 * pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
    rw [hsecond]
    have htriple := tripleMassAt_energy security attachmentRoot scalar (fun _ => 1)
    simp only [one_pow, FiniteDist.expectation_const, mul_one] at htriple
    have hcomp := signedCompensatorAt_energy security compensatorRoot score
    have hnonnegative := profileSquareNorm_nonneg (uniformReference security).weight
      (signedCompensatorAt security compensatorRoot score) (uniformReference security).nonneg
    have hinput := (primaryLaw security).l2Sq_nonneg score
    have ha := activation_le_half security
    calc
      _ ≤ profileSquareNorm (uniformReference security).weight (signedCompensatorAt security compensatorRoot score) *
          (4 * pairBudget security) := mul_le_mul_of_nonneg_left htriple hnonnegative
      _ ≤ (1024 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) *
          (4 * pairBudget security) := mul_le_mul_of_nonneg_right hcomp
            (mul_nonneg (by norm_num) (pairBudget_nonneg security))
      _ = activation security * (4096 * pairBudget security *
          (primaryLaw security).expectation (fun primary => score primary ^ 2)) := by ring
      _ ≤ (1 / 2) * (4096 * pairBudget security *
          (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_right ha (by
          change 0 ≤ 4096 * pairBudget security * (primaryLaw security).l2Sq score
          exact mul_nonneg (mul_nonneg (by norm_num) (pairBudget_nonneg security)) hinput)
      _ = _ := by ring
  have hsum := profileEnergy_sub_le reference.weight
    (PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score))
    (PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1))) reference.nonneg
  change profileSquareNorm reference.weight (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤ _ at hsum
  change profileSquareNorm reference.weight (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤ _
  nlinarith only [hsum, hfirst', hsecond']

theorem paired_degree_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) degree) ≤
        (66048 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := LocalTensors.degreeTensor_energy_le (fun _ : Fin 4 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (pairedMassAt security compensatorRoot attachmentRoot scalar score) degree
  change _ ≤ (2 : ℝ) ^ Fintype.card (Fin 4) * densitySquareNorm
    (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
    (fun word => pairedMassAt security compensatorRoot attachmentRoot scalar score word /
      (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight word) at h
  rw [densityScore_square] at h
  norm_num only [Fintype.card_fin, Nat.reducePow] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (pairedMassAt_energy security compensatorRoot attachmentRoot scalar score)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

theorem compensatorAt_channel (security : ℕ) (root : ℤ) (output : Palette security) :
    (compensatorAt security root).weight output =
      ∑ center, (centerLaw security).weight center * atom (shiftEquiv security root center) output := by
  classical
  rw [compensatorAt, FiniteDist.map_weight]
  simp only [atom, mul_ite, mul_one, mul_zero]

theorem pairedMassAt_control_sum (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (score : Palette security → ℝ) (word : Fin 4 → Palette security) :
    pairedMassAt security compensatorRoot attachmentRoot scalar score word =
      ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center *
        (pairAt security primary scalar).weight (word 1, word 2) *
        (attachmentAt security attachmentRoot scalar).weight (word 3) *
        atom (shiftEquiv security compensatorRoot center) (word 0) := by
  unfold pairedMassAt PhysicalBlockTensors.compensatedTripleMass tripleMassAt
  rw [compensatorAt_channel, signedCompensatorAt_channel]
  unfold signedPairAt
  simp only [mul_one]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  conv_lhs => arg 2; ext center; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  unfold pairedScore
  ring

/-- The positive local channel conditional on the actual two public
controls and the same protected scalar. -/
def controlMass (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : PhysicalSynthesis.Group security) (word : Fin 4 → Palette security) : ℝ :=
  (pairAt security group.1 scalar).weight (word 1, word 2) *
    (attachmentAt security attachmentRoot scalar).weight (word 3) *
    atom (shiftEquiv security compensatorRoot group.2) (word 0)

/-- One actual finite public-control sum, with the true paired channel as
its numerator. Every homogeneous coefficient below is extracted from it. -/
def pairedMassLinear (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    (Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) where
  toFun score word := ∑ group, (PhysicalSynthesis.groupLaw security).weight group *
    PhysicalSynthesis.pairedChannel security score group * controlMass security compensatorRoot attachmentRoot scalar group word
  map_add' first second := by
    funext word
    simp only [map_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' coefficient score := by
    funext word
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro group _
    ring

theorem pairedMassLinear_apply (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (score : Palette security → ℝ) :
    pairedMassLinear security compensatorRoot attachmentRoot scalar score =
      pairedMassAt security compensatorRoot attachmentRoot scalar score := by
  funext word
  rw [pairedMassAt_control_sum]
  simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, PhysicalSynthesis.groupLaw,
    FiniteDist.prod_weight, Fintype.sum_prod_type, PhysicalSynthesis.pairedChannel, controlMass]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  ring

/-- The actual symmetric degree coefficient, as a linear map on an
arbitrary primary input score. Its definition is finite extraction from
the physical four-coordinate mass, not a supplied response matrix. -/
def localDegreeLinear (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (degree : ℕ) : (Palette security → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) (Palette security) :=
  (LocalTensors.degreeTensorLinear (fun _ : Fin 4 => uniformReference security) degree).comp
    (pairedMassLinear security compensatorRoot attachmentRoot scalar)

theorem localDegreeLinear_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (degree : ℕ) (score : Palette security → ℝ) :
    BlockFock.tensorEnergy (localDegreeLinear security compensatorRoot attachmentRoot scalar degree score) ≤
      (66048 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  simp only [localDegreeLinear, LinearMap.comp_apply, LocalTensors.degreeTensorLinear_apply, pairedMassLinear_apply]
  exact paired_degree_energy security compensatorRoot attachmentRoot scalar score degree

def jointPairedMass {Root : Type*} [Fintype Root] (security : ℕ) (source : FiniteDist Root)
    (compensatorRoot attachmentRoot : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Palette security → ℝ) (word : Fin 4 → Palette security) : ℝ :=
  ∑ root, source.weight root * pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) word

theorem jointPaired_degree_energy {Root : Type*} [Fintype Root] (security : ℕ) (source : FiniteDist Root)
    (compensatorRoot attachmentRoot : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Palette security → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (jointPairedMass security source compensatorRoot attachmentRoot scalar score) degree) ≤
        (66048 * pairBudget security) * source.expectation (fun root =>
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hprojection := LocalTensors.degreeTensor_energy_le (fun _ : Fin 4 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (jointPairedMass security source compensatorRoot attachmentRoot scalar score) degree
  change _ ≤ (2 : ℝ) ^ Fintype.card (Fin 4) * densitySquareNorm reference.weight
    (fun word => jointPairedMass security source compensatorRoot attachmentRoot scalar score word / reference.weight word) at hprojection
  rw [densityScore_square] at hprojection
  norm_num only [Fintype.card_fin, Nat.reducePow] at hprojection
  have havg := profileSquareNorm_average_le source reference.weight reference.nonneg
    (fun root => pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root))
  have hbound : (∑ root, source.weight root * profileSquareNorm reference.weight
      (pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root))) ≤
        (4128 * pairBudget security) * source.expectation (fun root =>
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
    calc
      _ ≤ ∑ root, source.weight root * ((4128 * pairBudget security) *
          (primaryLaw security).expectation (fun primary => score root primary ^ 2)) :=
        Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left
          (pairedMassAt_energy security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root)) (source.nonneg root))
      _ = _ := by
        change (∑ root, source.weight root * ((4128 * pairBudget security) *
          (primaryLaw security).expectation (fun primary => score root primary ^ 2))) =
            (4128 * pairBudget security) * ∑ root, source.weight root *
              (primaryLaw security).expectation (fun primary => score root primary ^ 2)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro root _
        ring
  exact hprojection.trans ((mul_le_mul_of_nonneg_left (havg.trans hbound)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

theorem joint_retained_paired_degree_energy {Root Retained : Type*} [Fintype Root] [Fintype Retained]
    (security : ℕ) (source : FiniteDist Root) (retained : FiniteDist Retained)
    (compensatorRoot attachmentRoot : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Retained → Palette security → ℝ) (degree : ℕ) :
    (∑ coordinate, retained.weight coordinate *
      BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
        (jointPairedMass security source compensatorRoot attachmentRoot scalar (fun root => score root coordinate)) degree)) ≤
        (66048 * pairBudget security) * source.expectation (fun root => retained.expectation (fun coordinate =>
          (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) := by
  calc
    _ ≤ ∑ coordinate, retained.weight coordinate * ((66048 * pairBudget security) *
        source.expectation (fun root => (primaryLaw security).expectation (fun primary => score root coordinate primary ^ 2))) :=
      Finset.sum_le_sum (fun coordinate _ => mul_le_mul_of_nonneg_left
        (jointPaired_degree_energy security source compensatorRoot attachmentRoot scalar (fun root => score root coordinate) degree)
        (retained.nonneg coordinate))
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

end CurrentAFT.PairedReferenceEnergy

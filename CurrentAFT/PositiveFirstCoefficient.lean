import CurrentAFT.ReferenceMarginals
import CurrentAFT.PairedReferenceEnergy
import AFT.TripleMarginals

/-!
# Sharp first coefficients of the actual positive local factors

The first coefficient is estimated from its one-coordinate marginals,
not from the much larger full pair density. The resulting square budget
has exponent 31, retaining the half-power needed by the Fourier tail.
-/

namespace CurrentAFT.PositiveFirstCoefficient

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ReferenceMarginals PairedReferenceEnergy
open AFT.PhysicalBlockTensors
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base primaryLaw activation

def meanPairLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (primaryLaw security).mix (fun primary => pairAt security primary scalar)

def meanDiffuseLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (primaryLaw security).mix (fun primary => diffusePairAt security primary scalar)

def meanMarkedCompanion (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix (fun primary => markedCompanionAt security primary scalar)

private theorem map_pair_first {Color : Type*} [Fintype Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    (law.map Prod.fst).weight color = ∑ second, law.weight (color, second) := by
  classical
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type]
  change (∑ first, ∑ second, if first = color then law.weight (first, second) else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem map_pair_second {Color : Type*} [Fintype Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    (law.map Prod.snd).weight color = ∑ first, law.weight (first, color) := by
  classical
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem meanDiffuse_first_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    ((meanDiffuseLaw security scalar).map Prod.fst).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  rw [map_pair_first]
  simp only [meanDiffuseLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_left
        (diffusePairAt_first_height security primary scalar output) ((primaryLaw security).nonneg primary))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem meanDiffuse_second_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    ((meanDiffuseLaw security scalar).map Prod.snd).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  rw [map_pair_second]
  simp only [meanDiffuseLaw, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_left
        (diffusePairAt_second_height security primary scalar output) ((primaryLaw security).nonneg primary))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem meanPair_first (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    ((meanPairLaw security scalar).map Prod.fst).weight output =
      (1 - activation security) * ((meanDiffuseLaw security scalar).map Prod.fst).weight output +
        activation security * (primaryLaw security).weight output := by
  classical
  rw [map_pair_first, map_pair_first]
  simp only [meanPairLaw, meanDiffuseLaw, FiniteDist.mix_weight, pairAt,
    markedPairAt_weight, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    apply Finset.sum_congr rfl
    intro primary _
    ring
  · rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
    ring

theorem meanPair_second (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    ((meanPairLaw security scalar).map Prod.snd).weight output =
      (1 - activation security) * ((meanDiffuseLaw security scalar).map Prod.snd).weight output +
        activation security * (meanMarkedCompanion security scalar).weight output := by
  classical
  rw [map_pair_second, map_pair_second]
  simp only [meanPairLaw, meanDiffuseLaw, meanMarkedCompanion, FiniteDist.mix_weight,
    pairAt, markedPairAt_weight, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro primary _
    ring
  · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro primary _
    ring

private theorem probability_height_energy (security : ℕ) (law : FiniteDist (Palette security))
    (height : ℝ) (hheight : ∀ color, law.weight color ≤ height) :
    profileSquareNorm (uniformReference security).weight law.weight ≤ height * Parameters.modulus security := by
  have hq := FirstResponse.modulus_pos security
  have hheight0 : 0 ≤ height := by
    obtain ⟨color⟩ := (inferInstance : Nonempty (Palette security))
    exact (law.nonneg color).trans (hheight color)
  have h := probability_energy_le_height (uniformReference security) law
    (1 / (Parameters.modulus security : ℝ)) height (by positivity) hheight0
    (fun color => (uniformReference_weight security color).ge) hheight
  exact h.trans_eq (by field_simp)

private theorem profileEnergy_two (security : ℕ) (first second : Palette security → ℝ) (a b : ℝ) :
    profileSquareNorm (uniformReference security).weight (fun color => a * first color + b * second color) ≤
      2 * a ^ 2 * profileSquareNorm (uniformReference security).weight first +
        2 * b ^ 2 * profileSquareNorm (uniformReference security).weight second := by
  simp only [profileSquareNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro color _
  have h : (a * first color + b * second color) ^ 2 ≤ 2 * a ^ 2 * first color ^ 2 + 2 * b ^ 2 * second color ^ 2 := by
    nlinarith [sq_nonneg (a * first color - b * second color)]
  exact (div_le_div_of_nonneg_right h ((uniformReference security).nonneg color)).trans_eq (by ring)

def heightBudget (security : ℕ) : ℝ := activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security

theorem meanPair_first_energy (security : ℕ) (scalar : Scalar security) :
    profileSquareNorm (uniformReference security).weight ((meanPairLaw security scalar).map Prod.fst).weight ≤
      2 * heightBudget security + 4 := by
  have hd := probability_height_energy security ((meanDiffuseLaw security scalar).map Prod.fst)
    (2 / (Parameters.modulus security : ℝ)) (meanDiffuse_first_height security scalar)
  have hq := FirstResponse.modulus_pos security
  have hd' : profileSquareNorm (uniformReference security).weight
      ((meanDiffuseLaw security scalar).map Prod.fst).weight ≤ 2 := hd.trans_eq (by field_simp)
  have hp := probability_height_energy security (primaryLaw security) (primaryMaximum security)
    (GaussianHeights.primaryLaw_upper security)
  have h := profileEnergy_two security ((meanDiffuseLaw security scalar).map Prod.fst).weight
    (primaryLaw security).weight (1 - activation security) (activation security)
  simp_rw [← meanPair_first] at h
  have ha : (1 - activation security) ^ 2 ≤ 1 := by
    have := activation_pos security; have := activation_le_half security; nlinarith
  have hdiff0 := profileSquareNorm_nonneg (uniformReference security).weight
    ((meanDiffuseLaw security scalar).map Prod.fst).weight (uniformReference security).nonneg
  have hdiff := mul_le_mul_of_nonneg_right ha hdiff0
  have hprimary := mul_le_mul_of_nonneg_left hp (sq_nonneg (activation security))
  unfold heightBudget
  nlinarith only [h, hdiff, hd', hprimary]

theorem meanPair_second_energy (security : ℕ) (scalar : Scalar security) :
    profileSquareNorm (uniformReference security).weight ((meanPairLaw security scalar).map Prod.snd).weight ≤
      4 * heightBudget security + 4 := by
  have hd := probability_height_energy security ((meanDiffuseLaw security scalar).map Prod.snd)
    (2 / (Parameters.modulus security : ℝ)) (meanDiffuse_second_height security scalar)
  have hq := FirstResponse.modulus_pos security
  have hd' : profileSquareNorm (uniformReference security).weight
      ((meanDiffuseLaw security scalar).map Prod.snd).weight ≤ 2 := hd.trans_eq (by field_simp)
  have hp := probability_height_energy security (meanMarkedCompanion security scalar) (2 * primaryMaximum security)
    (markedCompanionAt_primary_height security scalar)
  have h := profileEnergy_two security ((meanDiffuseLaw security scalar).map Prod.snd).weight
    (meanMarkedCompanion security scalar).weight (1 - activation security) (activation security)
  simp_rw [← meanPair_second] at h
  have ha : (1 - activation security) ^ 2 ≤ 1 := by
    have := activation_pos security; have := activation_le_half security; nlinarith
  have hdiff0 := profileSquareNorm_nonneg (uniformReference security).weight
    ((meanDiffuseLaw security scalar).map Prod.snd).weight (uniformReference security).nonneg
  have hdiff := mul_le_mul_of_nonneg_right ha hdiff0
  have hprimary := mul_le_mul_of_nonneg_left hp (sq_nonneg (activation security))
  unfold heightBudget
  nlinarith only [h, hdiff, hd', hprimary]

def positiveTripleLaw (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security) :
    FiniteDist (Fin 3 → Palette security) :=
  sharedSourceTriple (primaryLaw security) (fun primary => pairAt security primary scalar)
    (fun _ _ _ => attachmentAt security attachmentRoot scalar)

theorem positiveTriple_first_marginal (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security)
    (output : Palette security) :
    ((positiveTripleLaw security attachmentRoot scalar).map (fun word => word 0)).weight output =
      ((meanPairLaw security scalar).map Prod.fst).weight output := by
  rw [positiveTripleLaw, sharedSourceTriple_first_marginal, map_pair_first]
  rfl

theorem positiveTriple_second_marginal (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security)
    (output : Palette security) :
    ((positiveTripleLaw security attachmentRoot scalar).map (fun word => word 1)).weight output =
      ((meanPairLaw security scalar).map Prod.snd).weight output := by
  rw [positiveTripleLaw, sharedSourceTriple_second_marginal, map_pair_second]
  rfl

theorem positiveTriple_attachment_height (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security)
    (output : Palette security) :
    ((positiveTripleLaw security attachmentRoot scalar).map (fun word => word 2)).weight output ≤
      4 / (Parameters.modulus security : ℝ) := by
  unfold positiveTripleLaw
  apply sharedSourceTriple_body_marginal_le
  intro _ _ _ _
  exact attachmentAt_height security attachmentRoot scalar _

private theorem prod_map_fst {First Second : Type*} [Fintype First] [Fintype Second]
    (first : FiniteDist First) (second : FiniteDist Second) : (first.prod second).map Prod.fst = first := by
  classical
  apply FiniteDist.ext
  intro color
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  change (∑ a, ∑ b, if a = color then first.weight a * second.weight b else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.mul_sum, second.sum_one, mul_one]

private theorem prod_map_snd {First Second : Type*} [Fintype First] [Fintype Second]
    (first : FiniteDist First) (second : FiniteDist Second) : (first.prod second).map Prod.snd = second := by
  classical
  apply FiniteDist.ext
  intro color
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  change (∑ a, ∑ b, if b = color then first.weight a * second.weight b else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, first.sum_one, one_mul]

private theorem prod_map_snd_function {First Second Output : Type*}
    [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (f : Second → Output) :
    (first.prod second).map (fun pair => f pair.2) = second.map f := by
  calc
    _ = ((first.prod second).map Prod.snd).map f := (FiniteDist.map_map _ _ _).symm
    _ = _ := by rw [prod_map_snd]

def positiveFourLaw (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    FiniteDist (Fin 4 → Palette security) :=
  ((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map
    (fun draw => Fin.cons draw.1 draw.2)

theorem positiveFour_compensator_marginal (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) :
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).map (fun word => word 0) =
      compensatorAt security compensatorRoot := by
  rw [positiveFourLaw, FiniteDist.map_map]
  change ((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map Prod.fst = _
  exact prod_map_fst _ _

theorem positiveFour_succ_marginal (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (index : Fin 3) :
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).map (fun word => word index.succ) =
      (positiveTripleLaw security attachmentRoot scalar).map (fun word => word index) := by
  rw [positiveFourLaw, FiniteDist.map_map]
  change ((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map
    (fun draw => draw.2 index) = _
  exact prod_map_snd_function (compensatorAt security compensatorRoot)
    (positiveTripleLaw security attachmentRoot scalar) (fun word : Fin 3 → Palette security => word index)

private theorem centered_energy_bound (security : ℕ) (law : FiniteDist (Palette security)) (bound : ℝ)
    (hbound : profileSquareNorm (uniformReference security).weight law.weight ≤ bound) :
    profileSquareNorm (uniformReference security).weight
      (fun color => law.weight color - (uniformReference security).weight color) ≤ 2 * bound + 2 := by
  have h := centered_probability_energy_le (uniformReference security) law
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
  linarith

theorem positiveTriple_first_energy (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (positiveTripleLaw security attachmentRoot scalar).weight 1) ≤ 96 * heightBudget security + 240 := by
  let law := positiveTripleLaw security attachmentRoot scalar
  have h0 := centered_energy_bound security (law.map (fun word => word 0))
    (2 * heightBudget security + 4) (by
      simp_rw [show (law.map (fun word => word 0)).weight = ((meanPairLaw security scalar).map Prod.fst).weight by
        funext output; exact positiveTriple_first_marginal security attachmentRoot scalar output]
      exact meanPair_first_energy security scalar)
  have h1 := centered_energy_bound security (law.map (fun word => word 1))
    (4 * heightBudget security + 4) (by
      simp_rw [show (law.map (fun word => word 1)).weight = ((meanPairLaw security scalar).map Prod.snd).weight by
        funext output; exact positiveTriple_second_marginal security attachmentRoot scalar output]
      exact meanPair_second_energy security scalar)
  have h2 := centered_energy_bound security (law.map (fun word => word 2)) 4 (by
    exact (probability_height_energy security _ (4 / (Parameters.modulus security : ℝ))
      (positiveTriple_attachment_height security attachmentRoot scalar)).trans_eq (by
        field_simp [(FirstResponse.modulus_pos security).ne']))
  have h := LocalTensors.first_degree_energy_le (fun _ : Fin 3 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security)) law
  norm_num only [Fintype.card_fin, Nat.reducePow] at h
  rw [Fin.sum_univ_three] at h
  linarith

theorem positiveFour_first_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight 1) ≤ 192 * heightBudget security + 640 := by
  let law := positiveFourLaw security compensatorRoot attachmentRoot scalar
  have h0 := centered_energy_bound security (law.map (fun word => word 0)) 4 (by
    rw [positiveFour_compensator_marginal]
    exact compensatorAt_energy security compensatorRoot)
  have h1 := centered_energy_bound security (law.map (fun word => word 1))
    (2 * heightBudget security + 4) (by
      rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl, positiveFour_succ_marginal]
      simp_rw [show ((positiveTripleLaw security attachmentRoot scalar).map (fun word => word 0)).weight =
          ((meanPairLaw security scalar).map Prod.fst).weight by
        funext output; exact positiveTriple_first_marginal security attachmentRoot scalar output]
      exact meanPair_first_energy security scalar)
  have h2 := centered_energy_bound security (law.map (fun word => word 2))
    (4 * heightBudget security + 4) (by
      rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl, positiveFour_succ_marginal]
      simp_rw [show ((positiveTripleLaw security attachmentRoot scalar).map (fun word => word 1)).weight =
          ((meanPairLaw security scalar).map Prod.snd).weight by
        funext output; exact positiveTriple_second_marginal security attachmentRoot scalar output]
      exact meanPair_second_energy security scalar)
  have h3 := centered_energy_bound security (law.map (fun word => word 3)) 4 (by
    rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl, positiveFour_succ_marginal]
    exact (probability_height_energy security _ (4 / (Parameters.modulus security : ℝ))
      (positiveTriple_attachment_height security attachmentRoot scalar)).trans_eq (by
        field_simp [(FirstResponse.modulus_pos security).ne']))
  have h := LocalTensors.first_degree_energy_le (fun _ : Fin 4 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security)) law
  norm_num only [Fintype.card_fin, Nat.reducePow] at h
  rw [Fin.sum_univ_four] at h
  linarith

theorem positiveFour_first_polynomial (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight 1) ≤
        (640 + 12583104 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by
  have h := positiveFour_first_energy security compensatorRoot attachmentRoot scalar
  have hmax := activated_primaryMaximum security
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hp : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 31 := one_le_pow₀ hb
  change heightBudget security ≤ _ at hmax
  nlinarith only [h, hmax, hp]

theorem positiveTriple_first_polynomial (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (positiveTripleLaw security attachmentRoot scalar).weight 1) ≤
        (240 + 6291552 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by
  have h := positiveTriple_first_energy security attachmentRoot scalar
  have hmax := activated_primaryMaximum security
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hp : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 31 := one_le_pow₀ hb
  change heightBudget security ≤ _ at hmax
  nlinarith only [h, hmax, hp]

theorem positiveTriple_weight (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security)
    (word : Fin 3 → Palette security) :
    (positiveTripleLaw security attachmentRoot scalar).weight word =
      tripleMass (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word := by
  rw [positiveTripleLaw, sharedSourceTriple_weight]
  unfold tripleMass BlockDensity.attachedMass tripleMassAt signedPairAt
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro primary _
  ring

def consEquiv (Color : Type*) : (Color × (Fin 3 → Color)) ≃ (Fin 4 → Color) where
  toFun draw := Fin.cons draw.1 draw.2
  invFun word := (word 0, Fin.tail word)
  left_inv draw := by cases draw; rfl
  right_inv word := by ext index; fin_cases index <;> rfl

theorem positiveFour_weight (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (word : Fin 4 → Palette security) :
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word := by
  change (((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map
    (consEquiv (Palette security))).weight word = _
  rw [FiniteDist.map_equiv_weight]
  change (compensatorAt security compensatorRoot).weight (word 0) *
    (positiveTripleLaw security attachmentRoot scalar).weight (Fin.tail word) = _
  rw [positiveTriple_weight]
  rfl

theorem positiveTriple_degree_energy (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (positiveTripleLaw security attachmentRoot scalar).weight degree) ≤ 32 * pairBudget security := by
  have hmass : (positiveTripleLaw security attachmentRoot scalar).weight =
      tripleMass (tripleMassAt security attachmentRoot scalar (fun _ => 1)) :=
    funext (positiveTriple_weight security attachmentRoot scalar)
  rw [hmass]
  have h := triple_degree_energy security attachmentRoot scalar (fun _ => 1) degree
  simpa only [one_pow, FiniteDist.expectation_const, mul_one] using h

theorem positiveFour_degree_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight degree) ≤ 256 * pairBudget security := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hmass : (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight =
      compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar (fun _ => 1)) :=
    funext (positiveFour_weight security compensatorRoot attachmentRoot scalar)
  have hfactor := compensated_triple_density_energy (uniformReference security)
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1))
  change densitySquareNorm reference.weight (fun word => compensatedTripleMass
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word /
      reference.weight word) = _ at hfactor
  rw [densityScore_square] at hfactor
  have hfull : profileSquareNorm reference.weight (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight ≤
      16 * pairBudget security := by
    rw [hmass, hfactor]
    have hcomp := compensatorAt_energy security compensatorRoot
    have htriple := tripleMassAt_energy security attachmentRoot scalar (fun _ => 1)
    simp only [one_pow, FiniteDist.expectation_const, mul_one] at htriple
    have hnonneg := profileSquareNorm_nonneg (uniformReference security).weight
      (compensatorAt security compensatorRoot).weight (uniformReference security).nonneg
    calc
      _ ≤ profileSquareNorm (uniformReference security).weight (compensatorAt security compensatorRoot).weight *
          (4 * pairBudget security) := mul_le_mul_of_nonneg_left htriple hnonneg
      _ ≤ 4 * (4 * pairBudget security) := mul_le_mul_of_nonneg_right hcomp
        (mul_nonneg (by norm_num) (pairBudget_nonneg security))
      _ = _ := by ring
  have h := LocalTensors.degreeTensor_energy_le (fun _ : Fin 4 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight degree
  change _ ≤ (2 : ℝ) ^ Fintype.card (Fin 4) * densitySquareNorm reference.weight (fun word =>
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word / reference.weight word) at h
  rw [densityScore_square] at h
  norm_num only [Fintype.card_fin, Nat.reducePow] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end

end CurrentAFT.PositiveFirstCoefficient

import CurrentAFT.FixedPairedFirst
import CurrentAFT.PhysicalFockRates
import AFT.SingletonFock
import AFT.JointPhysicalFock

/-!
# Complete current paired local Fock response

The sharp first coefficient and all higher coefficients are extracted from
the same actual four-output signed mass. The normalization always uses the
full current output population, including its square-root denominator.
-/

namespace CurrentAFT.TaggedPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst
  PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount BackgroundRates.radius
  ProposalPrimary.primaryLaw

/-- A finite four-output estimate retaining the exact sharp first scale.
Only degrees two through four use the larger whole-density estimate. -/
theorem fourOutput_energy_le {Color : Type*} [Fintype Color]
    (reference : FiniteDist Color) (population : ℕ) (radius : ℝ)
    (mass : (Fin 4 → Color) → ℝ) (hmass : ∑ word, mass word = 0)
    (first higher input : ℝ) (_hhigher : 0 ≤ higher) (_hinput : 0 ≤ input)
    (hscale0 : 0 ≤ radius / Real.sqrt population) (hscale1 : radius / Real.sqrt population ≤ 1)
    (hfirst : BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => reference) mass 1) ≤ first * input)
    (hdegree : ∀ degree, 2 ≤ degree → degree ≤ 4 →
      BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => reference) mass degree) ≤ higher * input) :
    BlockProducts.taggedCoefficientEnergy reference mass population radius ≤
      (10 * (radius / Real.sqrt population) ^ 2 * first +
        2200 * (radius / Real.sqrt population) ^ 4 * higher) * input := by
  let scale := radius / Real.sqrt population
  let energy := fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => reference) mass degree)
  have hz : energy 0 = 0 := by
    unfold energy BlockFock.tensorEnergy
    simp only [LocalTensors.degreeTensor_zero_formula, hmass,
      zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero]
  have hidentity : BlockProducts.taggedCoefficientEnergy reference mass population radius =
      10 * scale ^ 2 * energy 1 + 40 * scale ^ 4 * energy 2 +
        240 * scale ^ 6 * energy 3 + 1920 * scale ^ 8 * energy 4 := by
    unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor
    simp only [TensorFock.tensorEnergy_smul, Fintype.card_fin, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, zero_add]
    norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat,
      Nat.cast_one, Nat.cast_zero, one_mul, pow_one, Nat.reducePow]
    change 5 * (energy 0 + 2 * (scale ^ 2 * energy 1) +
      8 * ((scale ^ 2) ^ 2 * energy 2) + 48 * ((scale ^ 3) ^ 2 * energy 3) +
      384 * ((scale ^ 4) ^ 2 * energy 4)) = _
    rw [hz]
    dsimp only [scale]
    ring
  have hs6 : scale ^ 6 ≤ scale ^ 4 := pow_le_pow_of_le_one hscale0 hscale1 (by omega : 4 ≤ 6)
  have hs8 : scale ^ 8 ≤ scale ^ 4 := pow_le_pow_of_le_one hscale0 hscale1 (by omega : 4 ≤ 8)
  have h2 := hdegree 2 (by omega) (by omega)
  have h3 := hdegree 3 (by omega) (by omega)
  have h4 := hdegree 4 (by omega) (by omega)
  have hepos (degree : ℕ) : 0 ≤ energy degree := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [hidentity]
  calc
    _ ≤ 10 * scale ^ 2 * (first * input) + 40 * scale ^ 4 * (higher * input) +
        240 * scale ^ 4 * (higher * input) + 1920 * scale ^ 4 * (higher * input) := by
      gcongr <;> exact hepos _
    _ = _ := by dsimp only [scale]; ring

def firstConstant : ℝ := 16 + 1310740 * Real.exp Real.pi
def higherConstant : ℝ := 66048 * (524288 + 17180131328 * Real.exp Real.pi)

theorem firstConstant_nonneg : 0 ≤ firstConstant := by unfold firstConstant; positivity
theorem higherConstant_nonneg : 0 ≤ higherConstant := by unfold higherConstant; positivity

/-- Actual fixed-root, fixed-scalar local mass; its whole finite Fock
energy has the sharp first-degree scale, with no full-Fock premise. -/
theorem fixedPaired_energy_le (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) (radius : ℝ)
    (hradius0 : 0 ≤ radius / Real.sqrt (Parameters.dimension security : ℝ))
    (hradius1 : radius / Real.sqrt (Parameters.dimension security : ℝ) ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) (Parameters.dimension security) radius ≤
      (10 * (radius / Real.sqrt (Parameters.dimension security : ℝ)) ^ 2 *
        (firstConstant * (Parameters.base security : ℝ) ^ 31) +
      2200 * (radius / Real.sqrt (Parameters.dimension security : ℝ)) ^ 4 *
        (higherConstant * (Parameters.base security : ℝ) ^ 47)) *
          (primaryLaw security).l2Sq score := by
  apply fourOutput_energy_le
    (uniformReference security) (Parameters.dimension security) radius _
    (by rw [fixedMass_sum, hcentered, mul_zero])
    (firstConstant * (Parameters.base security : ℝ) ^ 31)
    (higherConstant * (Parameters.base security : ℝ) ^ 47)
    ((primaryLaw security).l2Sq score) (by have := higherConstant_nonneg; positivity)
    ((primaryLaw security).l2Sq_nonneg score) hradius0 hradius1
    (fixedPaired_first_polynomial security compensatorRoot attachmentRoot scalar score hcentered)
  intro degree _ _
  have h := paired_degree_energy security compensatorRoot attachmentRoot scalar score degree
  have hbudget := mul_le_mul_of_nonneg_left (pairBudget_polynomial security) (by norm_num : (0 : ℝ) ≤ 66048)
  have hbudget' : 66048 * pairBudget security ≤ higherConstant * (Parameters.base security : ℝ) ^ 47 :=
    hbudget.trans_eq (by unfold higherConstant; ring)
  exact h.trans (mul_le_mul_of_nonneg_right hbudget' ((primaryLaw security).l2Sq_nonneg score))

def pairedConstant (multiple : ℝ) : ℝ :=
  10 * firstConstant * multiple ^ 2 + 2200 * higherConstant * multiple ^ 4

theorem pairedConstant_nonneg (multiple : ℝ) : 0 ≤ pairedConstant multiple := by
  unfold pairedConstant
  have := firstConstant_nonneg
  have := higherConstant_nonneg
  positivity

theorem fixedPaired_normalized_energy_le (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : FirstHistogram.Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) (multiple : ℝ) (hmultiple : 0 ≤ multiple)
    (hscale : normalizedScale security multiple ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) (Parameters.dimension security)
        (multiple * BackgroundRates.radius security) ≤
      (pairedConstant multiple / (Parameters.legCount security : ℝ)) * (primaryLaw security).l2Sq score := by
  have hlegs : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos (FirstResponse.base_pos security) _
  have h := fixedPaired_energy_le security compensatorRoot attachmentRoot scalar score hcentered
    (multiple * BackgroundRates.radius security) (normalizedScale_nonneg security multiple hmultiple) hscale
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ ((primaryLaw security).l2Sq_nonneg score)
  apply (le_div_iff₀ hlegs).mpr
  have hfirst := mul_le_mul_of_nonneg_left (primary_first_scale_le security multiple)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) firstConstant_nonneg)
  have hhigher := mul_le_mul_of_nonneg_left (primary_higher_scale_le security multiple hmultiple)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2200) higherConstant_nonneg)
  change (10 * normalizedScale security multiple ^ 2 * (firstConstant * (Parameters.base security : ℝ) ^ 31) +
    2200 * normalizedScale security multiple ^ 4 * (higherConstant * (Parameters.base security : ℝ) ^ 47)) *
      (Parameters.legCount security : ℝ) ≤ pairedConstant multiple
  unfold pairedConstant
  nlinarith only [hfirst, hhigher]

/-- Finite probability averaging contracts the entire marked coefficient
energy of arbitrary signed masses, all degrees at once. -/
theorem taggedEnergy_average_le {Choice Slot Color : Type*} [Fintype Choice]
    [Fintype Slot] [Fintype Color] (source : FiniteDist Choice) (reference : FiniteDist Color)
    (mass : Choice → (Slot → Color) → ℝ) (population : ℕ) (radius : ℝ) :
    BlockProducts.taggedCoefficientEnergy reference (∑ choice, source.weight choice • mass choice) population radius ≤
      source.expectation (fun choice => BlockProducts.taggedCoefficientEnergy reference (mass choice) population radius) := by
  rw [← LocalTensors.finiteFockChannel_energy]
  have hlinear : LocalTensors.finiteFockChannel reference population radius
      (∑ choice, source.weight choice • mass choice) =
      ∑ choice, source.weight choice • LocalTensors.finiteFockChannel reference population radius (mass choice) := by
    rw [map_sum]
    simp only [map_smul]
  rw [hlinear]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ coordinate, ∑ choice, source.weight choice *
        LocalTensors.finiteFockChannel reference population radius (mass choice) coordinate ^ 2 :=
      Finset.sum_le_sum (fun coordinate _ => BlockFock.mean_square_le source _)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, LocalTensors.finiteFockChannel_energy]
      rfl

/-- The protected second scalar is averaged inside the same four-output
channel, so its pair and attachment are never independently resampled. -/
def averagedPairedChannel (security : ℕ) (compensatorRoot attachmentRoot : ℤ) :
    (FirstHistogram.Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → FirstHistogram.Palette security) → ℝ) :=
  ∑ scalar, (scalarLaw security).weight scalar •
    pairedMassLinear security compensatorRoot attachmentRoot scalar

theorem averagedPairedChannel_apply (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : FirstHistogram.Palette security → ℝ) :
    averagedPairedChannel security compensatorRoot attachmentRoot score =
      ∑ scalar, (scalarLaw security).weight scalar •
        pairedMassAt security compensatorRoot attachmentRoot scalar score := by
  simp only [averagedPairedChannel, LinearMap.sum_apply, LinearMap.smul_apply, pairedMassLinear_apply]

theorem averagedPaired_energy_le (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : FirstHistogram.Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0)
    (multiple : ℝ) (hmultiple : 0 ≤ multiple) (hscale : normalizedScale security multiple ≤ 1) :
    BlockProducts.taggedCoefficientEnergy (uniformReference security)
      (averagedPairedChannel security compensatorRoot attachmentRoot score) (Parameters.dimension security)
        (multiple * BackgroundRates.radius security) ≤
      (pairedConstant multiple / (Parameters.legCount security : ℝ)) * (primaryLaw security).l2Sq score := by
  rw [averagedPairedChannel_apply]
  apply (taggedEnergy_average_le (scalarLaw security) (uniformReference security) _ _ _).trans
  calc
    _ ≤ (scalarLaw security).expectation (fun _ =>
        (pairedConstant multiple / (Parameters.legCount security : ℝ)) * (primaryLaw security).l2Sq score) :=
      Finset.sum_le_sum (fun scalar _ => mul_le_mul_of_nonneg_left
        (fixedPaired_normalized_energy_le security compensatorRoot attachmentRoot scalar score hcentered multiple hmultiple hscale)
        ((scalarLaw security).nonneg scalar))
    _ = _ := FiniteDist.expectation_const _ _

end

end CurrentAFT.TaggedPhysicalFock

import CurrentAFT.ActualControls
import AFT.ChannelCentering

/-!
# The complete paired synthesis on joint kernels

The local signed channel is the actual primary/compensator score. Its tensor
power acts on an arbitrary joint density kernel. The tensor Hilbert bound
is obtained from the proved actual local laws, and does not assume that the
kernel is a product of one-coordinate functions.
-/

namespace CurrentAFT.PhysicalSynthesis

open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) :=
  Classical.decEq _

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
  primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Group (security : ℕ) := Palette security × Palette security

private theorem expectation_cons_any {Color : Type*} [Fintype Color]
    (count : ℕ) [headDecision : DecidableEq (Fin (count + 1))]
    [tailDecision : DecidableEq (Fin count)]
    (law : Fin (count + 1) → FiniteDist Color)
    (value : (Fin (count + 1) → Color) → ℝ) :
    (FiniteDist.independent law).expectation value =
      (law 0).expectation (fun first =>
        (FiniteDist.independent (fun index : Fin count => law index.succ)).expectation
          (fun rest => value (Fin.cons first rest))) := by
  cases Subsingleton.elim headDecision (instDecidableEqFin (count + 1))
  cases Subsingleton.elim tailDecision (instDecidableEqFin count)
  exact FiniteConcentration.expectation_cons count law value

private theorem tensor_energy_any {Input Output : Type*} [Fintype Input] [Fintype Output]
    (count : ℕ) [decision : DecidableEq (Fin count)]
    (input : Fin count → FiniteDist Input) (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index score, (output index).l2Sq (channel index score) ≤
      bound index ^ 2 * (input index).l2Sq score)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (TensorChannel.apply count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  cases Subsingleton.elim decision (instDecidableEqFin count)
  exact TensorChannel.energy_le count input output channel bound hchannel kernel

def groupLaw (security : ℕ) : FiniteDist (Group security) :=
  (primaryLaw security).prod (centerLaw security)

/-- The same coefficient function enters the marked primary and its
compensator. The latter is integrated against the actual inward anchor. -/
def pairedChannel (security : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score := fun group => pairedScore security score group.1 group.2
  map_add' first second := by
    funext group
    simp only [pairedScore, compensatorScore, anchorWeightedScore, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, add_div]
    ring
  map_smul' scalar score := by
    funext group
    simp only [pairedScore, compensatorScore, anchorWeightedScore, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    have hsum : (∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight group.2 *
        (primaryLaw security).weight color * (scalar * score color)) =
        scalar * ∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight group.2 *
          (primaryLaw security).weight color * score color := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    rw [hsum]
    ring

theorem compensator_square_mean (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center ^ 2) =
      activation security ^ 2 * profileSquareNorm (centerLaw security).weight
        (anchorWeightedScore security score) := by
  calc
    _ = activation security ^ 2 * densitySquareNorm (centerLaw security).weight
        (fun center => anchorWeightedScore security score center / (centerLaw security).weight center) := by
      unfold densitySquareNorm compensatorScore
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = _ := by rw [densityScore_square]

/-- A uniform bound on all scores permits tensorization before imposing
canonical centering. The sharper canonical local bound is 129. -/
theorem pairedChannel_energy_le (security : ℕ) (score : Palette security → ℝ) :
    (groupLaw security).l2Sq (pairedChannel security score) ≤
      258 * (primaryLaw security).l2Sq score := by
  have hpoint (primary center : Palette security) :
      pairedScore security score primary center ^ 2 ≤
        2 * score primary ^ 2 + 2 * compensatorScore security score center ^ 2 := by
    unfold pairedScore
    nlinarith [sq_nonneg (score primary + compensatorScore security score center)]
  have hsum : (groupLaw security).l2Sq (pairedChannel security score) ≤
      2 * (primaryLaw security).l2Sq score +
        2 * ∑ center, (centerLaw security).weight center * compensatorScore security score center ^ 2 := by
    calc
      _ ≤ ∑ primary, ∑ center, (primaryLaw security).weight primary *
          (centerLaw security).weight center *
            (2 * score primary ^ 2 + 2 * compensatorScore security score center ^ 2) := by
        unfold FiniteDist.l2Sq FiniteDist.expectation groupLaw
        simp only [FiniteDist.prod_weight, Fintype.sum_prod_type, pairedChannel]
        apply Finset.sum_le_sum
        intro primary _
        apply Finset.sum_le_sum
        intro center _
        exact mul_le_mul_of_nonneg_left (hpoint primary center)
          (mul_nonneg ((primaryLaw security).nonneg primary) ((centerLaw security).nonneg center))
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [show (∑ primary, ∑ center, (primaryLaw security).weight primary *
            (centerLaw security).weight center * (2 * score primary ^ 2)) =
            2 * (primaryLaw security).l2Sq score by
          simp only [FiniteDist.l2Sq, FiniteDist.expectation]
          simp_rw [show ∀ primary center, (primaryLaw security).weight primary *
              (centerLaw security).weight center * (2 * score primary ^ 2) =
              2 * ((primaryLaw security).weight primary * score primary ^ 2) *
                (centerLaw security).weight center by intros; ring]
          simp_rw [← Finset.mul_sum, FiniteDist.sum_one, mul_one]
          rw [Finset.mul_sum]]
        congr 1
        rw [Finset.sum_comm]
        simp_rw [show ∀ primary center, (primaryLaw security).weight primary *
            (centerLaw security).weight center * (2 * compensatorScore security score center ^ 2) =
            (2 * ((centerLaw security).weight center * compensatorScore security score center ^ 2)) *
              (primaryLaw security).weight primary by intros; ring]
        simp_rw [← Finset.mul_sum, FiniteDist.sum_one, mul_one]
        rw [Finset.mul_sum]
  rw [compensator_square_mean] at hsum
  have hcomp := compensator_energy_le security score
  have hin : 0 ≤ (primaryLaw security).l2Sq score :=
    by
      unfold FiniteDist.l2Sq FiniteDist.expectation
      exact Finset.sum_nonneg (fun color _ =>
        mul_nonneg ((primaryLaw security).nonneg color) (sq_nonneg _))
  have ha := mul_le_mul_of_nonneg_right (activation_le_half security) hin
  change _ ≤ 258 * ∑ color, (primaryLaw security).weight color * score color ^ 2
  change 0 ≤ ∑ color, (primaryLaw security).weight color * score color ^ 2 at hin
  change activation security * (∑ color, (primaryLaw security).weight color * score color ^ 2) ≤
    (1 / 2) * (∑ color, (primaryLaw security).weight color * score color ^ 2) at ha
  change _ ≤ 2 * (∑ color, (primaryLaw security).weight color * score color ^ 2) + _ at hsum
  nlinarith only [hsum, hcomp, ha]

theorem pairedChannel_mean (security : ℕ) (score : Palette security → ℝ) :
    (groupLaw security).expectation (pairedChannel security score) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have hrow (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center) =
        (primaryLaw security).weight primary * score primary -
          (primaryLaw security).weight primary *
            ∑ center, (centerLaw security).weight center * compensatorScore security score center := by
    unfold pairedScore
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ center, (primaryLaw security).weight primary *
          (centerLaw security).weight center * score primary) =
          (primaryLaw security).weight primary * score primary *
            ∑ center, (centerLaw security).weight center by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
      rw [FiniteDist.sum_one, mul_one]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
  change (∑ group, (groupLaw security).weight group * pairedChannel security score group) = _
  simp only [groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type, pairedChannel,
    LinearMap.coe_mk, AddHom.coe_mk, hrow, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul, compensatorScore_mass]
  unfold FiniteDist.expectation
  ring

/-- Finite tensor mean identity for arbitrary joint kernels and actual
local linear channels. Each local mean multiplier is retained. -/
theorem tensor_mean {Input Output : Type*} [Fintype Input] [Fintype Output]
    (count : ℕ) (input : Fin count → FiniteDist Input)
    (output : Fin count → FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (multiplier : Fin count → ℝ)
    (hmean : ∀ index score, (output index).expectation (channel index score) =
      multiplier index * (input index).expectation score)
    (kernel : (Fin count → Input) → ℝ) :
    (FiniteDist.independent output).expectation (TensorChannel.apply count channel kernel) =
      (∏ index, multiplier index) * (FiniteDist.independent input).expectation kernel := by
  induction count with
  | zero =>
    have hkernel : kernel = fun _ => kernel Fin.elim0 := by
      funext word
      congr 1
      exact Subsingleton.elim _ _
    rw [hkernel]
    simp only [TensorChannel.apply, Fin.prod_univ_zero, FiniteDist.expectation_const, one_mul]
  | succ count ih =>
    rw [expectation_cons_any]
    simp only [TensorChannel.apply_cons]
    rw [FiniteDist.expectation_comm]
    simp_rw [hmean]
    rw [FiniteDist.expectation_const_mul, FiniteDist.expectation_comm]
    simp_rw [ih (fun index => input index.succ) (fun index => output index.succ)
      (fun index => channel index.succ) (fun index => multiplier index.succ)
      (fun index => hmean index.succ)]
    rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ,
      expectation_cons_any, mul_assoc]

/-- The physical lift applies this actual channel in every primary slot,
while retaining the entire body tuple as a parameter. -/
def pairedKernel (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := Palette security)
      (Body := ActualControls.SafePalette security) r s)
    (groups : Fin r → Group security) (centers : Fin s → ActualControls.SafePalette security) : ℝ :=
  TensorChannel.apply r (fun _ => pairedChannel security) (fun colors => kernel colors centers) groups

theorem pairedKernel_energy_le (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := Palette security)
      (Body := ActualControls.SafePalette security) r s)
    (centers : Fin s → ActualControls.SafePalette security) :
    (FiniteDist.independent (fun _ : Fin r => groupLaw security)).l2Sq
      (fun groups => pairedKernel security r s kernel groups centers) ≤
        258 ^ r * (FiniteDist.independent (fun _ : Fin r => primaryLaw security)).l2Sq
          (fun colors => kernel colors centers) := by
  have hlocal (index : Fin r) (score : Palette security → ℝ) :
      (groupLaw security).l2Sq (pairedChannel security score) ≤
        Real.sqrt 258 ^ 2 * (primaryLaw security).l2Sq score := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 258)]
    exact pairedChannel_energy_le security score
  have h := tensor_energy_any r (fun _ => primaryLaw security) (fun _ => groupLaw security)
    (fun _ => pairedChannel security) (fun _ => Real.sqrt 258) hlocal (fun colors => kernel colors centers)
  simpa only [pairedKernel, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 258),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem pairedKernel_mean (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := Palette security)
      (Body := ActualControls.SafePalette security) r s) :
    ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (pairedKernel security r s kernel) =
        (1 - activation security) ^ r *
          ControlCoordinates.kernelMean (primaryLaw security) (ActualControls.bodyReference security) kernel := by
  rw [ControlCoordinates.kernelMean_iterated_reverse,
    ControlCoordinates.kernelMean_iterated_reverse]
  have hpoint (centers : Fin s → ActualControls.SafePalette security) :
      (FiniteDist.independent (fun _ : Fin r => groupLaw security)).expectation
        (fun groups => pairedKernel security r s kernel groups centers) =
        (1 - activation security) ^ r *
          (FiniteDist.independent (fun _ : Fin r => primaryLaw security)).expectation
            (fun colors => kernel colors centers) := by
    have h := tensor_mean r (fun _ => primaryLaw security) (fun _ => groupLaw security)
      (fun _ => pairedChannel security) (fun _ => 1 - activation security)
      (fun _ => pairedChannel_mean security) (fun colors => kernel colors centers)
    simpa only [pairedKernel, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  simp only [FiniteDist.expectation, FiniteDist.independent] at hpoint ⊢
  simp_rw [hpoint]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro centers _
  ring

theorem pairedCanonicalKernel_mean_zero (security r s : ℕ)
    (kernel : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s) (hdegree : 0 < r + s) :
    ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (pairedKernel security r s kernel.val) = 0 := by
  rw [pairedKernel_mean, ControlCoordinates.canonicalKernel_mean_zero _ _ kernel hdegree, mul_zero]

theorem twoPoolUStatistic_mean_of_zero {Primary Body : Type*}
    [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : ControlCoordinates.DensityKernel
      (Primary := Primary) (Body := Body) r s)
    (hmean : ControlCoordinates.kernelMean primary body kernel = 0)
    (primaryPool bodyPool : ℕ) :
    ControlCoordinates.kernelMean primary body
      (ControlCoordinates.twoPoolUStatistic primaryPool bodyPool kernel) = 0 := by
  let law := (FiniteDist.independent (fun _ : Fin primaryPool => primary)).prod
    (FiniteDist.independent (fun _ : Fin bodyPool => body))
  have hplaced (selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool)) :
      law.expectation (fun inputs => kernel (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2)) = 0 := by
    simpa only [ControlCoordinates.kernelMean, law, FiniteDist.expectation,
      FiniteDist.independent, FiniteDist.prod_weight] using
        (ControlCoordinates.placedKernel_mean primary body kernel selection.1 selection.2).trans hmean
  change law.expectation (fun inputs => (∑ selection :
    (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
      kernel (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2)) /
        ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ))) = 0
  have hdivide (function : ((Fin primaryPool → Primary) × (Fin bodyPool → Body)) → ℝ)
      (denominator : ℝ) :
      law.expectation (fun inputs => function inputs / denominator) =
        law.expectation function / denominator := by
    simp only [FiniteDist.expectation, mul_div_assoc, Finset.sum_div]
  rw [hdivide]
  have hsum : law.expectation (fun inputs => ∑ selection :
      (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
        kernel (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2)) =
      ∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
        law.expectation (fun inputs => kernel (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2)) := by
    unfold FiniteDist.expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp only [hplaced, Finset.sum_const_zero, zero_div]

/-- Actual paired synthesis at fixed public placement. Both pools are
averaged over distinct groups, with their separate falling factorials. -/
def coefficientWeight (security order primaryPool bodyPool : ℕ)
    (coefficient : ActualControls.Coefficients security order)
    (groups : Fin primaryPool → Group security)
    (centers : Fin bodyPool → ActualControls.SafePalette security) : ℝ :=
  coefficient.1 + ∑ arity : ControlCoordinates.PositiveArity order,
    ControlCoordinates.twoPoolUStatistic primaryPool bodyPool
      (pairedKernel security arity.val.1.val arity.val.2.val (coefficient.2 arity).val) groups centers

theorem coefficientWeight_mean (security order primaryPool bodyPool : ℕ)
    (coefficient : ActualControls.Coefficients security order) :
    ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (coefficientWeight security order primaryPool bodyPool coefficient) = coefficient.1 := by
  let law := (FiniteDist.independent (fun _ : Fin primaryPool => groupLaw security)).prod
    (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security))
  have hterm (arity : ControlCoordinates.PositiveArity order) :
      law.expectation (fun inputs =>
        ControlCoordinates.twoPoolUStatistic primaryPool bodyPool
          (pairedKernel security arity.val.1.val arity.val.2.val (coefficient.2 arity).val)
          inputs.1 inputs.2) = 0 := by
    have h := twoPoolUStatistic_mean_of_zero (groupLaw security) (ActualControls.bodyReference security)
      _ (pairedCanonicalKernel_mean_zero security _ _ (coefficient.2 arity)
        (by have := arity.property.1; omega)) primaryPool bodyPool
    simpa only [ControlCoordinates.kernelMean, law, FiniteDist.expectation,
      FiniteDist.independent, FiniteDist.prod_weight] using h
  unfold ControlCoordinates.kernelMean coefficientWeight
  simp only [FiniteDist.expectation, FiniteDist.independent, FiniteDist.prod_weight]
  simp only [FiniteDist.expectation, FiniteDist.independent, FiniteDist.prod_weight, law] at hterm
  simp only [mul_add, Finset.sum_add_distrib]
  have hconstant : (∑ inputs : (Fin primaryPool → Group security) ×
      (Fin bodyPool → ActualControls.SafePalette security), ((∏ index : Fin primaryPool,
      (groupLaw security).weight (inputs.1 index)) * (∏ index : Fin bodyPool,
        (ActualControls.bodyReference security).weight (inputs.2 index))) * coefficient.1) = coefficient.1 := by
    simpa only [law, FiniteDist.expectation, FiniteDist.independent, FiniteDist.prod_weight] using
      FiniteDist.expectation_const law coefficient.1
  rw [hconstant]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hterm, Finset.sum_const_zero, add_zero]

theorem coefficientWeight_mass_one (security order primaryPool bodyPool : ℕ)
    (coefficient : ActualControls.Coefficients security order) (hscalar : coefficient.1 = 1) :
    ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (coefficientWeight security order primaryPool bodyPool coefficient) = 1 := by
  rw [coefficientWeight_mean, hscalar]

end

end CurrentAFT.PhysicalSynthesis

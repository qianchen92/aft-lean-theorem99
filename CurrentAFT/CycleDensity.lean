import CurrentAFT.CycleJointLikelihood
import CurrentAFT.SupportedHoeffding
import CurrentAFT.CycleForestCounting
import CurrentAFT.PairCycleDensity

/-!
# Complete fixed-order protected-cycle root bound

The conditional law is the actual cyclic-difference pushforward. Its full
likelihood energy is bounded before centering, and the public selection
average gains the probability of having no isolated selected vertex.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color Index : Type*} [Fintype Color] [Fintype Index] [DecidableEq Index]

/-- Positive words are exactly words in the positive one-coordinate support. -/
def supportWordEquiv (reference : FiniteDist Color) :
    {word : Index → Color // ∀ index, 0 < reference.weight (word index)} ≃
      (Index → {color : Color // 0 < reference.weight color}) where
  toFun word index := ⟨word.val index, word.property index⟩
  invFun word := ⟨fun index => (word index).val, fun index => (word index).property⟩
  left_inv word := by rfl
  right_inv word := by rfl

/-- A complete pointwise squared-mass bound controls the full likelihood
energy by the support cardinality, without a smallest-atom loss. -/
theorem likelihoodEnergy_le_support_power (joint : FiniteDist (Index → Color))
    (reference : FiniteDist Color)
    (hpointwise : ∀ output, joint.weight output ^ 2 ≤ ∏ index, reference.weight (output index)) :
    (FiniteDist.independent (fun _ : Index => reference)).l2Sq
      (fun output => joint.weight output / (FiniteDist.independent (fun _ : Index => reference)).weight output) ≤
        ((referenceSupport reference).card : ℝ) ^ Fintype.card Index := by
  let product := FiniteDist.independent (fun _ : Index => reference)
  have hterm (output : Index → Color) :
      product.weight output * (joint.weight output / product.weight output) ^ 2 ≤
        if ∀ index, 0 < reference.weight (output index) then (1 : ℝ) else 0 := by
    by_cases hzero : product.weight output = 0
    · simp only [hzero, div_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      split_ifs <;> norm_num
    · have hpositive : 0 < product.weight output :=
        lt_of_le_of_ne (product.nonneg output) (Ne.symm hzero)
      have hcoordinates : ∀ index, 0 < reference.weight (output index) := by
        intro index
        apply lt_of_le_of_ne (reference.nonneg _)
        intro hequal
        apply hzero
        change (∏ i, reference.weight (output i)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ index) hequal.symm
      rw [if_pos hcoordinates]
      have hmass : joint.weight output ^ 2 ≤ product.weight output := hpointwise output
      calc
        _ = joint.weight output ^ 2 / product.weight output := by field_simp
        _ ≤ 1 := (div_le_one hpositive).mpr hmass
  have hsum := Finset.sum_le_sum (fun output (_ : output ∈ Finset.univ) => hterm output)
  change product.l2Sq (fun output => joint.weight output / product.weight output) ≤ _ at hsum
  apply hsum.trans_eq
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
  rw [Fintype.card_congr (supportWordEquiv (Index := Index) reference), Fintype.card_fun]
  rw [Fintype.card_subtype]
  simp only [Nat.cast_pow, referenceSupport]

/-- The current cyclic feature definition agrees exactly with the protected
root law. No endpoint-independence assertion is used. -/
theorem selectedFeatureLaw_sub_eq {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (source : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (sites : Selection body order) :
    selectedFeatureLaw body order source (fun first second => value second - value first) sites =
      selectedLaw body order modulus source value sites := by
  unfold selectedFeatureLaw selectedLaw ProtectedCycle.cycleLaw
  rw [FiniteDist.map_map]
  rfl

/-- Swapping the two iid scalars reverses the convention for subtraction. -/
theorem marginal_sub_eq {Scalar : Type*} [Fintype Scalar]
    (source : FiniteDist Scalar) {modulus : ℕ} [NeZero modulus]
    (value : Scalar → ZMod modulus) :
    PathLikelihood.marginal source (fun first second => value second - value first) =
      ProtectedCycle.differenceLaw source value := by
  ext output
  unfold PathLikelihood.marginal ProtectedCycle.differenceLaw
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  split_ifs <;> ring

/-- The true selected root probability satisfies the full joint bound. -/
theorem selectedLaw_weight_sq_le {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (output : Fin order → ZMod modulus) :
    (selectedLaw body order modulus source value sites).weight output ^ 2 ≤
      ∏ slot, (ProtectedCycle.differenceLaw source value).weight (output slot) := by
  have h := selectedFeatureLaw_weight_sq_le body order hbody source
    (fun first second => value second - value first) sites output
  rwa [selectedFeatureLaw_sub_eq, marginal_sub_eq] at h

/-- The whole selected law is supported on the actual product reference. -/
theorem selectedLaw_reference_support {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (input : Fin order → ZMod modulus)
    (hinput : (selectedLaw body order modulus source value sites).weight input ≠ 0) :
    ∀ slot, 0 < (ProtectedCycle.differenceLaw source value).weight (input slot) := by
  have hbound := selectedLaw_weight_sq_le body order modulus hbody source value sites input
  have hproduct : 0 < ∏ slot, (ProtectedCycle.differenceLaw source value).weight (input slot) :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hinput) hbound
  intro slot
  apply lt_of_le_of_ne ((ProtectedCycle.differenceLaw source value).nonneg _)
  intro hequal
  have hzero : (∏ i, (ProtectedCycle.differenceLaw source value).weight (input i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ slot) hequal.symm
  linarith

/-- Complete conditional centered root energy for the concrete Gaussian
cycle, valid at every order and with every zero residue atom retained. -/
theorem selected_centered_energy_le (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (hbody : 2 ≤ body) (sites : Selection body order) :
    (FiniteDist.independent (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites)
        (fun _ => gaussianRootReference width cutoff modulus)) ≤ (4 * cutoff + 1 : ℝ) ^ order := by
  apply (SupportedHoeffding.centeredRootDensity_energy_le _ _
    (selectedLaw_reference_support body order modulus hbody _ _ sites)).trans
  apply (likelihoodEnergy_le_support_power _ _
    (selectedLaw_weight_sq_le body order modulus hbody _ _ sites)).trans
  simp only [Fintype.card_fin]
  exact pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast gaussianRootReference_support_card width cutoff modulus) order

/-- Full fixed-order root smallness for the actual Gaussian cycle and the
actual uniform distinct public placement. The rare-event probability is
gained before taking the output norm. -/
theorem averaged_centered_norm_le (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * Real.sqrt ((4 * cutoff + 1 : ℝ) ^ order) /
        (body : ℝ) ^ ((order + 1) / 2) := by
  have hbodyTwo : 2 ≤ body := by omega
  let rootReference := gaussianRootReference width cutoff modulus
  let reference := FiniteDist.independent (fun _ : Fin order => rootReference)
  let placements := selectionLaw body order (by omega : order ≤ body)
  let coefficient := fun (sites : Selection body order) (output : Fin order → ZMod modulus) =>
    centeredRootDensity
      (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites) (fun _ => rootReference) output
  let bound : ℝ := Real.sqrt ((4 * cutoff + 1 : ℝ) ^ order)
  have hboundNonneg : 0 ≤ bound := Real.sqrt_nonneg _
  have hboundSquare : bound ^ 2 = (4 * cutoff + 1 : ℝ) ^ order := Real.sq_sqrt (by positivity)
  have henergy (sites : Selection body order) : reference.l2Sq (coefficient sites) ≤ bound ^ 2 := by
    rw [hboundSquare]
    exact selected_centered_energy_le body order modulus cutoff width hbodyTwo sites
  have hzero (sites : Selection body order) (hnot : ¬NoIsolated sites)
      (output : Fin order → ZMod modulus) (houtput : reference.weight output ≠ 0) :
      coefficient sites output = 0 := by
    obtain ⟨slot, hslot⟩ := not_forall.mp hnot
    have hisolated : Isolated sites slot := by
      intro other hother hadjacent
      exact hslot ⟨other, hother, hadjacent⟩
    have hslotOutput : rootReference.weight (output slot) ≠ 0 := by
      intro hzero
      apply houtput
      change (∏ index, rootReference.weight (output index)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ slot) hzero
    exact isolated_centeredRootDensity_zero body order modulus hbodyTwo
      (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites slot hisolated output hslotOutput
  have haverage := CurrentAFT.rare_mixture_l2Sq placements reference NoIsolated coefficient bound hzero henergy
  let average := centeredRootDensity
    (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus))) (fun _ => rootReference)
  have havg : average = fun output => placements.expectation (fun sites => coefficient sites output) := by
    funext output
    exact centeredRootDensity_mix placements
      (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus))) (fun _ => rootReference) output
  have haverageEnergy : reference.l2Sq average ≤ placements.eventMass NoIsolated ^ 2 * bound ^ 2 := by
    rw [havg]
    exact haverage
  have hprobability := placements.eventMass_nonneg NoIsolated
  have hprobabilityBound : placements.eventMass NoIsolated ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2) :=
    selectionLaw_noIsolated_probability body order horder hbody
  have hsquare := Real.sq_sqrt (reference.l2Sq_nonneg average)
  have hrootNonneg := Real.sqrt_nonneg (reference.l2Sq average)
  have hproductNonneg : 0 ≤ placements.eventMass NoIsolated * bound := mul_nonneg hprobability hboundNonneg
  have hrootBound : Real.sqrt (reference.l2Sq average) ≤ placements.eventMass NoIsolated * bound := by
    nlinarith
  change Real.sqrt (reference.l2Sq average) ≤
    (((2 * (order + 1) : ℕ) : ℝ) ^ order) * bound / (body : ℝ) ^ ((order + 1) / 2)
  calc
    _ ≤ placements.eventMass NoIsolated * bound := hrootBound
    _ ≤ ((((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2)) * bound :=
      mul_le_mul_of_nonneg_right hprobabilityBound hboundNonneg
    _ = _ := by ring

/-- Square roots commute with the natural powers used by the root bound. -/
theorem sqrt_nat_power (value : ℝ) (hvalue : 0 ≤ value) (order : ℕ) :
    Real.sqrt (value ^ order) = Real.sqrt value ^ order := by
  apply (Real.sqrt_eq_iff_eq_sq (pow_nonneg hvalue _) (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
  rw [← pow_mul, Nat.mul_comm order 2, pow_mul, Real.sq_sqrt hvalue]

theorem sqrt_nat_power_rpow (value : ℝ) (hvalue : 0 ≤ value) (order : ℕ) :
    Real.sqrt (value ^ order) = value ^ ((order : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hvalue]
  congr 1
  ring

/-- The complete fixed-order bound in the real half-power notation of the
manuscript's theorem. -/
theorem averaged_centered_norm_le_rpow (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * (4 * cutoff + 1 : ℝ) ^ ((order : ℝ) / 2) /
        (body : ℝ) ^ ((order + 1) / 2) := by
  have h := averaged_centered_norm_le body order modulus cutoff width horder hbody
  rwa [sqrt_nat_power_rpow _ (by positivity)] at h

/-- The parity exponent in the exact counting estimate is at least the
half-order exponent in the root tag. -/
theorem root_ratio_bound (size : ℝ) (hsize : 1 ≤ size) (width : ℝ) (hwidth : 0 ≤ width) (order : ℕ) :
    Real.sqrt (width ^ order) / size ^ ((order + 1) / 2) ≤
      (Real.sqrt width / Real.sqrt size) ^ order := by
  have hsizePositive : 0 < size := lt_of_lt_of_le zero_lt_one hsize
  have hsqrtPositive : 0 < Real.sqrt size := Real.sqrt_pos.mpr hsizePositive
  have hpower : (Real.sqrt size ^ order) ^ 2 = size ^ order := by
    rw [← pow_mul, Nat.mul_comm order 2, pow_mul, Real.sq_sqrt hsizePositive.le]
  have hpowerBound : size ^ order ≤ (size ^ ((order + 1) / 2)) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hsize (by omega)
  have hdenominator : Real.sqrt size ^ order ≤ size ^ ((order + 1) / 2) := by
    have hn := pow_nonneg (Real.sqrt_nonneg size) order
    have hm := pow_nonneg hsizePositive.le ((order + 1) / 2)
    nlinarith
  rw [div_pow, ← sqrt_nat_power width hwidth order]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (pow_pos hsqrtPositive _) hdenominator

/-- A root-tag form of the actual complete fixed-order estimate. -/
theorem averaged_centered_norm_le_tag (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) *
        (Real.sqrt (4 * cutoff + 1 : ℝ) / Real.sqrt (body : ℝ)) ^ order := by
  apply (averaged_centered_norm_le body order modulus cutoff width horder hbody).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (root_ratio_bound (body : ℝ) (by exact_mod_cast (by omega : 1 ≤ body)) _ (by positivity) order)
    (by positivity)

/-- The first centered root component is exactly zero in its actual
weighted L2 space, including the convention at zero reference atoms. -/
theorem averaged_centered_singleton_energy_zero {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) :
    (FiniteDist.independent (fun _ : Fin 1 => ProtectedCycle.differenceLaw source value)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body 1 modulus (by omega) source value)
        (fun _ => ProtectedCycle.differenceLaw source value)) = 0 := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  apply Finset.sum_eq_zero
  intro output _
  by_cases hzero : (FiniteDist.independent
      (fun _ : Fin 1 => ProtectedCycle.differenceLaw source value)).weight output = 0
  · rw [hzero, zero_mul]
  · have houtput : (ProtectedCycle.differenceLaw source value).weight (output 0) ≠ 0 := by
      intro h
      apply hzero
      change (∏ index : Fin 1, (ProtectedCycle.differenceLaw source value).weight (output index)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ 0) h
    have hisolated (sites : Selection body 1) : Isolated sites (0 : Fin 1) := by
      intro other hne
      exact False.elim (hne (Subsingleton.elim _ _))
    have hcoefficient (sites : Selection body 1) := isolated_centeredRootDensity_zero body 1 modulus
      hbody source value sites 0 (hisolated sites) output houtput
    dsimp only
    rw [averagedSelectedLaw, centeredRootDensity_mix]
    simp [hcoefficient, FiniteDist.expectation]

end

end CurrentAFT.CycleSelections

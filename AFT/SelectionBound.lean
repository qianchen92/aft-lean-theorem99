import AFT.NonlinearFock

/-! # Scalar bounds for the complete nonlinear selection sum -/

namespace AFT
namespace SelectionBound

open MeasureTheory
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false in
/-- The exact exponential moment that counts ordered selections. -/
theorem exponential_factorial_moment (degree : ℕ) :
    (∫ value : ℝ in Set.Ioi 0, Real.exp (-value) * value ^ degree) = degree.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (degree : ℝ) + 1) (r := 1) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, one_mul, one_div_one, Real.one_rpow,
    one_mul, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  simpa only [mul_comm] using h

/-- Integrability is established before exchanging the finite selection sum
with the exponential integral. -/
theorem exponential_factorial_integrable (degree : ℕ) :
    Integrable (fun value : ℝ => Real.exp (-value) * value ^ degree) (volume.restrict (Set.Ioi 0)) := by
  by_contra h
  have hmoment := exponential_factorial_moment degree
  rw [integral_undef h] at hmoment
  have hpositive : (0 : ℝ) < degree.factorial := by positivity
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- The whole factorial-weighted subset selection sum is bounded by one
geometric denominator. The proof integrates its exact finite generating
product against an exponential density. -/
theorem factorial_subset_sum_le {Index : Type*} (indices : Finset Index)
    (weight : Index → ℝ) (hnonneg : ∀ index ∈ indices, 0 ≤ weight index)
    (hsmall : (∑ index ∈ indices, weight index) < 1) :
    (∑ selected ∈ indices.powerset, (selected.card.factorial : ℝ) * ∏ index ∈ selected, weight index) ≤
      1 / (1 - ∑ index ∈ indices, weight index) := by
  let total := ∑ index ∈ indices, weight index
  have htotal : total < 1 := hsmall
  have hexpand (value : ℝ) :
      Real.exp (-value) * (∏ index ∈ indices, (1 + value * weight index)) =
        ∑ selected ∈ indices.powerset,
          (Real.exp (-value) * value ^ selected.card) * ∏ index ∈ selected, weight index := by
    rw [Finset.prod_one_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  have hintegral : (∫ value : ℝ in Set.Ioi 0,
      Real.exp (-value) * (∏ index ∈ indices, (1 + value * weight index))) =
        ∑ selected ∈ indices.powerset, (selected.card.factorial : ℝ) * ∏ index ∈ selected, weight index := by
    simp_rw [hexpand]
    rw [integral_finset_sum _ (fun selected _ => (exponential_factorial_integrable selected.card).mul_const _)]
    simp_rw [integral_mul_const, exponential_factorial_moment]
  have hpoint (value : ℝ) (hvalue : value ∈ Set.Ioi 0) :
      Real.exp (-value) * (∏ index ∈ indices, (1 + value * weight index)) ≤
        Real.exp ((total - 1) * value) := by
    have hprod : (∏ index ∈ indices, (1 + value * weight index)) ≤
        ∏ index ∈ indices, Real.exp (value * weight index) := by
      apply Finset.prod_le_prod
      · intro index hindex
        exact add_nonneg (by norm_num) (mul_nonneg hvalue.le (hnonneg index hindex))
      · intro index _
        simpa only [add_comm] using Real.add_one_le_exp (value * weight index)
    have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-value)).le
    apply hmul.trans_eq
    rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
    congr 1
    dsimp [total]
    ring
  rw [← hintegral]
  calc
    _ ≤ ∫ value : ℝ in Set.Ioi 0, Real.exp ((total - 1) * value) := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with value hvalue
        apply mul_nonneg (Real.exp_pos _).le
        exact Finset.prod_nonneg (fun index hindex => add_nonneg (by norm_num)
          (mul_nonneg hvalue.le (hnonneg index hindex)))
      · exact integrableOn_exp_mul_Ioi (by linarith) 0
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with value hvalue
        exact hpoint value hvalue
    _ = 1 / (1 - total) := by
      rw [integral_exp_mul_Ioi (by linarith : total - 1 < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      rw [show total - 1 = -(1 - total) by ring, div_neg]
      ring

/-- Number of nonlinear blocks in a selection. -/
def choiceActive : NonlinearFock.BlockChoice → ℕ
  | none => 0
  | some _ => 1

noncomputable def choiceWeight (pair triple : ℝ) : NonlinearFock.BlockChoice → ℝ
  | none => 1
  | some false => pair
  | some true => triple

noncomputable def selectionCount {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ := ∑ index, choiceActive (choice index)

noncomputable def selectionWeight {Index : Type*} [Fintype Index]
    (pair triple : Index → ℝ) (choice : Index → NonlinearFock.BlockChoice) : ℝ :=
  ∏ index, choiceWeight (pair index) (triple index) (choice index)

set_option backward.isDefEq.respectTransparency false in
/-- The categorical version needed by quadratic/cubic blocks: the complete
factorial-weighted selection sum has one geometric denominator in the total
pair-plus-triple activity. -/
theorem factorial_choice_sum_le {Index : Type*} [Fintype Index]
    (pair triple : Index → ℝ) (hpair : ∀ index, 0 ≤ pair index) (htriple : ∀ index, 0 ≤ triple index)
    (hsmall : (∑ index, (pair index + triple index)) < 1) :
    (∑ choice : Index → NonlinearFock.BlockChoice,
      ((selectionCount choice).factorial : ℝ) * selectionWeight pair triple choice) ≤
      1 / (1 - ∑ index, (pair index + triple index)) := by
  let total := ∑ index, (pair index + triple index)
  have htotal : total < 1 := hsmall
  have hsum (index : Index) (value : ℝ) :
      (∑ choice : NonlinearFock.BlockChoice,
        value ^ choiceActive choice * choiceWeight (pair index) (triple index) choice) =
        1 + value * (pair index + triple index) := by
    simp only [Fintype.sum_option, Fintype.sum_bool, choiceActive, choiceWeight, pow_zero, pow_one, mul_one]
    ring
  have hexpand (value : ℝ) :
      Real.exp (-value) * (∏ index, (1 + value * (pair index + triple index))) =
        ∑ choice : Index → NonlinearFock.BlockChoice,
          (Real.exp (-value) * value ^ selectionCount choice) * selectionWeight pair triple choice := by
    have h := Fintype.prod_sum (fun index (choice : NonlinearFock.BlockChoice) =>
      value ^ choiceActive choice * choiceWeight (pair index) (triple index) choice)
    simp_rw [hsum, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro choice _
    simp only [selectionCount, selectionWeight, mul_assoc]
  have hintegral : (∫ value : ℝ in Set.Ioi 0,
      Real.exp (-value) * (∏ index, (1 + value * (pair index + triple index)))) =
      ∑ choice : Index → NonlinearFock.BlockChoice,
        ((selectionCount choice).factorial : ℝ) * selectionWeight pair triple choice := by
    simp_rw [hexpand]
    rw [integral_finset_sum _ (fun choice _ =>
      (exponential_factorial_integrable (selectionCount choice)).mul_const _)]
    simp_rw [integral_mul_const, exponential_factorial_moment]
  rw [← hintegral]
  have hpoint (value : ℝ) (hvalue : value ∈ Set.Ioi 0) :
      Real.exp (-value) * (∏ index, (1 + value * (pair index + triple index))) ≤
        Real.exp ((total - 1) * value) := by
    have hp : (∏ index, (1 + value * (pair index + triple index))) ≤
        ∏ index, Real.exp (value * (pair index + triple index)) := by
      apply Finset.prod_le_prod
      · intro index _
        exact add_nonneg (by norm_num) (mul_nonneg hvalue.le (add_nonneg (hpair index) (htriple index)))
      · intro index _
        simpa only [add_comm] using Real.add_one_le_exp (value * (pair index + triple index))
    apply (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
    congr 1
    dsimp [total]
    ring
  calc
    _ ≤ ∫ value : ℝ in Set.Ioi 0, Real.exp ((total - 1) * value) := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with value hvalue
        apply mul_nonneg (Real.exp_pos _).le
        apply Finset.prod_nonneg
        intro index _
        exact add_nonneg (by norm_num) (mul_nonneg hvalue.le (add_nonneg (hpair index) (htriple index)))
      · exact integrableOn_exp_mul_Ioi (by linarith) 0
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with value hvalue
        exact hpoint value hvalue
    _ = _ := by
      rw [integral_exp_mul_Ioi (by linarith : total - 1 < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      rw [show total - 1 = -(1 - total) by ring, div_neg]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Omission of `k` linear factors changes the aggregate mean by at most
sqrt(k times the actual total linear energy). -/
theorem remaining_mean_energy_le {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (coefficient : Index → Coordinate → ℝ) (choice : Index → NonlinearFock.BlockChoice) :
    (∑ coordinate, (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) ^ 2) ≤
      2 * (∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) +
        2 * selectionCount choice * (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) := by
  let removed : Finset Index := Finset.univ.filter (fun index => choice index ≠ none)
  have hcard : removed.card = selectionCount choice := by
    dsimp [removed, selectionCount]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro index _
    cases choice index <;> simp [choiceActive]
  have hsplit (coordinate : Coordinate) :
      (∑ index, coefficient index coordinate) =
        (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) +
          ∑ index ∈ removed, coefficient index coordinate := by
    simp only [removed, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hc : choice index = none <;> simp [NonlinearFock.remainingLinear, hc]
  have hremoved : (∑ coordinate, (∑ index ∈ removed, coefficient index coordinate) ^ 2) ≤
      (selectionCount choice : ℝ) * (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) := by
    calc
      _ ≤ ∑ coordinate, (removed.card : ℝ) * ∑ index ∈ removed, coefficient index coordinate ^ 2 := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact sq_sum_le_card_mul_sum_sq
      _ = (selectionCount choice : ℝ) * ∑ index ∈ removed, ∑ coordinate, coefficient index coordinate ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm, hcard]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ removed)
          (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ coordinate, (2 * (∑ index, coefficient index coordinate) ^ 2 +
        2 * (∑ index ∈ removed, coefficient index coordinate) ^ 2) := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [hsplit coordinate]
      nlinarith [sq_nonneg ((∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) +
        2 * (∑ index ∈ removed, coefficient index coordinate))]
    _ = 2 * (∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) +
        2 * (∑ coordinate, (∑ index ∈ removed, coefficient index coordinate) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by linarith

set_option backward.isDefEq.respectTransparency false in
/-- Under the actual small linear-energy condition, omissions cost only a
fixed constant per selected nonlinear block, retaining cancellations in the
original aggregate mean. -/
theorem remaining_mean_exp_le {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (coefficient : Index → Coordinate → ℝ) (choice : Index → NonlinearFock.BlockChoice)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8) :
    Real.exp (2 * ∑ coordinate, (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) ^ 2) ≤
      Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) * 4 ^ selectionCount choice := by
  have hmean := remaining_mean_energy_le coefficient choice
  have hcount : (0 : ℝ) ≤ selectionCount choice := by positivity
  have hexponent : 2 * (∑ coordinate, (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) ^ 2) ≤
      4 * (∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) + selectionCount choice := by
    nlinarith
  apply (Real.exp_le_exp.mpr hexponent).trans
  rw [Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hone : Real.exp 1 ≤ (4 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le hone (selectionCount choice)
  simpa only [← Real.exp_nat_mul, mul_one] using h

/-- A uniform factorial bound for quadratic/cubic selections after the one
radius enlargement required by Fock multiplication. -/
theorem nonlinear_factorial_sqrt_bound (capacity pairCount tripleCount : ℕ)
    (hcount : pairCount + tripleCount ≤ capacity) :
    Real.sqrt (((2 * pairCount + 3 * tripleCount).factorial : ℝ) *
      2 ^ (2 * pairCount + 3 * tripleCount)) ≤
      (32 : ℝ) ^ (pairCount + tripleCount) * (pairCount + tripleCount).factorial *
        (Real.sqrt capacity) ^ tripleCount := by
  let count := pairCount + tripleCount
  have hfactor := BlockFock.nonlinear_selection_factorial_bound pairCount tripleCount capacity hcount
  have hfact : pairCount.factorial * tripleCount.factorial ≤ count.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hdegree : 2 * pairCount + 3 * tripleCount ≤ 3 * count := by dsimp [count]; omega
  have hpower : (2 : ℕ) ^ (2 * pairCount + 3 * tripleCount) ≤ 8 ^ count := by
    calc
      _ ≤ 2 ^ (3 * count) := Nat.pow_le_pow_right (by norm_num) hdegree
      _ = _ := by norm_num [Nat.pow_mul]
  have hnat : (2 * pairCount + 3 * tripleCount).factorial * 2 ^ (2 * pairCount + 3 * tripleCount) ≤
      1024 ^ count * capacity ^ tripleCount * count.factorial ^ 2 := by
    calc
      _ ≤ (64 ^ count * capacity ^ tripleCount * (pairCount.factorial * tripleCount.factorial) ^ 2) *
          8 ^ count := Nat.mul_le_mul hfactor hpower
      _ ≤ (64 ^ count * capacity ^ tripleCount * count.factorial ^ 2) * 8 ^ count := by gcongr
      _ = 512 ^ count * capacity ^ tripleCount * count.factorial ^ 2 := by
        rw [show (512 : ℕ) = 64 * 8 by norm_num, Nat.mul_pow]
        ring
      _ ≤ _ := by gcongr; norm_num
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hreal : ((2 * pairCount + 3 * tripleCount).factorial : ℝ) *
        2 ^ (2 * pairCount + 3 * tripleCount) ≤
        1024 ^ count * (capacity : ℝ) ^ tripleCount * (count.factorial : ℝ) ^ 2 := by exact_mod_cast hnat
    apply hreal.trans_eq
    simp only [mul_pow]
    rw [← pow_mul, Nat.mul_comm count 2, pow_mul]
    norm_num only [show (32 : ℝ) ^ 2 = 1024 by norm_num]
    have hsqrt : (Real.sqrt (capacity : ℝ) ^ tripleCount) ^ 2 = (capacity : ℝ) ^ tripleCount := by
      rw [← pow_mul, Nat.mul_comm tripleCount 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg capacity)]
    rw [hsqrt]
    dsimp [count]
    ring

noncomputable def pairSelections {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ :=
  ∑ index, if choice index = some false then 1 else 0

noncomputable def tripleSelections {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ :=
  ∑ index, if choice index = some true then 1 else 0

/-- Every nonlinear selection is either quadratic or cubic. -/
theorem selection_count_eq {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) :
    selectionCount choice = pairSelections choice + tripleSelections choice := by
  simp only [selectionCount, pairSelections, tripleSelections, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  cases choice index with
  | none => simp [choiceActive]
  | some active => cases active <;> simp [choiceActive]

/-- The selected homogeneous degree is exactly twice the quadratic count plus
three times the cubic count. -/
theorem selected_slots_card {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) :
    Fintype.card (Sigma (fun index => NonlinearFock.selectedSlots (choice index))) =
      2 * pairSelections choice + 3 * tripleSelections choice := by
  simp only [Fintype.card_sigma, pairSelections, tripleSelections, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  cases choice index with
  | none => simp [NonlinearFock.selectedSlots]
  | some active => cases active <;> simp [NonlinearFock.selectedSlots]

/-- Square roots commute with a finite product of nonnegative real factors. -/
theorem sqrt_prod {Index : Type*} (indices : Finset Index) (weight : Index → ℝ)
    (hweight : ∀ index ∈ indices, 0 ≤ weight index) :
    Real.sqrt (∏ index ∈ indices, weight index) = ∏ index ∈ indices, Real.sqrt (weight index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnot ih =>
    rw [Finset.prod_insert hnot, Real.sqrt_mul (hweight index (Finset.mem_insert_self _ _)),
      Finset.prod_insert hnot, ih (fun other hother => hweight other (Finset.mem_insert_of_mem hother))]

/-- Actual energy of the selected coordinate tensor equals the product of the
actual local quadratic/cubic energies, including the constant choices. -/
theorem selection_tensor_energy {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (choice : Index → NonlinearFock.BlockChoice) :
    BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice) =
      selectionWeight (fun index => BlockFock.tensorEnergy (quadratic index))
        (fun index => BlockFock.tensorEnergy (cubic index)) choice := by
  rw [NonlinearFock.selectionTensor, NonlinearFock.family_tensor_energy]
  unfold selectionWeight
  apply Finset.prod_congr rfl
  intro index _
  cases choice index with
  | none => simp [NonlinearFock.selectedTensor, NonlinearFock.selectedSlots,
      BlockFock.tensorEnergy, choiceWeight]
  | some active => cases active <;> rfl

/-- Actual selected tensor norms multiply into local Hilbert norms. -/
theorem selection_tensor_sqrt_energy {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (choice : Index → NonlinearFock.BlockChoice) :
    Real.sqrt (BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice)) =
      selectionWeight (fun index => Real.sqrt (BlockFock.tensorEnergy (quadratic index)))
        (fun index => Real.sqrt (BlockFock.tensorEnergy (cubic index))) choice := by
  rw [selection_tensor_energy]
  unfold selectionWeight
  rw [sqrt_prod _ _ (by
    intro index _
    cases choice index with
    | none => norm_num [choiceWeight]
    | some active => cases active <;> exact Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply Finset.prod_congr rfl
  intro index _
  cases choice index with
  | none => simp [choiceWeight]
  | some active => cases active <;> rfl

/-- Rescaling each selected quadratic/cubic activity collects exactly one
common factor per selected block and one extra factor per cubic selection. -/
theorem selection_weight_scale {Index : Type*} [Fintype Index]
    (pair triple : Index → ℝ) (scale cubicScale : ℝ) (choice : Index → NonlinearFock.BlockChoice) :
    selectionWeight (fun index => scale * pair index)
      (fun index => scale * cubicScale * triple index) choice =
      scale ^ selectionCount choice * cubicScale ^ tripleSelections choice * selectionWeight pair triple choice := by
  have hpoint (index : Index) :
      choiceWeight (scale * pair index) (scale * cubicScale * triple index) (choice index) =
        (scale ^ choiceActive (choice index)) * (cubicScale ^ (if choice index = some true then 1 else 0)) *
          choiceWeight (pair index) (triple index) (choice index) := by
    cases choice index with
    | none => simp [choiceWeight, choiceActive]
    | some active => cases active <;> simp [choiceWeight, choiceActive]
  simp only [selectionWeight, hpoint, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    selectionCount, tripleSelections]

/-- The number of genuinely nonlinear blocks, detected by their actual local
Hilbert energies, rather than the size of the linear background. -/
noncomputable def nonlinearSupport {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) : Finset Index :=
  Finset.univ.filter (fun index => BlockFock.tensorEnergy (quadratic index) ≠ 0 ∨ BlockFock.tensorEnergy (cubic index) ≠ 0)

/-- Every nonzero selection uses only genuinely nonlinear blocks. -/
theorem selection_count_le_support {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (choice : Index → NonlinearFock.BlockChoice)
    (hnonzero : BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice) ≠ 0) :
    selectionCount choice ≤ (nonlinearSupport quadratic cubic).card := by
  rw [selection_tensor_energy] at hnonzero
  have hlocal (index : Index) : choiceWeight (BlockFock.tensorEnergy (quadratic index))
      (BlockFock.tensorEnergy (cubic index)) (choice index) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hnonzero) index (Finset.mem_univ _)
  simp only [selectionCount, nonlinearSupport, Finset.card_filter]
  apply Finset.sum_le_sum
  intro index _
  have h := hlocal index
  cases hc : choice index with
  | none => simp [choiceActive]
  | some active =>
    cases active
    · simp only [hc, choiceWeight] at h
      simp [choiceActive, h]
    · simp only [hc, choiceWeight] at h
      simp [choiceActive, h]

/-- Local Hilbert norms used by the original pair and triple activities. -/
noncomputable def localPairNorm {Index Coordinate : Type*} [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate) (index : Index) : ℝ :=
  Real.sqrt (BlockFock.tensorEnergy (quadratic index))

noncomputable def localTripleNorm {Index Coordinate : Type*} [Fintype Coordinate]
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (index : Index) : ℝ :=
  Real.sqrt (BlockFock.tensorEnergy (cubic index))

set_option backward.isDefEq.respectTransparency false in
/-- A pointwise selection estimate with an absolute cost per selected block;
all quantities are computed from actual tensors and actual aggregate means. -/
theorem cubic_selection_term_le {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (coefficient : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (nonlinearSupport quadratic cubic).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8)
    (choice : Index → NonlinearFock.BlockChoice) :
    Real.sqrt (((Fintype.card (Sigma (fun index => NonlinearFock.selectedSlots (choice index)))).factorial : ℝ) *
      2 ^ Fintype.card (Sigma (fun index => NonlinearFock.selectedSlots (choice index))) *
        BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice)) *
      (2 * Real.exp (2 * ∑ coordinate, (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) ^ 2)) ≤
      (2 * Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2)) *
        (((selectionCount choice).factorial : ℝ) *
          selectionWeight (fun index => 128 * localPairNorm quadratic index)
            (fun index => 128 * Real.sqrt capacity * localTripleNorm cubic index) choice) := by
  have hweight : 0 ≤ selectionWeight (fun index => 128 * localPairNorm quadratic index)
      (fun index => 128 * Real.sqrt capacity * localTripleNorm cubic index) choice := by
    unfold selectionWeight
    apply Finset.prod_nonneg
    intro index _
    cases choice index with
    | none => norm_num [choiceWeight]
    | some active => cases active <;> simp only [choiceWeight, localPairNorm, localTripleNorm] <;> positivity
  by_cases hzero : BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice) = 0
  · simp only [hzero, mul_zero, Real.sqrt_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hweight)
  · have hcount : pairSelections choice + tripleSelections choice ≤ capacity := by
      rw [← selection_count_eq]
      exact (selection_count_le_support quadratic cubic choice hzero).trans hcapacity
    have hfactor := nonlinear_factorial_sqrt_bound capacity (pairSelections choice) (tripleSelections choice) hcount
    rw [← selection_count_eq] at hfactor
    have hmean := remaining_mean_exp_le coefficient choice henergy
    have hnorm : 0 ≤ BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.sqrt_mul (by positivity), selected_slots_card]
    calc
      _ ≤ ((32 : ℝ) ^ selectionCount choice * ((selectionCount choice).factorial : ℝ) *
            Real.sqrt capacity ^ tripleSelections choice *
            Real.sqrt (BlockFock.tensorEnergy (NonlinearFock.selectionTensor quadratic cubic choice))) *
          (2 * (Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) * 4 ^ selectionCount choice)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _)
        · exact mul_le_mul_of_nonneg_left hmean (by norm_num)
        · positivity
        · positivity
      _ = _ := by
        rw [selection_tensor_sqrt_energy, selection_weight_scale]
        rw [show (128 : ℝ) = 32 * 4 by norm_num, mul_pow]
        rw [show localPairNorm quadratic = (fun index => Real.sqrt (BlockFock.tensorEnergy (quadratic index))) from rfl,
          show localTripleNorm cubic = (fun index => Real.sqrt (BlockFock.tensorEnergy (cubic index))) from rfl]
        ring

set_option backward.isDefEq.respectTransparency false in
/-- The full finite selection majorant is dimension-independent under the
original linear-energy and nonlinear-activity smallness conditions. The
capacity is the actual number of nonzero nonlinear blocks. -/
theorem cubic_selection_majorant_le {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (coefficient : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (nonlinearSupport quadratic cubic).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * localPairNorm quadratic index +
      128 * Real.sqrt capacity * localTripleNorm cubic index)) < 1) :
    NonlinearFock.cubicSelectionMajorant coefficient quadratic cubic ≤
      (2 * Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2)) /
        (1 - ∑ index, (128 * localPairNorm quadratic index +
          128 * Real.sqrt capacity * localTripleNorm cubic index)) := by
  have hsum := Finset.sum_le_sum (fun choice (_ : choice ∈ (Finset.univ : Finset (Index → NonlinearFock.BlockChoice))) =>
    cubic_selection_term_le coefficient quadratic cubic capacity hcapacity henergy choice)
  rw [← Finset.mul_sum] at hsum
  apply hsum.trans
  have hgeom := factorial_choice_sum_le (fun index => 128 * localPairNorm quadratic index)
    (fun index => 128 * Real.sqrt capacity * localTripleNorm cubic index)
    (fun _ => by unfold localPairNorm; positivity) (fun _ => by unfold localTripleNorm; positivity) hsmall
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ 2 * Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- Uniform absolute-constant form of the complete nonlinear selection bound. -/
theorem cubic_selection_majorant_uniform {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (coefficient : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (nonlinearSupport quadratic cubic).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * localPairNorm quadratic index +
      128 * Real.sqrt capacity * localTripleNorm cubic index)) ≤ 1 / 2) :
    NonlinearFock.cubicSelectionMajorant coefficient quadratic cubic ≤
      4 * Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) := by
  apply (cubic_selection_majorant_le coefficient quadratic cubic capacity hcapacity henergy (by linarith)).trans
  apply (div_le_iff₀ (by linarith)).mpr
  nlinarith [Real.exp_pos (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2)]

set_option backward.isDefEq.respectTransparency false in
/-- The original dimension-independent independent-block Fock estimate for
actual degree-at-most-three block polynomials, with explicit absolute constants. -/
theorem independent_cubic_block_fock_bound {Index Coordinate : Type*}
    [Fintype Index] [Fintype Coordinate] [Nonempty Coordinate]
    (coefficient : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (capacity : ℕ)
    (hcapacity : (nonlinearSupport quadratic cubic).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * localPairNorm quadratic index +
      128 * Real.sqrt capacity * localTripleNorm cubic index)) ≤ 1 / 2) :
    (∫ value, Complex.normSq (NonlinearFock.cubicBlockProduct coefficient quadratic cubic value)
      ∂FockGaussian.field) ≤
      16 * Real.exp (8 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) := by
  apply (NonlinearFock.cubic_block_energy_le coefficient quadratic cubic henergy).trans
  have hnorm := cubic_selection_majorant_uniform coefficient quadratic cubic capacity hcapacity henergy hsmall
  have hnonneg := NonlinearFock.cubic_selection_majorant_nonneg coefficient quadratic cubic
  have hsquare : NonlinearFock.cubicSelectionMajorant coefficient quadratic cubic ^ 2 ≤
      (4 * Real.exp (4 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ hnonneg hnorm 2
  apply hsquare.trans_eq
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Complete histogram tail with an explicit uniform block estimate. The
premises refer only to actual local coefficient energies, genuine nonlinear
support, and exact coefficients of the given product, never to a desired
norm or tail estimate. -/
theorem complete_cubic_histogram_tail_uniform {Index Coordinate : Type*}
    [Fintype Index] [Fintype Coordinate] [Nonempty Coordinate]
    (population cutoff capacity : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (coefficient : Index → Coordinate → ℝ)
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate)
    (hpopulation : 0 < population) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hsymmetric : ∀ degree ≤ population, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word)
    (hcoefficients : ∀ value,
      TensorFock.seriesEvaluation (Finset.range (population + 1))
        (TensorFock.normalizedTensor population radius tensor) value =
          NonlinearFock.cubicBlockProduct coefficient quadratic cubic value)
    (hcapacity : (nonlinearSupport quadratic cubic).card ≤ capacity)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * localPairNorm quadratic index +
      128 * Real.sqrt capacity * localTripleNorm cubic index)) ≤ 1 / 2) :
    HistogramTail.likelihoodTailEnergy population cutoff (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (16 * Real.exp (8 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2)) := by
  apply (HistogramTail.complete_tail_energy_le population cutoff radius _ hpopulation
    (fun degree => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hradius).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change HistogramTail.fockEnergy population radius (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤ _
  rw [← TensorFock.normalized_fock_isometry population radius tensor hsymmetric]
  simp_rw [hcoefficients]
  exact independent_cubic_block_fock_bound coefficient quadratic cubic capacity hcapacity henergy hsmall

end SelectionBound
end AFT

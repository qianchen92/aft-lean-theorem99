import AFT.HilbertConcentration
import AFT.RootSlice

/-!
# Exponential Hilbert concentration after an actual event

Conditioning is the finite probability law from `RootSlice`.  A concave
power interpolation gives logarithmic event cost, avoiding an uncompensated
inverse-event-probability factor in the exponential-square estimate.
-/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

omit [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] in
theorem conditional_expectation_nonneg_le (law : FiniteDist Sample) (event : Sample → Prop)
    (hprob : 0 < law.eventMass event) (value : Sample → ℝ) (hvalue : ∀ sample, 0 ≤ value sample) :
    (law.condition event hprob).expectation value ≤ law.expectation value / law.eventMass event := by
  unfold FiniteDist.expectation FiniteDist.condition
  simp only
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hprob.le
  apply Finset.sum_le_sum
  intro sample _
  split_ifs
  · rfl
  · exact (zero_mul _).le.trans (mul_nonneg (law.nonneg sample) (hvalue sample))

omit [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] in
theorem exponential_interpolation (law : FiniteDist Sample) (value : Sample → ℝ)
    (fraction bound : ℝ) (hfraction : 0 ≤ fraction) (hle : fraction ≤ 1)
    (hbound : law.expectation (fun sample => Real.exp (value sample)) ≤ bound) :
    law.expectation (fun sample => Real.exp (fraction * value sample)) ≤ bound ^ fraction := by
  have hh := (Real.concaveOn_rpow hfraction hle).le_map_sum
    (fun sample (_ : sample ∈ Finset.univ) => law.nonneg sample) law.sum_one
    (fun sample (_ : sample ∈ Finset.univ) => (Real.exp_nonneg (value sample)))
  simp only [smul_eq_mul] at hh
  have heq (sample : Sample) : Real.exp (fraction * value sample) = Real.exp (value sample) ^ fraction := by
    rw [mul_comm fraction, Real.exp_mul]
  simp only [heq]
  apply hh.trans
  apply Real.rpow_le_rpow _ hbound hfraction
  exact Finset.sum_nonneg fun sample _ => mul_nonneg (law.nonneg sample) (Real.exp_nonneg _)

theorem vectorMean_norm_sq_le (law : FiniteDist Sample) (value : Sample → Hilbert) :
    ‖vectorMean law value‖ ^ 2 ≤ law.expectation (fun sample => ‖value sample‖ ^ 2) := by
  have hnorm : ‖vectorMean law value‖ ≤ law.expectation (fun sample => ‖value sample‖) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro sample _
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (law.nonneg sample)]
    rfl
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (scalar_mean_sq_le law _)

theorem vectorMean_exp_norm_sq_le (law : FiniteDist Sample) (value : Sample → Hilbert)
    (parameter : ℝ) (hparameter : 0 ≤ parameter) :
    Real.exp (parameter * ‖vectorMean law value‖ ^ 2) ≤
      law.expectation (fun sample => Real.exp (parameter * ‖value sample‖ ^ 2)) := by
  apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (vectorMean_norm_sq_le law value) hparameter)).trans
  have hh := convexOn_exp.map_sum_le
    (fun sample (_ : sample ∈ Finset.univ) => law.nonneg sample) law.sum_one
    (fun sample (_ : sample ∈ Finset.univ) => Set.mem_univ (parameter * ‖value sample‖ ^ 2))
  simp only [smul_eq_mul] at hh
  convert hh using 1
  congr 1
  unfold FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  ring

/-- An actual conditional law, centered at its actual conditional vector
mean.  The exponent of the event cost tends to zero with the requested
Laplace parameter. -/
theorem conditional_centered_square_interpolation (law : FiniteDist Sample)
    (event : Sample → Prop) (hprob : 0 < law.eventMass event) (value : Sample → Hilbert)
    (baseParameter parameter bound : ℝ) (hbase : 0 < baseParameter)
    (hparameter : 0 ≤ parameter) (hsmall : 2 * parameter ≤ baseParameter)
    (hbound : law.expectation (fun sample => Real.exp (baseParameter * ‖value sample‖ ^ 2)) ≤ bound) :
    (law.condition event hprob).expectation (fun sample =>
      Real.exp (parameter * ‖value sample - vectorMean (law.condition event hprob) value‖ ^ 2)) ≤
        (bound / law.eventMass event) ^ (4 * parameter / baseParameter) := by
  let conditional := law.condition event hprob
  let mean := vectorMean conditional value
  let fraction := 2 * parameter / baseParameter
  have hf0 : 0 ≤ fraction := by dsimp [fraction]; positivity
  have hf1 : fraction ≤ 1 := (div_le_one hbase).mpr hsmall
  have hexp : conditional.expectation (fun sample => Real.exp (baseParameter * ‖value sample‖ ^ 2)) ≤
      bound / law.eventMass event :=
    (conditional_expectation_nonneg_le law event hprob _ (fun _ => Real.exp_nonneg _)).trans
      (div_le_div_of_nonneg_right hbound hprob.le)
  have hhalf : conditional.expectation (fun sample => Real.exp ((2 * parameter) * ‖value sample‖ ^ 2)) ≤
      (bound / law.eventMass event) ^ fraction := by
    have hh := exponential_interpolation conditional (fun sample => baseParameter * ‖value sample‖ ^ 2)
      fraction (bound / law.eventMass event) hf0 hf1 hexp
    convert hh using 1
    congr 1
    funext sample
    congr 1
    dsimp [fraction]
    field_simp
  have hm : Real.exp ((2 * parameter) * ‖mean‖ ^ 2) ≤ (bound / law.eventMass event) ^ fraction :=
    (vectorMean_exp_norm_sq_le conditional value (2 * parameter) (by positivity)).trans hhalf
  have hpoint (sample : Sample) : Real.exp (parameter * ‖value sample - mean‖ ^ 2) ≤
      Real.exp ((2 * parameter) * ‖mean‖ ^ 2) * Real.exp ((2 * parameter) * ‖value sample‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := norm_sub_le (value sample) mean
    have hs : ‖value sample - mean‖ ^ 2 ≤ 2 * ‖mean‖ ^ 2 + 2 * ‖value sample‖ ^ 2 := by
      nlinarith [norm_nonneg (value sample - mean), norm_nonneg (value sample), norm_nonneg mean,
        sq_nonneg (‖value sample‖ - ‖mean‖)]
    nlinarith
  have hh := Finset.sum_le_sum (fun sample (_ : sample ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint sample) (conditional.nonneg sample))
  have heq : (∑ sample, conditional.weight sample *
      (Real.exp ((2 * parameter) * ‖mean‖ ^ 2) * Real.exp ((2 * parameter) * ‖value sample‖ ^ 2))) =
      Real.exp ((2 * parameter) * ‖mean‖ ^ 2) * conditional.expectation
        (fun sample => Real.exp ((2 * parameter) * ‖value sample‖ ^ 2)) := by
    simp only [FiniteDist.expectation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample _
    ring
  rw [heq] at hh
  have hcn : 0 ≤ conditional.expectation (fun sample => Real.exp ((2 * parameter) * ‖value sample‖ ^ 2)) :=
    Finset.sum_nonneg fun sample _ => mul_nonneg (conditional.nonneg sample) (Real.exp_nonneg _)
  have hboundpos : 0 < bound / law.eventMass event :=
    lt_of_lt_of_le (Real.exp_pos (baseParameter * ‖vectorMean conditional value‖ ^ 2))
      ((vectorMean_exp_norm_sq_le conditional value baseParameter hbase.le).trans hexp)
  have hprod := mul_le_mul hm hhalf hcn (le_of_lt (Real.rpow_pos_of_pos hboundpos fraction))
  apply (hh.trans hprod).trans_eq
  rw [← Real.rpow_add hboundpos]
  congr 1
  dsimp [fraction]
  ring

/-- The conditional Hilbert-sum bound required by the complete-tail proof.
All concentration premises are derived from independent centered summands
and their actual deterministic bounds.  The event is arbitrary and may be
as rare as the exact integer root slice. -/
theorem conditioned_hilbert_sum_square_mgf (count : ℕ)
    (law : Fin count → FiniteDist Sample) (value : Fin count → Sample → Hilbert)
    (bound : Fin count → ℝ) (hcenter : ∀ index, vectorMean (law index) (value index) = 0)
    (hbound : ∀ index, 0 ≤ bound index) (hvalue : ∀ index sample, ‖value index sample‖ ≤ bound index)
    (event : (Fin count → Sample) → Prop)
    (hprob : 0 < (FiniteDist.independent law).eventMass event)
    (hbudget : 0 < ∑ index, bound index ^ 2) (parameter : ℝ) (hparameter : 0 ≤ parameter)
    (hsmall : 64 * parameter * (∑ index, bound index ^ 2) ≤ 1) :
    ((FiniteDist.independent law).condition event hprob).expectation (fun word =>
      Real.exp (parameter * ‖(∑ index, value index (word index)) -
        vectorMean ((FiniteDist.independent law).condition event hprob)
          (fun word => ∑ index, value index (word index))‖ ^ 2)) ≤
      Real.exp ((128 * parameter * ∑ index, bound index ^ 2) *
        Real.log (2 * Real.exp 1 / (FiniteDist.independent law).eventMass event)) := by
  let budget := ∑ index, bound index ^ 2
  let baseParameter := 1 / (32 * budget)
  have hb : 0 < budget := hbudget
  have ha : 0 < baseParameter := by dsimp [baseParameter]; positivity
  have hab : baseParameter * budget = 1 / 32 := by
    dsimp [baseParameter]
    field_simp
  have hbaseSmall : 16 * baseParameter * (∑ index, bound index ^ 2) < 1 := by
    change 16 * baseParameter * budget < 1
    nlinarith
  have hbase := hilbert_sum_square_mgf count law value bound hcenter hbound hvalue
    baseParameter ha.le hbaseSmall
  have hconstant : Real.exp (2 * baseParameter * budget) *
      (Real.sqrt (1 - 16 * baseParameter * budget))⁻¹ ≤ 2 * Real.exp 1 := by
    have he : Real.exp (2 * baseParameter * budget) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hs : 1 - 16 * baseParameter * budget = 1 / 2 := by nlinarith
    rw [hs]
    have hroot : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
    have hi : (Real.sqrt (1 / 2 : ℝ))⁻¹ ≤ 2 := by
      rw [← one_div]
      apply (div_le_iff₀ hroot).mpr
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hh := mul_le_mul he hi (inv_nonneg.mpr hroot.le) (Real.exp_nonneg 1)
    simpa only [mul_comm (Real.exp 1)] using hh
  have hsmall' : 2 * parameter ≤ baseParameter := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * budget)).mpr
    change 64 * parameter * budget ≤ 1 at hsmall
    nlinarith
  have hh := conditional_centered_square_interpolation (FiniteDist.independent law) event hprob
    (fun word => ∑ index, value index (word index)) baseParameter parameter (2 * Real.exp 1)
    ha hparameter hsmall' (hbase.trans hconstant)
  have hpos : 0 < 2 * Real.exp 1 / (FiniteDist.independent law).eventMass event := by positivity
  apply hh.trans_eq
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  dsimp [baseParameter, budget]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end

end AFT.FiniteConcentration

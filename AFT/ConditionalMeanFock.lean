import AFT.ConditionalConcentration

/-! # The actual root-conditioned mean and bounded queue displacement -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

/-- A bounded actual queue displacement preserves the logarithmic slice
cost of the root mean. The displacement can even depend on the root word. -/
theorem conditioned_shifted_hilbert_sum_square_mgf (count : ℕ)
    (law : Fin count → FiniteDist Sample) (value : Fin count → Sample → Hilbert)
    (bound : Fin count → ℝ) (hcenter : ∀ index, vectorMean (law index) (value index) = 0)
    (hbound : ∀ index, 0 ≤ bound index) (hvalue : ∀ index sample, ‖value index sample‖ ≤ bound index)
    (event : (Fin count → Sample) → Prop)
    (hprob : 0 < (FiniteDist.independent law).eventMass event)
    (hbudget : 0 < ∑ index, bound index ^ 2)
    (shift : (Fin count → Sample) → Hilbert) (shiftBound : ℝ)
    (hshiftBound : 0 ≤ shiftBound) (hshift : ∀ word, ‖shift word‖ ≤ shiftBound)
    (parameter : ℝ) (hparameter : 0 ≤ parameter)
    (hsmall : 128 * parameter * (∑ index, bound index ^ 2) ≤ 1) :
    ((FiniteDist.independent law).condition event hprob).expectation (fun word =>
      Real.exp (parameter * ‖((∑ index, value index (word index)) -
        vectorMean ((FiniteDist.independent law).condition event hprob)
          (fun word => ∑ index, value index (word index))) + shift word‖ ^ 2)) ≤
      Real.exp (2 * parameter * shiftBound ^ 2 +
        (256 * parameter * ∑ index, bound index ^ 2) *
          Real.log (2 * Real.exp 1 / (FiniteDist.independent law).eventMass event)) := by
  let conditional := (FiniteDist.independent law).condition event hprob
  let centered (word : Fin count → Sample) := (∑ index, value index (word index)) -
    vectorMean conditional (fun word => ∑ index, value index (word index))
  have hexp := conditioned_hilbert_sum_square_mgf count law value bound hcenter hbound hvalue
    event hprob hbudget (2 * parameter) (by positivity) (by nlinarith only [hsmall])
  have hpoint (word : Fin count → Sample) :
      Real.exp (parameter * ‖centered word + shift word‖ ^ 2) ≤
        Real.exp (2 * parameter * shiftBound ^ 2) * Real.exp ((2 * parameter) * ‖centered word‖ ^ 2) := by
    have hn := norm_add_le (centered word) (shift word)
    have hs : ‖centered word + shift word‖ ^ 2 ≤ (‖centered word‖ + ‖shift word‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    have hb : ‖shift word‖ ^ 2 ≤ shiftBound ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hshiftBound).mpr (hshift word)
    have hc : ‖centered word + shift word‖ ^ 2 ≤ 2 * ‖centered word‖ ^ 2 + 2 * shiftBound ^ 2 := by
      nlinarith [sq_nonneg (‖centered word‖ - ‖shift word‖)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hc hparameter
    nlinarith only [hh]
  have hh := Finset.sum_le_sum (fun word (_ : word ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint word) (conditional.nonneg word))
  have heq : (∑ word, conditional.weight word *
      (Real.exp (2 * parameter * shiftBound ^ 2) * Real.exp ((2 * parameter) * ‖centered word‖ ^ 2))) =
      Real.exp (2 * parameter * shiftBound ^ 2) * conditional.expectation
        (fun word => Real.exp ((2 * parameter) * ‖centered word‖ ^ 2)) := by
    unfold FiniteDist.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring
  rw [heq] at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end

end AFT.FiniteConcentration

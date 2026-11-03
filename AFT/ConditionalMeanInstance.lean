import AFT.ConditionalMeanFock

namespace AFT.FiniteConcentration
open scoped BigOperators Classical
noncomputable section
variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

/-- The concentration theorem is independent of the unique decidable equality instance. -/
theorem conditioned_shifted_hilbert_sum_square_mgf_instance (count : ℕ) [decision : DecidableEq (Fin count)]
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
  have hdecision : decision = instDecidableEqFin count := Subsingleton.elim _ _
  cases hdecision
  exact conditioned_shifted_hilbert_sum_square_mgf count law value bound hcenter hbound hvalue
    event hprob hbudget shift shiftBound hshiftBound hshift parameter hparameter hsmall

end
end AFT.FiniteConcentration

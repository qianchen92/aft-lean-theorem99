import AFT.IntegerLinearIteration
import AFT.CachedLinearIteration

/-! # Polynomial operand height in the materialized rational iteration -/
namespace AFT.RationalNumerics
open scoped BigOperators
variable {Color : Type*} [Fintype Color]

/-- A single common denominator is chosen for the stored matrix and rhs.
Consequently the bit bound is linear in the iteration count. -/
theorem linearIteration_height (matrix : Color → Color → ℚ) (rhs : Color → ℚ)
    (bits steps : ℕ) (hmatrix : ∀output input,HeightBound (matrix output input) bits)
    (hrhs : ∀output,HeightBound (rhs output) bits) (output : Color) :
    HeightBound (linearIteration matrix rhs steps output)
      (steps*((3*(Fintype.card Color^2+Fintype.card Color)+1)*bits+Fintype.card Color+1)) := by
  let values : (Color×Color)⊕Color → ℚ := Sum.elim (fun pair => matrix pair.1 pair.2) rhs
  let denominator := commonDenominator values
  let intMatrix := fun output input => commonNumerator values (Sum.inl (output,input))
  let intRhs := fun output => commonNumerator values (Sum.inr output)
  have hvalues : ∀index,HeightBound (values index) bits := by
    intro index
    cases index with
    | inl pair => exact hmatrix pair.1 pair.2
    | inr color => exact hrhs color
  have hc : Fintype.card ((Color×Color)⊕Color)=Fintype.card Color^2+Fintype.card Color := by
    simp [pow_two]
  have hd := commonDenominator_le values bits hvalues
  have hi := commonNumerator_abs_le values bits hvalues
  rw [hc] at hd hi
  have hh := integerLinearIteration_height denominator ((Fintype.card Color^2+Fintype.card Color+1)*bits)
    ((Fintype.card Color^2+Fintype.card Color)*bits) intMatrix intRhs hd
    (fun output input => hi (Sum.inl (output,input))) (fun output => hi (Sum.inr output)) steps output
  rw [integerLinearIteration_exact denominator (commonDenominator_pos values)] at hh
  have hm : (fun out inp => (intMatrix out inp : ℚ)/denominator)=matrix := by
    funext out inp
    exact commonNumerator_div values (Sum.inl (out,inp))
  have hr : (fun out => (intRhs out : ℚ)/denominator)=rhs := by
    funext out
    exact commonNumerator_div values (Sum.inr out)
  rw [hm,hr] at hh
  convert hh using 1
  unfold iterationHeightSlope
  ring

/-- Every cached iterate, rather than just the final scalar result, has
this polynomial bound on numerator and denominator lengths. -/
theorem cachedLinearIteration_height (colors bits steps : ℕ)
    (matrix : Fin colors → Fin colors → ℚ) (rhs : Fin colors → ℚ)
    (hmatrix : ∀output input,HeightBound (matrix output input) bits)
    (hrhs : ∀output,HeightBound (rhs output) bits) (output : Fin colors) :
    HeightBound ((cachedLinearIteration (cachedMatrix colors matrix) (Vector.ofFn rhs) steps).get output)
      (steps*((3*(colors^2+colors)+1)*bits+colors+1)) := by
  rw [cachedLinearIteration_get]
  simpa only [Fintype.card_fin] using linearIteration_height matrix rhs bits steps hmatrix hrhs output

end AFT.RationalNumerics

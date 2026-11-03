import CurrentAFT.PhysicalPolynomialAverages

/-! # Independence from finite enumeration witnesses -/
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial CycleRootExpansion
noncomputable section

theorem generating_enumeration {Slot Color : Type*} [Fintype Color]
    (first second : Fintype Slot) (reference : Color → ℝ) (mass : (Slot → Color) → ℝ) :
    @centeredGeneratingLinear Slot Color first _ reference mass =
      @centeredGeneratingLinear Slot Color second _ reference mass := by
  cases Subsingleton.elim first second
  rfl

theorem uniform_average_enumeration {Source Value : Type*} [Nonempty Source]
    [AddCommGroup Value] [Module ℝ Value] (first second : Fintype Source) (test : Source → Value) :
    (letI := first; expectationLinear (FiniteDist.uniform Source) test) =
      (letI := second; expectationLinear (FiniteDist.uniform Source) test) := by
  cases Subsingleton.elim first second
  rfl

end
end CurrentAFT.PhysicalPolynomialAverages

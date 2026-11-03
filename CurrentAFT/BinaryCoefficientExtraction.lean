import CurrentAFT.BinaryCoefficientDensity
import CurrentAFT.BinaryStoredSymmetrization

/-! Stored-slot joint density extraction, tensor inversion, and exact
symmetrization, implemented by binary arithmetic and full finite sums. -/
namespace CurrentAFT.BinaryCoefficientExtraction
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {totalSlots degree : ℕ}
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def normalized (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  BinaryDensityInverseTensor.current security bits degree output (fun source => BinaryCoefficientDensity.current security bits slots source mass)

def current (security bits : ℕ) (slots : Vector (Fin totalSlots) degree)
    (program : BinaryStoredSymmetrization.Program degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult) : RationalResult :=
  BinaryStoredSymmetrization.current security program output (fun source => normalized security bits slots source mass)

theorem normalized_value (security bits : ℕ) (selected : Finset (Fin 4)) (slots : Vector (Fin 4) selected.card)
    (hslots : ∀ index, slots.get index = ((Finset.orderIsoOfFin selected rfl) index).val)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode = value (fun index => (source.get index).val)) :
    (normalized security bits slots output mass).data.decode =
      RationalCoefficientExtraction.normalized security bits value selected (fun index => (output.get index).val) :=
  BinaryDensityInverseTensor.current_value security bits selected.card output _ _
    (fun source => BinaryCoefficientDensity.current_value security bits selected slots hslots source mass value hmass)

noncomputable section
open scoped Classical

theorem current_value (security bits : ℕ) (selected : Finset (Fin 4)) (slots : Vector (Fin 4) selected.card)
    (hslots : ∀ index, slots.get index = ((Finset.orderIsoOfFin selected rfl) index).val)
    (program : BinaryStoredSymmetrization.Program selected.card)
    (hprogram : program.meaning RationalBits.decode = BinaryStoredSymmetrization.meanSyntax selected.card)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 4 → RationalResult)
    (value : (Fin 4 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode = value (fun index => (source.get index).val)) :
    (current security bits slots program output mass).data.decode =
      RationalCoefficientExtraction.selectedKernel security bits value selected (fun index => (output.get index).val) :=
  BinaryStoredSymmetrization.current_value security program hprogram output _ _
    (fun source => normalized_value security bits selected slots hslots source mass value hmass)

noncomputable def normalizedHeightPolynomial (totalSlots degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseTensor.heightPolynomial degree precision (BinaryCoefficientDensity.heightPolynomial totalSlots degree precision inputBits)
noncomputable def normalizedWorkPolynomial (totalSlots degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseTensor.workPolynomial degree precision (BinaryCoefficientDensity.heightPolynomial totalSlots degree precision inputBits)
    (BinaryCoefficientDensity.workPolynomial totalSlots degree precision inputBits inputWork)
noncomputable def heightPolynomial (totalSlots : ℕ) (program : BinaryStoredSymmetrization.Program degree)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryStoredSymmetrization.heightPolynomial program (normalizedHeightPolynomial totalSlots degree precision inputBits)
noncomputable def workPolynomial (totalSlots : ℕ) (program : BinaryStoredSymmetrization.Program degree)
    (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryStoredSymmetrization.workPolynomial program (normalizedHeightPolynomial totalSlots degree precision inputBits)
    (normalizedWorkPolynomial totalSlots degree precision inputBits inputWork)

theorem normalized_bounds (security : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (slots : Vector (Fin totalSlots) degree) (output : Vector (Fin (colors security)) degree)
    (mass : Vector (Fin (colors security)) totalSlots → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security) :
    HeightBound (normalized security (precision.eval security) slots output mass).data.decode
      ((normalizedHeightPolynomial totalSlots degree precision inputBits).eval security) ∧
      (normalized security (precision.eval security) slots output mass).work ≤
        (normalizedWorkPolynomial totalSlots degree precision inputBits inputWork).eval security :=
  BinaryDensityInverseTensor.current_bounds security degree precision _ _ output _
    (fun source => (BinaryCoefficientDensity.current_bounds security precision inputBits inputWork slots source mass hh hw).1)
    (fun source => (BinaryCoefficientDensity.current_bounds security precision inputBits inputWork slots source mass hh hw).2)

theorem current_bounds (security : ℕ) (precision inputBits inputWork : Polynomial ℕ)
    (slots : Vector (Fin totalSlots) degree) (program : BinaryStoredSymmetrization.Program degree)
    (output : Vector (Fin (colors security)) degree) (mass : Vector (Fin (colors security)) totalSlots → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security) :
    HeightBound (current security (precision.eval security) slots program output mass).data.decode
      ((heightPolynomial totalSlots program precision inputBits).eval security) ∧
      (current security (precision.eval security) slots program output mass).work ≤
        (workPolynomial totalSlots program precision inputBits inputWork).eval security :=
  BinaryStoredSymmetrization.current_bounds security program _ _ output _
    (fun source => (normalized_bounds security precision inputBits inputWork slots source mass hh hw).1)
    (fun source => (normalized_bounds security precision inputBits inputWork slots source mass hh hw).2)

end
end CurrentAFT.BinaryCoefficientExtraction

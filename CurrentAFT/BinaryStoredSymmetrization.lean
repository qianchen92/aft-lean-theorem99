import CurrentAFT.BinaryDensityInverseTensor
import CurrentAFT.FamilyProductSyntax

/-! Symmetrization by a finite stored arithmetic program. This program is
fixed before security; all runtime tuple reads and arithmetic are charged. -/
namespace CurrentAFT.BinaryStoredSymmetrization
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev Slots (degree : ℕ) := Vector (Fin degree) degree
abbrev Program (degree : ℕ) := StoredScalarProgram (Slots degree) RationalBits

def gatherEntry {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree)
    (index : Fin degree) : CountedValue (Fin (BinaryFirstInverseProgram.colors security)) :=
  let position := readVector ⟨0, by have h := index.isLt; omega⟩ slots index
  let result := readVector (BinaryDensityInverseTensor.first security) input position.value
  ⟨result.value,position.work+result.work+1⟩

def gather {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree) :
    CountedValue (Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) :=
  storeData degree (gatherEntry security input slots)

theorem gather_get {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree) (index : Fin degree) :
    (gather security input slots).value.get index = input.get (slots.get index) := by
  simp only [gather, storeData_get, gatherEntry, readVector_value]

theorem gather_work {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree) (slots : Slots degree) :
    (gather security input slots).work ≤ degree*(6*degree+9)+2 := by
  apply storeData_work
  intro index
  have hp := readVector_work (⟨0, by have h := index.isLt; omega⟩ : Fin degree) slots index
  have hv := readVector_work (BinaryDensityInverseTensor.first security) input
    (readVector (⟨0, by have h := index.isLt; omega⟩ : Fin degree) slots index).value
  change _+_+1 ≤ _
  omega

def leaf {degree : ℕ} (security : ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult)
    (slots : Slots degree) : CountedValue RationalBits :=
  let word := gather security input slots
  let value := kernel word.value
  ⟨value.data,word.work+value.work+2⟩

def current {degree : ℕ} (security : ℕ) (program : Program degree)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult) : RationalResult :=
  let value := program.binaryRun (leaf security input kernel)
  ⟨value.value,value.work+1⟩

noncomputable section
open scoped Classical

def meanSyntax (degree : ℕ) : ScalarProgram (Slots degree) :=
  .multiply (.rational (1/(degree.factorial:ℚ)))
    (FamilyProductSyntax.sum (fun permutation : Equiv.Perm (Fin degree) => .atom (Vector.ofFn permutation)))

theorem exists_stored (degree : ℕ) : ∃ program : Program degree,
    program.meaning RationalBits.decode = meanSyntax degree := ScalarProgram.exists_binaryStored (meanSyntax degree)

theorem current_value {degree : ℕ} (security : ℕ) (program : Program degree)
    (hprogram : program.meaning RationalBits.decode = meanSyntax degree)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult)
    (value : (Fin degree → ℕ) → ℚ)
    (hk : ∀ word, (kernel word).data.decode = value (fun index => (word.get index).val)) :
    (current security program input kernel).data.decode =
      (1/(degree.factorial:ℚ))*∑ permutation : Equiv.Perm (Fin degree),
        value ((fun index => (input.get index).val) ∘ permutation) := by
  simp only [current, StoredScalarProgram.binaryRun_value, hprogram, meanSyntax, ScalarProgram.run,
    FamilyProductSyntax.sum_run]
  congr 1
  apply Finset.sum_congr rfl
  intro permutation _
  simp only [leaf, hk]
  congr 1
  funext index
  rw [gather_get, Vector.get_ofFn]
  rfl

noncomputable def heightPolynomial {degree : ℕ} (program : Program degree) (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.heightPolynomial program inputBits
noncomputable def workPolynomial {degree : ℕ} (program : Program degree) (inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.workPolynomial program inputBits (Polynomial.C (degree*(6*degree+9)+4)+inputWork)+1

theorem current_bounds {degree : ℕ} (security : ℕ) (program : Program degree) (inputBits inputWork : Polynomial ℕ)
    (input : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) degree → RationalResult)
    (hh : ∀ word, HeightBound (kernel word).data.decode (inputBits.eval security))
    (hw : ∀ word, (kernel word).work ≤ inputWork.eval security) :
    HeightBound (current security program input kernel).data.decode ((heightPolynomial program inputBits).eval security) ∧
      (current security program input kernel).work ≤ (workPolynomial program inputBits inputWork).eval security := by
  have hl (slots : Slots degree) : HeightBound (leaf security input kernel slots).value.decode (inputBits.eval security) := hh _
  have wl (slots : Slots degree) : (leaf security input kernel slots).work ≤ degree*(6*degree+9)+4+inputWork.eval security := by
    have hg := gather_work security input slots
    have hk := hw (gather security input slots).value
    change _+_+2 ≤ _
    omega
  constructor
  · simpa only [heightPolynomial, BinaryFixedScalarProgram.heightPolynomial_eval] using
      BinaryFixedScalarProgram.run_height program (leaf security input kernel) (inputBits.eval security) hl
  · have h := BinaryFixedScalarProgram.run_work program (leaf security input kernel)
      (inputBits.eval security) (degree*(6*degree+9)+4+inputWork.eval security) hl wl
    change (program.binaryRun _).work+1 ≤ _
    simpa only [workPolynomial, Polynomial.eval_add, Polynomial.eval_one,
      BinaryFixedScalarProgram.workPolynomial_eval, Polynomial.eval_C] using Nat.add_le_add_right h 1

end
end CurrentAFT.BinaryStoredSymmetrization

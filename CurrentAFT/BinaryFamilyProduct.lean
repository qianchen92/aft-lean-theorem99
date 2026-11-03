import CurrentAFT.FamilyProductSyntax
import AFT.BinaryDataArrays

/-! # Executed joint-slot gathers and binary coefficient multiplication -/
namespace CurrentAFT.BinaryFamilyProduct
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev CoefficientProgram (order : ℕ) := (arity : TruncatedArity order) →
  Vector ℕ arity.val.1.val → Vector ℕ arity.val.2.val → CountedValue RationalBits

def gatherEntry {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) (storedSlots : Vector ℕ outputCount)
    (hslots : ∀ index, storedSlots.get index = (slots.get index).val) (index : Fin outputCount) : CountedValue ℕ :=
  let position := readVector 0 storedSlots index
  let output := readVector 0 input ⟨position.value, by rw [readVector_value, hslots]; exact (slots.get index).isLt⟩
  ⟨output.value, position.work + output.work + 1⟩

def gather {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) : CountedValue (Vector ℕ outputCount) :=
  let positions := slots.map Fin.val
  let result := storeData outputCount (gatherEntry input slots positions (by intro index; simp [positions]))
  ⟨result.value, result.work + outputCount + 1⟩

theorem gatherEntry_value {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) (storedSlots : Vector ℕ outputCount)
    (hslots : ∀ index, storedSlots.get index = (slots.get index).val) (index : Fin outputCount) :
    (gatherEntry input slots storedSlots hslots index).value = input.get (slots.get index) := by
  simp only [gatherEntry, readVector_value]
  congr 1
  exact Fin.ext (hslots index)

theorem gather_get {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) (index : Fin outputCount) :
    (gather input slots).value.get index = input.get (slots.get index) := by
  simp only [gather, storeData_get, gatherEntry_value]

theorem gather_work {inputCount outputCount : ℕ} (input : Vector ℕ inputCount)
    (slots : Vector (Fin inputCount) outputCount) :
    (gather input slots).work ≤ outputCount*(3*outputCount+3*inputCount+10)+3 := by
  have he (index : Fin outputCount) :
      (gatherEntry input slots (slots.map Fin.val) (by intro index; simp) index).work ≤
        3*outputCount+3*inputCount+7 := by
    have hp := readVector_work 0 (slots.map Fin.val) index
    have hv := readVector_work 0 input (⟨(readVector 0 (slots.map Fin.val) index).value, by
      rw [readVector_value, Vector.get_map]; exact (slots.get index).isLt⟩ : Fin inputCount)
    simp only [gatherEntry]
    omega
  have hs := storeData_work outputCount (3*outputCount+3*inputCount+7) _ he
  simp only [gather]
  nlinarith

def leaf (order : ℕ) (output : TruncatedArity order) (first second : CoefficientProgram order)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (code : FamilyProductSyntax.Leaf order output) : CountedValue RationalBits :=
  let primary := gather colors code.primarySlots
  let body := gather centers code.bodySlots
  let result := (if code.second then second else first) code.arity primary.value body.value
  ⟨result.value, primary.work + body.work + result.work + 3⟩

def run (order : ℕ) (output : TruncatedArity order)
    (stored : StoredScalarProgram (FamilyProductSyntax.Leaf order output) RationalBits)
    (first second : CoefficientProgram order)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val) : CountedValue RationalBits :=
  stored.binaryRun (leaf order output first second colors centers)

theorem leaf_value (order : ℕ) (output : TruncatedArity order) (first second : CoefficientProgram order)
    (firstTable secondTable : Table ℚ ℕ ℕ order)
    (hfirst : ∀ arity colors centers, (first arity colors centers).value.decode = firstTable arity colors.get centers.get)
    (hsecond : ∀ arity colors centers, (second arity colors centers).value.decode = secondTable arity colors.get centers.get)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (code : FamilyProductSyntax.Leaf order output) :
    (leaf order output first second colors centers code).value.decode =
      FamilyProductSyntax.value order output firstTable secondTable colors.get centers.get code := by
  unfold leaf FamilyProductSyntax.value
  cases code.second <;> simp only [Bool.false_eq_true, if_false, if_true, hfirst, hsecond]
  all_goals congr 1 <;> funext index <;> exact gather_get _ _ index

noncomputable section
open scoped Classical

theorem run_value (order : ℕ) (output : TruncatedArity order)
    (stored : StoredScalarProgram (FamilyProductSyntax.Leaf order output) RationalBits)
    (hstored : stored.meaning RationalBits.decode = FamilyProductSyntax.product order output)
    (first second : CoefficientProgram order) (firstTable secondTable : Table ℚ ℕ ℕ order)
    (hfirst : ∀ arity colors centers, (first arity colors centers).value.decode = firstTable arity colors.get centers.get)
    (hsecond : ∀ arity colors centers, (second arity colors centers).value.decode = secondTable arity colors.get centers.get)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val) :
    (run order output stored first second colors centers).value.decode =
      product order firstTable secondTable output colors.get centers.get := by
  unfold run
  rw [StoredScalarProgram.binaryRun_value, hstored]
  have he : (fun code => (leaf order output first second colors centers code).value.decode) =
      FamilyProductSyntax.value order output firstTable secondTable colors.get centers.get :=
    funext (leaf_value order output first second firstTable secondTable hfirst hsecond colors centers)
  rw [he, FamilyProductSyntax.product_run]

def leafWork (order kernelWork : ℕ) : ℕ := 2*order*(6*order+10)+kernelWork+9

theorem leaf_bounds (order base bits budget : ℕ) (output : TruncatedArity order)
    (first second : CoefficientProgram order)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (first arity colors centers).value.decode bits ∧ (first arity colors centers).work ≤ budget)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (second arity colors centers).value.decode bits ∧ (second arity colors centers).work ≤ budget)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base)
    (code : FamilyProductSyntax.Leaf order output) :
    HeightBound (leaf order output first second colors centers code).value.decode bits ∧
      (leaf order output first second colors centers code).work ≤ leafWork order budget := by
  have hp : ∀ i, (gather colors code.primarySlots).value.get i < base := by
    intro i; rw [gather_get]; exact hcolors _
  have hb : ∀ i, (gather centers code.bodySlots).value.get i < base := by
    intro i; rw [gather_get]; exact hcenters _
  have hk : HeightBound ((if code.second then second else first) code.arity
      (gather colors code.primarySlots).value (gather centers code.bodySlots).value).value.decode bits ∧
      ((if code.second then second else first) code.arity
        (gather colors code.primarySlots).value (gather centers code.bodySlots).value).work ≤ budget := by
    split_ifs
    · exact hsecond _ _ _ hp hb
    · exact hfirst _ _ _ hp hb
  have hi := output.property
  have ho := code.arity.property
  have hgp : (gather colors code.primarySlots).work ≤ order*(6*order+10)+3 := by
    apply (gather_work colors code.primarySlots).trans
    gcongr <;> omega
  have hgb : (gather centers code.bodySlots).work ≤ order*(6*order+10)+3 := by
    apply (gather_work centers code.bodySlots).trans
    gcongr <;> omega
  refine ⟨hk.1, ?_⟩
  change (gather colors code.primarySlots).work + (gather centers code.bodySlots).work + _ + 3 ≤ _
  unfold leafWork
  nlinarith [hk.2]

theorem run_bounds (order base bits budget : ℕ) (output : TruncatedArity order)
    (stored : StoredScalarProgram (FamilyProductSyntax.Leaf order output) RationalBits)
    (first second : CoefficientProgram order)
    (hfirst : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (first arity colors centers).value.decode bits ∧ (first arity colors centers).work ≤ budget)
    (hsecond : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (second arity colors centers).value.decode bits ∧ (second arity colors centers).work ≤ budget)
    (colors : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (run order output stored first second colors centers).value.decode
        (BinaryFixedScalarProgram.height stored bits) ∧
      (run order output stored first second colors centers).work ≤
        BinaryFixedScalarProgram.work stored bits (leafWork order budget) := by
  have h := leaf_bounds order base bits budget output first second hfirst hsecond colors centers hcolors hcenters
  exact ⟨BinaryFixedScalarProgram.run_height stored _ bits (fun code => (h code).1),
    BinaryFixedScalarProgram.run_work stored _ bits (leafWork order budget) (fun code => (h code).1) (fun code => (h code).2)⟩

end
end CurrentAFT.BinaryFamilyProduct

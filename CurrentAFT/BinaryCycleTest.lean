import CurrentAFT.BinarySparseCycleEvaluation
import CurrentAFT.CurrentCycleEntryProgram
import CurrentAFT.BinaryProposalGuard
import AFT.BinarySignedComparison
import AFT.BinaryIntegerDivision

/-! Modular point indicators and centered products for sparse cycle tests.
The equality test uses Euclidean binary residue and two signed comparisons. -/
namespace CurrentAFT.BinaryCycleTest
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def equalResidue (modulus : List Bool) (root : IntegerBits) (output : ℕ) : CountedValue Bool :=
  let residue := IntegerBits.residue root modulus
  let expected := canonicalCounter output
  let first := signedLe false false residue.digits expected.digits
  let second := signedLe false false expected.digits residue.digits
  ⟨first.value && second.value,residue.work+expected.work+first.work+second.work+4⟩

 theorem equalResidue_value (modulus : List Bool) (hq : 0 < value modulus) (root : IntegerBits) (output : ℕ) :
    (equalResidue modulus root output).value = true ↔ root.decode % (value modulus : ℤ) = (output : ℤ) := by
  have hr := IntegerBits.residue_value root modulus hq
  simp only [equalResidue,Bool.and_eq_true,signedLe_value,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]
  rw [hr]
  constructor
  · rintro ⟨hf,hs⟩
    exact le_antisymm hf hs
  · intro he
    rw [he]
    exact ⟨le_rfl,le_rfl⟩

 theorem equalResidue_work (modulus : List Bool) (root : IntegerBits) (output rootBits modulusBits outputBound : ℕ)
    (hr : root.digits.length ≤ rootBits) (hm : modulus.length ≤ modulusBits) (ho : output ≤ outputBound) :
    (equalResidue modulus root output).work ≤
      60*(rootBits+modulusBits+1)^2+50*(outputBound+1)^2+48*(rootBits+modulusBits+outputBound)+50 := by
  have hres := IntegerBits.residue_work root modulus
  have hlen := IntegerBits.residue_length root modulus
  have he := canonicalCounter_work output
  have hel : (canonicalCounter output).digits.length ≤ outputBound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output))).trans ho
  have hf := signedLe_work false false (IntegerBits.residue root modulus).digits (canonicalCounter output).digits
  have hs := signedLe_work false false (canonicalCounter output).digits (IntegerBits.residue root modulus).digits
  have hq : 60*(root.digits.length+modulus.length+1)^2 ≤ 60*(rootBits+modulusBits+1)^2 := by gcongr
  have heq : 50*(output+1)^2 ≤ 50*(outputBound+1)^2 := by gcongr
  change (IntegerBits.residue root modulus).work+(canonicalCounter output).work+
    (signedLe false false _ _).work+(signedLe false false _ _).work+4 ≤ _
  omega


def point {count : ℕ} (modulus : List Bool) (output : Vector ℕ count) (roots : Vector IntegerBits count) : RationalResult :=
  let test := BinaryProposalGuard.allFin count (fun slot =>
    let root := readVector IntegerBits.zero roots slot
    let expected := readVector 0 output slot
    let checked := equalResidue modulus root.value expected.value
    ⟨checked.value,root.work+expected.work+checked.work+3⟩)
  ⟨if test.value then RationalBits.one else RationalBits.zero,test.work+2⟩

 theorem point_value {count : ℕ} (modulus : List Bool) (hq : 0 < value modulus)
    (output : Vector ℕ count) (roots : Vector IntegerBits count) :
    (point modulus output roots).data.decode =
      CurrentCycleEntryProgram.pointTest (value modulus) count output.get (fun slot => (roots.get slot).decode) := by
  have ht : (BinaryProposalGuard.allFin count (fun slot =>
    let root := readVector IntegerBits.zero roots slot
    let expected := readVector 0 output slot
    let checked := equalResidue modulus root.value expected.value
    (⟨checked.value,root.work+expected.work+checked.work+3⟩ : CountedValue Bool))).value = true ↔
      ∀ slot, (roots.get slot).decode % (value modulus : ℤ) = (output.get slot : ℤ) := by
    simp only [BinaryProposalGuard.allFin_value,equalResidue_value modulus hq,readVector_value]
  unfold point CurrentCycleEntryProgram.pointTest
  dsimp only
  by_cases h : ∀ slot, (roots.get slot).decode % (value modulus : ℤ) = (output.get slot : ℤ)
  · rw [if_pos (ht.mpr h),if_pos h,RationalBits.one_value]
  · rw [if_neg (fun hh => h (ht.mp hh)),if_neg h,RationalBits.zero_value]


def centeredFactor {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count) (slot : Fin count) : RationalResult :=
  let root := readVector IntegerBits.zero roots slot
  let expected := readVector 0 output slot
  let mass := readVector RationalBits.zero reference slot
  let checked := equalResidue modulus root.value expected.value
  let negative := RationalBits.negate mass.value
  let result := RationalBits.add (if checked.value then RationalBits.one else RationalBits.zero) negative.data
  ⟨result.data,root.work+expected.work+mass.work+checked.work+negative.work+result.work+6⟩

 theorem centeredFactor_value {count : ℕ} (modulus : List Bool) (hq : 0 < value modulus)
    (output : Vector ℕ count) (reference : Vector RationalBits count) (roots : Vector IntegerBits count) (slot : Fin count) :
    (centeredFactor modulus output reference roots slot).data.decode =
      (if (roots.get slot).decode % (value modulus : ℤ) = (output.get slot : ℤ) then 1 else 0) - (reference.get slot).decode := by
  have ht := equalResidue_value modulus hq (readVector IntegerBits.zero roots slot).value (readVector 0 output slot).value
  simp only [readVector_value] at ht
  simp only [centeredFactor,RationalBits.add_value,RationalBits.negate_value,readVector_value,sub_eq_add_neg]
  by_cases h : (roots.get slot).decode % (value modulus : ℤ) = (output.get slot : ℤ)
  · rw [if_pos (ht.mpr h),if_pos h,RationalBits.one_value]
  · rw [if_neg (fun hh => h (ht.mp hh)),if_neg h,RationalBits.zero_value]


def signed {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count) : RationalResult :=
  BinaryFiniteProduct.current count (centeredFactor modulus output reference roots)

 theorem signed_value {count : ℕ} (modulus : List Bool) (hq : 0 < value modulus)
    (output : Vector ℕ count) (reference : Vector RationalBits count) (roots : Vector IntegerBits count) :
    (signed modulus output reference roots).data.decode =
      ∏ slot, ((if (roots.get slot).decode % (value modulus : ℤ) = (output.get slot : ℤ) then 1 else 0) - (reference.get slot).decode) := by
  simp only [signed,BinaryFiniteProduct.current_value,centeredFactor_value modulus hq]

end CurrentAFT.BinaryCycleTest

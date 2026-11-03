import CurrentAFT.BinaryCycleTest

/-! Explicit binary costs and heights for modular cycle point and centered tests. -/
namespace CurrentAFT.BinaryCycleTestResources
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics BinaryCycleTest
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def matchWork (rootBits modulusBits outputBound : ℕ) : ℕ :=
  60*(rootBits+modulusBits+1)^2+50*(outputBound+1)^2+48*(rootBits+modulusBits+outputBound)+50


def pointWork (count rootBits modulusBits outputBound : ℕ) : ℕ :=
  count*(6*count+matchWork rootBits modulusBits outputBound+11)+3

 theorem point_bounds {count : ℕ} (modulus : List Bool) (output : Vector ℕ count) (roots : Vector IntegerBits count)
    (rootBits modulusBits outputBound : ℕ) (hr : ∀ slot, (roots.get slot).digits.length ≤ rootBits)
    (hm : modulus.length ≤ modulusBits) (ho : ∀ slot, output.get slot ≤ outputBound) :
    HeightBound (point modulus output roots).data.decode 0 ∧
      (point modulus output roots).work ≤ pointWork count rootBits modulusBits outputBound := by
  constructor
  · change HeightBound (if _ then RationalBits.one else RationalBits.zero).decode 0
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  · have htest := BinaryProposalGuard.allFin_work count (6*count+matchWork rootBits modulusBits outputBound+9)
      (fun slot =>
        let root := readVector IntegerBits.zero roots slot
        let expected := readVector 0 output slot
        let checked := equalResidue modulus root.value expected.value
        (⟨checked.value,root.work+expected.work+checked.work+3⟩ : CountedValue Bool)) (by
          intro slot
          have hroot := readVector_work IntegerBits.zero roots slot
          have hexpected := readVector_work 0 output slot
          have hchecked := equalResidue_work modulus (readVector IntegerBits.zero roots slot).value
            (readVector 0 output slot).value rootBits modulusBits outputBound
            (by rw [readVector_value]; exact hr slot) hm (by rw [readVector_value];exact ho slot)
          change _+_+_+3 ≤ _
          unfold matchWork
          omega)
    change (BinaryProposalGuard.allFin _ _).work+2 ≤ _
    unfold pointWork
    norm_num only [Nat.add_assoc] at htest ⊢
    omega


def factorWork (count rootBits modulusBits outputBound height : ℕ) : ℕ :=
  9*count+matchWork rootBits modulusBits outputBound+2*RationalBits.primitiveWorkBound (height+1)+20

 theorem centeredFactor_bounds {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count)
    (rootBits modulusBits outputBound height : ℕ) (hr : ∀ slot, (roots.get slot).digits.length ≤ rootBits)
    (hm : modulus.length ≤ modulusBits) (ho : ∀ slot, output.get slot ≤ outputBound)
    (hreference : ∀ slot, HeightBound (reference.get slot).decode height) (slot : Fin count) :
    HeightBound (centeredFactor modulus output reference roots slot).data.decode (height+1) ∧
      (centeredFactor modulus output reference roots slot).work ≤ factorWork count rootBits modulusBits outputBound height := by
  let root := readVector IntegerBits.zero roots slot
  let expected := readVector 0 output slot
  let mass := readVector RationalBits.zero reference slot
  let checked := equalResidue modulus root.value expected.value
  let indicator := if checked.value then RationalBits.one else RationalBits.zero
  let negative := RationalBits.negate mass.value
  have hi : HeightBound indicator.decode 0 := by
    dsimp only [indicator]
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  have href : HeightBound mass.value.decode height := by rw [readVector_value];exact hreference slot
  have hn : HeightBound negative.data.decode height := by rw [RationalBits.negate_value];exact href.neg
  have hsum := hi.add hn
  have hneg := RationalBits.negate_work mass.value (height+1)
  have hadd := RationalBits.add_work indicator negative.data (height+1)
    (hi.mono (Nat.zero_le _)) (hn.mono (by omega))
  have hroot := readVector_work IntegerBits.zero roots slot
  have hexpected := readVector_work 0 output slot
  have hmass := readVector_work RationalBits.zero reference slot
  have hchecked := equalResidue_work modulus root.value expected.value rootBits modulusBits outputBound
    (by rw [readVector_value];exact hr slot) hm (by rw [readVector_value];exact ho slot)
  constructor
  · change HeightBound (RationalBits.add indicator negative.data).data.decode (height+1)
    rw [RationalBits.add_value]
    simpa only [Nat.zero_add] using hsum
  · change root.work+expected.work+mass.work+checked.work+negative.work+(RationalBits.add indicator negative.data).work+6 ≤ _
    change root.work ≤ _ at hroot
    change expected.work ≤ _ at hexpected
    change mass.work ≤ _ at hmass
    change checked.work ≤ _ at hchecked
    change negative.work ≤ _ at hneg
    unfold factorWork matchWork
    omega

 theorem signed_bounds {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count)
    (rootBits modulusBits outputBound height : ℕ) (hr : ∀ slot, (roots.get slot).digits.length ≤ rootBits)
    (hm : modulus.length ≤ modulusBits) (ho : ∀ slot, output.get slot ≤ outputBound)
    (hreference : ∀ slot, HeightBound (reference.get slot).decode height) :
    HeightBound (signed modulus output reference roots).data.decode (count*(height+1)) ∧
      (signed modulus output reference roots).work ≤
        BinaryFiniteProduct.work count (height+1) (factorWork count rootBits modulusBits outputBound height) := by
  have h := centeredFactor_bounds modulus output reference roots rootBits modulusBits outputBound height hr hm ho hreference
  exact ⟨BinaryFiniteProduct.current_height count (height+1) _ (fun slot => (h slot).1),
    BinaryFiniteProduct.current_work count (height+1) _ _ (fun slot => (h slot).1) (fun slot => (h slot).2)⟩

end CurrentAFT.BinaryCycleTestResources

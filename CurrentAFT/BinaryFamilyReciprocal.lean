import CurrentAFT.BinaryFamilyPower
import AFT.BinaryChartProjectionCost

/-! # Binary evaluation of the fixed finite reciprocal -/
namespace CurrentAFT.BinaryFamilyReciprocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def complement (order : ℕ) (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let first := BinaryFamilyPower.unit order arity colors centers
    let second := table arity colors centers
    let result := difference first.value second.value
    ⟨result.data, first.work + second.work + result.work + 2⟩

def current (order : ℕ) (programs : List (Entry order)) (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin (order+1) (fun count =>
      let term := BinaryFamilyPower.power order programs (complement order table) count.val arity colors centers
      ⟨term.value, term.work+1⟩)
    ⟨result.data, result.work+1⟩

theorem complement_value (order : ℕ) (table : CoefficientProgram order)
    (actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (table arity colors centers).value.decode = actual arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (complement order table arity colors centers).value.decode =
      (RationalFamilyProductProgram.unit order - actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) arity colors.get centers.get := by
  simp only [complement, difference_value, BinaryFamilyPower.unit_value, hvalue]
  rfl

noncomputable section
open scoped Classical

theorem current_value (order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (table arity colors centers).value.decode = actual arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current order programs table arity colors centers).value.decode =
      RationalFamilyProductProgram.reciprocal order actual arity colors.get centers.get := by
  simp only [current, sumFin_value]
  simp_rw [BinaryFamilyPower.power_value order programs hcorrect hcomplete (complement order table)
    (RationalFamilyProductProgram.unit order - actual) (complement_value order table actual hvalue)]
  exact Fin.sum_univ_eq_sum_range (fun count =>
    RationalFamilyProductProgram.power order (RationalFamilyProductProgram.unit order - actual)
      count arity colors.get centers.get) (order+1)

noncomputable def complementWork (order : ℕ) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+10) + budget + 2 * BinaryCalibrationIteration.primitivePolynomial bits

theorem complement_bounds (order base security : ℕ) (table : CoefficientProgram order)
    (bits budget : Polynomial ℕ)
    (htable : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (table arity colors centers).value.decode (bits.eval security) ∧
        (table arity colors centers).work ≤ budget.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (complement order table arity colors centers).value.decode ((bits+1).eval security) ∧
      (complement order table arity colors centers).work ≤ (complementWork order bits budget).eval security := by
  have hu := BinaryFamilyPower.unit_bounds order arity colors centers
  have ht := htable arity colors centers hcolors hcenters
  constructor
  · simp only [complement, difference_value, Polynomial.eval_add, Polynomial.eval_one]
    have hs := hu.1.add ht.1.neg
    simpa only [zero_add, sub_eq_add_neg] using hs
  · have hd := difference_work (BinaryFamilyPower.unit order arity colors centers).value
      (table arity colors centers).value (bits.eval security) (hu.1.mono (Nat.zero_le _)) ht.1
    change (BinaryFamilyPower.unit order arity colors centers).work +
      (table arity colors centers).work +
      (difference (BinaryFamilyPower.unit order arity colors centers).value (table arity colors centers).value).work + 2 ≤ _
    simp only [complementWork, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_ofNat, BinaryCalibrationIteration.primitivePolynomial, Polynomial.eval_pow]
    unfold primitiveWorkBound at hd
    omega

noncomputable def heightSum (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.heightPolynomial order programs (bits+1) count.val

noncomputable def workSum (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.workPolynomial order programs (bits+1)
    (complementWork order bits budget) count.val

noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1) * (heightSum order programs bits + 1)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1) * (workSum order programs bits budget +
    BinaryCalibrationIteration.primitivePolynomial (Polynomial.C (order+2) * (heightSum order programs bits + 1)) + 3) + 3

theorem polynomial_bounds (order base security : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (bits budget : Polynomial ℕ)
    (htable : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (table arity colors centers).value.decode (bits.eval security) ∧
        (table arity colors centers).work ≤ budget.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (current order programs table arity colors centers).value.decode
        ((heightPolynomial order programs bits).eval security) ∧
      (current order programs table arity colors centers).work ≤
        (workPolynomial order programs bits budget).eval security := by
  let term := fun count : Fin (order+1) =>
    BinaryFamilyPower.power order programs (complement order table) count.val arity colors centers
  have ht (count : Fin (order+1)) := BinaryFamilyPower.polynomial_bounds order base security programs
    (complement order table) (bits+1) (complementWork order bits budget)
    (complement_bounds order base security table bits budget htable) count.val arity colors centers hcolors hcenters
  have hh (count : Fin (order+1)) : HeightBound (term count).value.decode
      ((heightSum order programs bits).eval security) := by
    apply (ht count).1.mono
    rw [heightSum, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun i : Fin (order+1) =>
      (BinaryFamilyPower.heightPolynomial order programs (bits+1) i.val).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ count)
  have hw (count : Fin (order+1)) : (term count).work ≤ (workSum order programs bits budget).eval security := by
    apply (ht count).2.trans
    rw [workSum, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun i : Fin (order+1) =>
      (BinaryFamilyPower.workPolynomial order programs (bits+1) (complementWork order bits budget) i.val).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ count)
  let entries := fun count : Fin (order+1) => (⟨(term count).value, (term count).work+1⟩ : RationalResult)
  have hheight := sumFin_height (order+1) ((heightSum order programs bits).eval security) entries hh
  have hwork := sumFin_work (order+1) ((heightSum order programs bits).eval security)
    ((workSum order programs bits budget).eval security+1) entries hh
    (fun count => Nat.add_le_add_right (hw count) 1)
  constructor
  · simpa only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one] using hheight
  · change (sumFin (order+1) entries).work + 1 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_one, BinaryCalibrationIteration.primitivePolynomial, Polynomial.eval_pow]
    unfold primitiveWorkBound at hwork
    have he : order+1+1 = order+2 := by omega
    rw [he] at hwork
    have ha : (workSum order programs bits budget).eval security+1+
        10000000*((order+2)*((heightSum order programs bits).eval security+1)+2)^3+2 =
      (workSum order programs bits budget).eval security+
        10000000*((order+2)*((heightSum order programs bits).eval security+1)+2)^3+3 := by omega
    rw [ha] at hwork
    omega

end
end CurrentAFT.BinaryFamilyReciprocal

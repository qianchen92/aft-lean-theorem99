import CurrentAFT.BinaryFamilyReciprocal
import CurrentAFT.BinaryBinomialCoefficient

/-! # Binary truncated population powers

The population enters only the computed binomial coefficients. The number of
family multiplications depends on the fixed calibration order.
-/
namespace CurrentAFT.BinaryFamilyBinomial
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def term (order population : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (count : ℕ) : CoefficientProgram order :=
  fun arity colors centers =>
    let coefficient := BinaryBinomialCoefficient.current population count
    let value := BinaryFamilyPower.power order programs table count arity colors centers
    let result := multiply coefficient.data value.value
    ⟨result.data, coefficient.work+value.work+result.work+3⟩

def current (order population : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin (order+1) (fun count =>
      let value := term order population programs table count.val arity colors centers
      ⟨value.value, value.work+1⟩)
    ⟨result.data, result.work+1⟩

noncomputable section
open scoped Classical

theorem current_value (order population : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (table : CoefficientProgram order) (actual : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ arity colors centers, (table arity colors centers).value.decode = actual arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current order population programs table arity colors centers).value.decode =
      RationalFamilyProductProgram.binomial order population actual arity colors.get centers.get := by
  simp only [current, sumFin_value, term, RationalBits.multiply_value, BinaryBinomialCoefficient.current_value,
    BinaryFamilyPower.power_value order programs hcorrect hcomplete table actual hvalue]
  exact Fin.sum_univ_eq_sum_range (fun count => (population.choose count : ℚ) *
    RationalFamilyProductProgram.power order actual count arity colors.get centers.get) (order+1)

def powerHeightSum (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.heightPolynomial order programs bits count.val

def powerWorkSum (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.workPolynomial order programs bits budget count.val

def termHeight (order : ℕ) (programs : List (Entry order)) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBinomialCoefficient.heightPolynomial order population + powerHeightSum order programs bits

def termWork (order : ℕ) (programs : List (Entry order)) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBinomialCoefficient.workPolynomial order population + powerWorkSum order programs bits budget +
    BinaryCalibrationIteration.primitivePolynomial (termHeight order programs population bits)+3

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(termHeight order programs population bits+1)

def workPolynomial (order : ℕ) (programs : List (Entry order)) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(termWork order programs population bits budget +
    BinaryCalibrationIteration.primitivePolynomial (Polynomial.C (order+2)*(termHeight order programs population bits+1))+3)+3

theorem term_bounds (order population base security : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (P bits budget : Polynomial ℕ) (hP : population ≤ P.eval security)
    (htable : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (table arity colors centers).value.decode (bits.eval security) ∧
        (table arity colors centers).work ≤ budget.eval security)
    (count : Fin (order+1)) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (term order population programs table count.val arity colors centers).value.decode
        ((termHeight order programs P bits).eval security) ∧
      (term order population programs table count.val arity colors centers).work ≤
        (termWork order programs P bits budget).eval security := by
  have hc := BinaryBinomialCoefficient.polynomial_bounds order population count.val security (by omega) P hP
  have hp := BinaryFamilyPower.polynomial_bounds order base security programs table bits budget htable
    count.val arity colors centers hcolors hcenters
  have hh : (BinaryFamilyPower.heightPolynomial order programs bits count.val).eval security ≤
      (powerHeightSum order programs bits).eval security := by
    rw [powerHeightSum, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun i : Fin (order+1) =>
      (BinaryFamilyPower.heightPolynomial order programs bits i.val).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ count)
  have hw : (BinaryFamilyPower.workPolynomial order programs bits budget count.val).eval security ≤
      (powerWorkSum order programs bits budget).eval security := by
    rw [powerWorkSum, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun i : Fin (order+1) =>
      (BinaryFamilyPower.workPolynomial order programs bits budget i.val).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ count)
  have hch : (BinaryBinomialCoefficient.heightPolynomial order P).eval security ≤
      (termHeight order programs P bits).eval security := by
    simp only [termHeight, Polynomial.eval_add]; omega
  have hph : (BinaryFamilyPower.heightPolynomial order programs bits count.val).eval security ≤
      (termHeight order programs P bits).eval security := by
    simp only [termHeight, Polynomial.eval_add]; omega
  have hm := multiply_work (BinaryBinomialCoefficient.current population count.val).data
    (BinaryFamilyPower.power order programs table count.val arity colors centers).value
    ((termHeight order programs P bits).eval security) (hc.1.mono hch) (hp.1.mono hph)
  constructor
  · simp only [term, RationalBits.multiply_value, termHeight, Polynomial.eval_add]
    exact (hc.1.mul hp.1).mono (Nat.add_le_add_left hh _)
  · change (BinaryBinomialCoefficient.current population count.val).work +
      (BinaryFamilyPower.power order programs table count.val arity colors centers).work +
      (multiply (BinaryBinomialCoefficient.current population count.val).data
        (BinaryFamilyPower.power order programs table count.val arity colors centers).value).work+3 ≤ _
    have hm' : (BinaryCalibrationIteration.primitivePolynomial (termHeight order programs P bits)).eval security =
        primitiveWorkBound ((termHeight order programs P bits).eval security) := by
      simp only [BinaryCalibrationIteration.primitivePolynomial, primitiveWorkBound,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_ofNat]
    simp only [termWork, Polynomial.eval_add, Polynomial.eval_ofNat, hm']
    omega

theorem polynomial_bounds (order population base security : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (P bits budget : Polynomial ℕ) (hP : population ≤ P.eval security)
    (htable : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (table arity colors centers).value.decode (bits.eval security) ∧
        (table arity colors centers).work ≤ budget.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (current order population programs table arity colors centers).value.decode
        ((heightPolynomial order programs P bits).eval security) ∧
      (current order population programs table arity colors centers).work ≤
        (workPolynomial order programs P bits budget).eval security := by
  let entries := fun count : Fin (order+1) =>
    let value := term order population programs table count.val arity colors centers
    (⟨value.value, value.work+1⟩ : RationalResult)
  have ht (count : Fin (order+1)) := term_bounds order population base security programs table P bits budget hP htable
    count arity colors centers hcolors hcenters
  have hh := sumFin_height (order+1) ((termHeight order programs P bits).eval security) entries (fun count => (ht count).1)
  have hw := sumFin_work (order+1) ((termHeight order programs P bits).eval security)
    ((termWork order programs P bits budget).eval security+1) entries (fun count => (ht count).1)
    (fun count => Nat.add_le_add_right (ht count).2 1)
  constructor
  · simpa only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one] using hh
  · change (sumFin (order+1) entries).work+1 ≤ _
    simp only [workPolynomial, BinaryCalibrationIteration.primitivePolynomial, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold primitiveWorkBound at hw
    have he : order+1+1 = order+2 := by omega
    rw [he] at hw
    have ha : (termWork order programs P bits budget).eval security+1+
        10000000*((order+2)*((termHeight order programs P bits).eval security+1)+2)^3+2 =
      (termWork order programs P bits budget).eval security+
        10000000*((order+2)*((termHeight order programs P bits).eval security+1)+2)^3+3 := by omega
    rw [ha] at hw
    omega

end
end CurrentAFT.BinaryFamilyBinomial

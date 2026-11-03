import CurrentAFT.BinaryShiftedSafeProfile
import CurrentAFT.BinarySeedDensityFormula
import CurrentAFT.BinaryUnsafeArray
import CurrentAFT.RationalBackgroundDensities

/-! # The original mixed translation body density from generated binary inputs -/
namespace CurrentAFT.BinaryBackgroundSeed
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryUnsafeArray.current BinaryShiftedSafeProfile.current
  BinarySafeProfile.current BinaryReferenceTables.current BinarySeedDensityFormula.current

def current (security bits : ℕ) (shift : IntegerBits) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let cache := BinaryUnsafeArray.current security shift
  let shifted := BinaryShiftedSafeProfile.current security shift code.digits
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security bits
  let fringe := readVector zero cache.profile output
  let center := readVector zero reference.center output
  let result := BinarySeedDensityFormula.current shifted.data fringe.value cache.total safe.data center.value
  ⟨result.data,code.work+cache.work+shifted.work+safe.work+reference.work+fringe.work+center.work+result.work+8⟩

theorem current_value (security bits : ℕ) (shift : IntegerBits) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits shift output).data.decode=RationalBackgroundDensities.seed security bits shift.decode output.val := by
  simp only [current,BinarySeedDensityFormula.current_value,readVector_value,BinaryUnsafeArray.profile_value,
    BinaryUnsafeArray.total_value,BinaryShiftedSafeProfile.current_value,BinarySafeProfile.current_value,
    canonicalCounter_value,BinaryReferenceTables.center_value,RationalBackgroundDensities.seed,
    RationalBackgroundProfiles.seedProfile,RationalBackgroundProfiles.projected]

noncomputable section
noncomputable def operandHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.heightPolynomial shiftBits+
    BinaryShiftedSafeProfile.heightPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+
    BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.heightPolynomial precision
noncomputable def heightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedDensityFormula.heightPolynomial (operandHeightPolynomial precision shiftBits)
noncomputable def workPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnsafeArray.workPolynomial shiftBits+
    BinaryShiftedSafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+
    BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.currentWorkPolynomial precision+6*BinaryFirstInverseProgram.colorsPolynomial+
    BinarySeedDensityFormula.workPolynomial (operandHeightPolynomial precision shiftBits)+14

theorem current_bounds (security : ℕ) (precision shiftBits : Polynomial ℕ) (shift : IntegerBits)
    (hs : shift.digits.length ≤ shiftBits.eval security) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) shift output).data.decode ((heightPolynomial precision shiftBits).eval security) ∧
      (current security (precision.eval security) shift output).work≤(workPolynomial precision shiftBits).eval security := by
  let code := canonicalCounter output.val
  let cache := BinaryUnsafeArray.current security shift
  let shifted := BinaryShiftedSafeProfile.current security shift code.digits
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let fringe := readVector zero cache.profile output
  let center := readVector zero reference.center output
  let H := (operandHeightPolynomial precision shiftBits).eval security
  have hq := BinaryFirstInverseProgram.colors_bound security
  have ho := output.isLt.le.trans hq
  have hl : code.digits.length≤BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have hc := BinaryUnsafeArray.current_bounds security shift shiftBits hs
  have hshift := BinaryShiftedSafeProfile.current_bounds security shift code.digits shiftBits BinaryFirstInverseProgram.colorsPolynomial hs hl
  have hsafe := BinarySafeProfile.current_bounds security code.digits BinaryFirstInverseProgram.colorsPolynomial hl
  have hr := BinaryReferenceTables.current_bounds security precision
  have hH : H=(BinaryUnsafeArray.heightPolynomial shiftBits).eval security+
      (BinaryShiftedSafeProfile.heightPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinaryReferenceTables.heightPolynomial precision).eval security := by
    simp only [H,operandHeightPolynomial,Polynomial.eval_add]
  have hfringe : HeightBound fringe.value.decode H := by
    rw [readVector_value]
    exact (hc.1 output).mono (by rw [hH]; omega)
  have hcenter : HeightBound center.value.decode H := by
    rw [readVector_value]
    exact (hr.2.1 output).mono (by rw [hH]; omega)
  have hf := BinarySeedDensityFormula.current_bounds shifted.data fringe.value cache.total safe.data center.value H
    (hshift.1.mono (by rw [hH]; omega)) hfringe (hc.2.1.mono (by rw [hH]; omega))
    (hsafe.1.mono (by rw [hH]; omega)) hcenter
  have wc := (canonicalCounter_work output.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  change code.work≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 at wc
  have wcache : cache.work≤(BinaryUnsafeArray.workPolynomial shiftBits).eval security := hc.2.2
  have wshift : shifted.work≤(BinaryShiftedSafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial).eval security := hshift.2
  have wsafe : safe.work≤(BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security := hsafe.2
  have wreference : reference.work≤(BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  have wfringe := readVector_work zero cache.profile output
  have wcenter := readVector_work zero reference.center output
  change fringe.work≤3*BinaryFirstInverseProgram.colors security+3 at wfringe
  change center.work≤3*BinaryFirstInverseProgram.colors security+3 at wcenter
  constructor
  · change HeightBound (BinarySeedDensityFormula.current _ _ _ _ _).data.decode _
    rw [heightPolynomial,BinarySeedDensityFormula.heightPolynomial_eval]
    exact hf.1
  · change code.work+cache.work+shifted.work+safe.work+reference.work+fringe.work+center.work+
      (BinarySeedDensityFormula.current shifted.data fringe.value cache.total safe.data center.value).work+8≤_
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,BinarySeedDensityFormula.workPolynomial_eval]
    change _≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
      (BinaryUnsafeArray.workPolynomial shiftBits).eval security+
      (BinaryShiftedSafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinaryReferenceTables.currentWorkPolynomial precision).eval security+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+
      BinarySeedDensityFormula.work H+14
    omega

end
end CurrentAFT.BinaryBackgroundSeed

import CurrentAFT.BinaryMassLiftKernel
import CurrentAFT.BinaryProfileTables
import CurrentAFT.BinaryReferenceTables
import CurrentAFT.RationalMassLiftProgram

/-! # Generated current sign tables and literal binary mass-lift evaluation -/
namespace CurrentAFT.BinaryFirstInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryProfileTables.sign
  BinaryMassLiftKernel.prepare BinaryMassLiftKernel.current BinaryReferenceTables.current

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def signPoint (security bits output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryProfileTables.sign security bits code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem signPoint_value (security bits output : ℕ) :
    (signPoint security bits output).data.decode = RationalFirstResponseProgram.signProfile security bits output := by
  simp only [signPoint, BinaryProfileTables.sign_value, canonicalCounter_value]

structure Cache (security : ℕ) where
  sign : Vector RationalBits (colors security)
  denominator : RationalBits
  work : ℕ

def prepare (security bits : ℕ) : Cache security :=
  let modulus := PublicParameterProgram.modulus security
  let sign := buildArray modulus.count (fun output => signPoint security bits output.val)
  let rate := BinaryActivationProgram.current security bits
  let denominator := BinaryMassLiftKernel.prepare sign.data rate.data
  ⟨sign.data, denominator.data, modulus.work+sign.work+rate.work+denominator.work+4⟩

theorem sign_value (security bits : ℕ) (output : Fin (colors security)) :
    ((prepare security bits).sign.get output).decode = RationalFirstResponseProgram.signProfile security bits output.val := by
  simp only [prepare, buildArray_get, signPoint_value]

theorem denominator_value (security bits : ℕ) :
    (prepare security bits).denominator.decode = RationalFirstResponseProgram.guardedDenominator security bits := by
  change (BinaryMassLiftKernel.prepare
    (buildArray (colors security) (fun output => signPoint security bits output.val)).data
    (BinaryActivationProgram.current security bits).data).data.decode = _
  rw [BinaryMassLiftKernel.prepare_value, BinaryActivationProgram.current_value]
  unfold RationalFirstResponseProgram.guardedDenominator RationalFirstResponseProgram.denominator
    RationalFirstResponseProgram.functional RationalFirstResponseProgram.anchorSign
  simp only [buildArray_get, signPoint_value]

def inputAt (security : ℕ) (input : Vector RationalBits (colors security)) (output : ℕ) : ℚ :=
  if h : output<colors security then (input.get ⟨output,h⟩).decode else 0

theorem inputAt_value (security : ℕ) (input : Vector RationalBits (colors security)) (output : Fin (colors security)) :
    inputAt security input output.val = (input.get output).decode := by
  simp only [inputAt, dif_pos output.isLt]

def current (security bits : ℕ) (input : Vector RationalBits (colors security)) (output : Fin (colors security)) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let inverse := prepare security bits
  let result := BinaryMassLiftKernel.current references.primary inverse.sign input references.activation inverse.denominator output
  ⟨result.data, references.work+inverse.work+result.work+3⟩

theorem current_value (security bits : ℕ) (input : Vector RationalBits (colors security)) (output : Fin (colors security)) :
    (current security bits input output).data.decode =
      RationalMassLiftProgram.current security bits (inputAt security input) output.val := by
  change (BinaryMassLiftKernel.current _ _ _ _ _ _).data.decode = _
  rw [BinaryMassLiftKernel.current_value, BinaryReferenceTables.primary_value,
    BinaryReferenceTables.activation_value, sign_value, denominator_value]
  unfold RationalMassLiftProgram.current RationalFirstResponseProgram.inverse RationalFirstResponseProgram.functional
    RationalFirstResponseProgram.anchorSign
  simp only [inputAt_value]

noncomputable section
open scoped Classical

noncomputable def colorsPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
noncomputable def signHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileTables.signHeightPolynomial precision colorsPolynomial
noncomputable def signWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(colorsPolynomial+1)^2+BinaryProfileTables.signWorkPolynomial precision colorsPolynomial+2

theorem colors_bound (security : ℕ) : colors security ≤ colorsPolynomial.eval security := by
  rw [colors, PublicParameterProgram.modulus_value]
  simpa only [colorsPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Parameters.base] using (Parameters.modulus_bounds security).2

theorem signPoint_bounds (security : ℕ) (precision : Polynomial ℕ) (output : Fin (colors security)) :
    HeightBound (signPoint security (precision.eval security) output.val).data.decode
      ((signHeightPolynomial precision).eval security) ∧
      (signPoint security (precision.eval security) output.val).work ≤ (signWorkPolynomial precision).eval security := by
  have hl : (canonicalCounter output.val).digits.length ≤ colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans
      (output.isLt.le.trans (colors_bound security))
  have hsign := BinaryProfileTables.sign_bounds security (canonicalCounter output.val).digits precision colorsPolynomial hl
  have wcode : (canonicalCounter output.val).work ≤ 50*(colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work output.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right (output.isLt.le.trans (colors_bound security)) 1) 2))
  constructor
  · exact hsign.1
  · change _+_+2 ≤ _
    simp only [signWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

end
end CurrentAFT.BinaryFirstInverseProgram

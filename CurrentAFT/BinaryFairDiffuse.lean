import CurrentAFT.BinaryDiffuseCurrent
import CurrentAFT.BinaryPairProgram
import CurrentAFT.BinaryFirstInverseProgram
import AFT.BinaryIntegerData
import CurrentAFT.RationalDiffuseResidualProgram

/-! # The genuine fair-sign diffuse pair, executed with binary data -/
namespace CurrentAFT.BinaryFairDiffuse
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.current

def midpoint (security : ℕ) : UnaryCounterResult :=
  let modulus := PublicParameterProgram.modulus security
  let last := differenceCounter modulus.count 1
  let result := divideCounter last.count 2
  ⟨result.quotient,modulus.work+last.work+result.work+3⟩

theorem midpoint_value (security : ℕ) :
    (midpoint security).count=(Parameters.modulus security-1)/2 := by
  simp only [midpoint,(divideCounter_value _ _ (by omega : 0<2)).1,differenceCounter_value,
    PublicParameterProgram.modulus_value]

theorem modulus_gt_two (security : ℕ) : 2<Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security^64 := one_le_pow₀ (by have := Parameters.base_ge_two security; omega)
  have h := (Parameters.modulus_bounds security).1
  omega

theorem midpoint_twice (security : ℕ) : 2*(midpoint security).count=Parameters.modulus security-1 := by
  rw [midpoint_value]
  obtain ⟨number,hn⟩ := (Parameters.modulus_spec security).2.even_sub_one (by have := modulus_gt_two security; omega)
  omega

def primary (security : ℕ) : FirstHistogram.Palette security :=
  ⟨(midpoint security).count,by have := midpoint_twice security; have := modulus_gt_two security; omega⟩

theorem evaluate_middle (security colors width cutoff bits primary : ℕ) (source : ℤ) (first second : ℕ)
    (hmiddle : 2*primary=colors-1) :
    LocalDiffuseProgram.evaluate security colors width cutoff bits primary source first second=
      RationalDiffuseResidualProgram.evaluate security colors width cutoff bits source first second := by
  have hd (choice : Bool) : LocalDiffuseProgram.direction colors primary choice=choice := by
    unfold LocalDiffuseProgram.direction
    simp only [hmiddle,lt_self_iff_false,if_false]
  simp only [LocalDiffuseProgram.evaluate,LocalDiffuseProgram.blurEntry,LocalDiffuseProgram.coinEntry,hd,
    RationalDiffuseResidualProgram.evaluate,Fintype.sum_bool,RationalProposalProgram.gaussianWeight_eq]
  simp_rw [show ∀ a b c d : ℚ, a*b*((c+d)/2)=(1/2*a*b*c)+(1/2*a*b*d) by intros; ring]
  simp only [Finset.sum_add_distrib]

def current (security bits : ℕ) (scalar : IntegerBits) (first second : List Bool) : RationalResult :=
  let middle := midpoint security
  let result := BinaryDiffuseCurrent.current security bits middle.count scalar.negative scalar.digits first second
  ⟨result.data,middle.work+result.work+2⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits) (first second : List Bool) :
    (current security bits scalar first second).data.decode=
      RationalDiffuseResidualProgram.pair security bits scalar.decode (value first) (value second) := by
  change (BinaryDiffuseCurrent.current _ _ _ _ _ _ _).data.decode=_
  rw [BinaryDiffuseCurrent.current_value]
  unfold LocalDiffuseProgram.current RationalDiffuseResidualProgram.pair
  apply evaluate_middle
  rw [PublicParameterProgram.modulus_value]
  exact midpoint_twice security

noncomputable section
noncomputable def midpointWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+2*BinaryFirstInverseProgram.colorsPolynomial+1+
    500*(BinaryFirstInverseProgram.colorsPolynomial+4)^2+3
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.diffuseHeightPolynomial precision inputBits
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  midpointWorkPolynomial+BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits+2

theorem midpoint_work (security : ℕ) :
    (midpoint security).work ≤ midpointWorkPolynomial.eval security := by
  let modulus := PublicParameterProgram.modulus security
  let last := differenceCounter modulus.count 1
  have wq := PublicParameterProgram.modulus_work security
  have wl := differenceCounter_work modulus.count 1
  have wd := divideCounter_work last.count 2 (by omega : 0<2)
  have hlast : last.count ≤ modulus.count := by rw [differenceCounter_value]; omega
  have hq : modulus.count ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have wd' : (divideCounter last.count 2).work ≤ 500*(BinaryFirstInverseProgram.colorsPolynomial.eval security+4)^2 :=
    wd.trans (by gcongr; omega)
  change modulus.work+last.work+(divideCounter last.count 2).work+3 ≤ _
  simp only [midpointWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval]
  change modulus.work ≤ _ at wq
  change last.work ≤ _ at wl
  omega

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (scalar : IntegerBits)
    (first second : List Bool) (hs : scalar.digits.length ≤ inputBits.eval security)
    (hf : first.length ≤ inputBits.eval security) (ht : second.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) scalar first second).data.decode
      ((heightPolynomial precision inputBits).eval security) ∧
    (current security (precision.eval security) scalar first second).work ≤ (workPolynomial precision inputBits).eval security := by
  have hh := BinaryDiffuseCurrent.current_height security (precision.eval security) (primary security)
    scalar.negative scalar.digits first second (inputBits.eval security) hs hf ht
  have hw := BinaryDiffuseCurrent.current_polynomial_work security (primary security)
    scalar.negative scalar.digits first second precision inputBits hs hf ht
  have wm := midpoint_work security
  constructor
  · rw [heightPolynomial,BinaryPairProgram.diffuseHeightPolynomial_eval]
    exact hh
  · simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
    change (midpoint security).work+(BinaryDiffuseCurrent.current _ _ _ _ _ _ _).work+2 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add wm hw) 2

end
end CurrentAFT.BinaryFairDiffuse

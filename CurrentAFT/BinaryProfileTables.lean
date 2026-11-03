import CurrentAFT.BinaryProfileProgram

/-! # Diffuse mean and sign tables from the same actual binary profiles -/
namespace CurrentAFT.BinaryProfileTables
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def diffuse (security bits : ℕ) (output : List Bool) : RationalResult :=
  let first := BinaryProfileProgram.current security bits true output
  let second := BinaryProfileProgram.current security bits false output
  let total := RationalBits.add first.data second.data
  let result := RationalBits.multiply total.data half
  ⟨result.data, first.work + second.work + total.work + result.work + 4⟩

theorem diffuse_formula (security bits output : ℕ) :
    RationalProposalProgram.diffuse security bits output =
      (RationalFirstResponseProgram.profile security bits true output+
        RationalFirstResponseProgram.profile security bits false output)/2 := by
  simp only [RationalProposalProgram.diffuse, RationalFirstResponseProgram.profile,
    RationalProposalProgram.seedEvaluate, RationalProposalProgram.diffuseKernel,
    RationalFirstResponseProgram.profileKernel, if_true, Bool.false_eq_true, if_false,
    mul_div, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem diffuse_value (security bits : ℕ) (output : List Bool) :
    (diffuse security bits output).data.decode = RationalProposalProgram.diffuse security bits (value output) := by
  simp only [diffuse, RationalBits.multiply_value, RationalBits.add_value, half_value,
    BinaryProfileProgram.current_value, diffuse_formula]
  ring

def sign (security bits : ℕ) (output : List Bool) : RationalResult :=
  let rate := BinaryActivationProgram.current security bits
  let first := BinaryProfileProgram.current security bits true output
  let second := BinaryProfileProgram.current security bits false output
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let negativeSecond := RationalBits.negate second.data
  let difference := RationalBits.add first.data negativeSecond.data
  let result := RationalBits.multiply remaining.data difference.data
  ⟨result.data, rate.work + first.work + second.work + negativeRate.work + remaining.work +
    negativeSecond.work + difference.work + result.work + 8⟩

theorem sign_value (security bits : ℕ) (output : List Bool) :
    (sign security bits output).data.decode = RationalFirstResponseProgram.signProfile security bits (value output) := by
  simp only [sign, RationalBits.multiply_value, RationalBits.add_value, RationalBits.negate_value, one_value,
    BinaryActivationProgram.current_value, BinaryProfileProgram.current_value,
    RationalFirstResponseProgram.signProfile, sub_eq_add_neg]

noncomputable section
open scoped Classical

theorem diffuse_error (security bits : ℕ) (output : FirstHistogram.Palette security) (code : List Bool)
    (ho : value code = output.val) :
    |((diffuse security bits code).data.decode:ℝ)-ProposalPrimary.diffuseMean security output| ≤ 3/(2:ℝ)^bits := by
  rw [diffuse_value, ho]
  exact RationalProposalProgram.diffuse_error security bits output

theorem sign_error (security bits : ℕ) (output : FirstHistogram.Palette security) (code : List Bool)
    (ho : value code = output.val) :
    |((sign security bits code).data.decode:ℝ)-DiffuseProfiles.signProfile security output| ≤ 7/(2:ℝ)^bits := by
  rw [sign_value, ho]
  exact RationalFirstResponseProgram.signProfile_error security bits output

noncomputable def diffuseHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+3
noncomputable def diffuseWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryProfileProgram.currentWorkPolynomial precision inputBits+
    primitiveWorkPolynomial (BinaryProfileProgram.currentHeightPolynomial precision inputBits)+
    primitiveWorkPolynomial (2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+2)+4

theorem diffuse_bounds (security : ℕ) (output : List Bool) (precision inputBits : Polynomial ℕ)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (diffuse security (precision.eval security) output).data.decode
      ((diffuseHeightPolynomial precision inputBits).eval security) ∧
      (diffuse security (precision.eval security) output).work ≤ (diffuseWorkPolynomial precision inputBits).eval security := by
  let first := BinaryProfileProgram.current security (precision.eval security) true output
  let second := BinaryProfileProgram.current security (precision.eval security) false output
  let total := RationalBits.add first.data second.data
  let height := (BinaryProfileProgram.currentHeightPolynomial precision inputBits).eval security
  have hf : HeightBound first.data.decode height := BinaryProfileProgram.current_height security true output precision inputBits ho
  have hs : HeightBound second.data.decode height := BinaryProfileProgram.current_height security false output precision inputBits ho
  have hh : HeightBound half.decode 2 := by rw [half_value]; norm_num [HeightBound]
  have ht : HeightBound total.data.decode (2*height+1) := by
    rw [RationalBits.add_value]; exact (hf.add hs).mono (by omega)
  have wf : first.work ≤ (BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security :=
    BinaryProfileProgram.current_polynomial_work security true output precision inputBits ho
  have ws : second.work ≤ (BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security :=
    BinaryProfileProgram.current_polynomial_work security false output precision inputBits ho
  have wt : total.work ≤ primitiveWorkBound height := RationalBits.add_work _ _ _ hf hs
  have wm := RationalBits.multiply_work total.data half (2*height+2) (ht.mono (by omega)) (hh.mono (by omega))
  constructor
  · change HeightBound (RationalBits.multiply total.data half).data.decode _
    rw [RationalBits.multiply_value]
    apply (ht.mul hh).mono
    simp only [diffuseHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    change (2*height+1)+2 ≤ 2*height+3
    omega
  · change first.work + second.work + total.work + (RationalBits.multiply total.data half).work + 4 ≤ _
    simp only [diffuseWorkPolynomial, primitiveWorkPolynomial_eval, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_ofNat]
    change _ ≤ 2*(BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security+
      primitiveWorkBound height+primitiveWorkBound (2*height+2)+4
    omega

noncomputable def signHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentHeightPolynomial precision+
    2*BinaryProfileProgram.currentHeightPolynomial precision inputBits+10
noncomputable def signWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision+2*BinaryProfileProgram.currentWorkPolynomial precision inputBits+
    5*primitiveWorkPolynomial (signHeightPolynomial precision inputBits)+8

theorem sign_bounds (security : ℕ) (output : List Bool) (precision inputBits : Polynomial ℕ)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (sign security (precision.eval security) output).data.decode
      ((signHeightPolynomial precision inputBits).eval security) ∧
      (sign security (precision.eval security) output).work ≤ (signWorkPolynomial precision inputBits).eval security := by
  let rate := BinaryActivationProgram.current security (precision.eval security)
  let first := BinaryProfileProgram.current security (precision.eval security) true output
  let second := BinaryProfileProgram.current security (precision.eval security) false output
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let negativeSecond := RationalBits.negate second.data
  let difference := RationalBits.add first.data negativeSecond.data
  let height := (signHeightPolynomial precision inputBits).eval security
  let rateHeight := BinaryActivationProgram.currentHeight security (precision.eval security)
  let profileHeight := (BinaryProfileProgram.currentHeightPolynomial precision inputBits).eval security
  have hheight : height = rateHeight+2*profileHeight+10 := by
    simp only [height, signHeightPolynomial, BinaryActivationProgram.currentHeightPolynomial_eval,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rfl
  have hr : HeightBound rate.data.decode rateHeight := (BinaryActivationProgram.current_bounds security _).1
  have hf : HeightBound first.data.decode profileHeight := BinaryProfileProgram.current_height security true output precision inputBits ho
  have hs : HeightBound second.data.decode profileHeight := BinaryProfileProgram.current_height security false output precision inputBits ho
  have hnr : HeightBound negativeRate.data.decode rateHeight := by rw [RationalBits.negate_value]; exact hr.neg
  have hrem : HeightBound remaining.data.decode (rateHeight+1) := by
    rw [RationalBits.add_value, one_value]; exact (HeightBound.one.add hnr).mono (by omega)
  have hns : HeightBound negativeSecond.data.decode profileHeight := by rw [RationalBits.negate_value]; exact hs.neg
  have hdiff : HeightBound difference.data.decode (2*profileHeight+1) := by
    rw [RationalBits.add_value]; exact (hf.add hns).mono (by omega)
  have wr : rate.work ≤ (BinaryActivationProgram.currentWorkPolynomial precision).eval security :=
    BinaryActivationProgram.current_polynomial_work precision security
  have wf : first.work ≤ (BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security :=
    BinaryProfileProgram.current_polynomial_work security true output precision inputBits ho
  have ws : second.work ≤ (BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security :=
    BinaryProfileProgram.current_polynomial_work security false output precision inputBits ho
  have wnr : negativeRate.work ≤ primitiveWorkBound height := RationalBits.negate_work _ _
  have wrem : remaining.work ≤ primitiveWorkBound height := RationalBits.add_work _ _ _
    (by rw [one_value]; exact HeightBound.one.mono (by omega)) (hnr.mono (by omega))
  have wns : negativeSecond.work ≤ primitiveWorkBound height := RationalBits.negate_work _ _
  have wdiff : difference.work ≤ primitiveWorkBound height := RationalBits.add_work _ _ _
    (hf.mono (by omega)) (hns.mono (by omega))
  have wm := RationalBits.multiply_work remaining.data difference.data height (hrem.mono (by omega)) (hdiff.mono (by omega))
  constructor
  · change HeightBound (RationalBits.multiply remaining.data difference.data).data.decode _
    rw [RationalBits.multiply_value]
    exact (hrem.mul hdiff).mono (by omega)
  · change rate.work + first.work + second.work + negativeRate.work + remaining.work + negativeSecond.work +
      difference.work + (RationalBits.multiply remaining.data difference.data).work + 8 ≤ _
    simp only [signWorkPolynomial, primitiveWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    change _ ≤ (BinaryActivationProgram.currentWorkPolynomial precision).eval security+
      2*(BinaryProfileProgram.currentWorkPolynomial precision inputBits).eval security+5*primitiveWorkBound height+8
    omega

end
end CurrentAFT.BinaryProfileTables

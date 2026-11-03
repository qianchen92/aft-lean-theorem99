import AFT.BinaryParameterProgram

/-! Literal polynomial bounds for the complete public modulus and root
population, including prime search and every binary division. -/
namespace AFT.BinaryArithmetic
open V7Calibration Polynomial
set_option backward.isDefEq.respectTransparency false

noncomputable def binaryPrimeWorkPolynomial (candidate : Polynomial ℕ) : Polynomial ℕ :=
  3*(candidate+2)+2+2*candidate+2+(2+candidate*(500*(candidate+candidate+4)^2+5))+3
noncomputable def binaryModulusTestPolynomial (base candidate : Polynomial ℕ) : Polynomial ℕ :=
  binaryPrimeWorkPolynomial candidate+(3*(base+candidate)+2)+(3*base+1)+(3*(candidate+(2*base+1))+2)+4
noncomputable def binaryModulusPolynomial : Polynomial ℕ :=
  3+41*(6*(X+1)^42+4)+(3*X^40+1)+2*X^40*(binaryModulusTestPolynomial (X^40) (2*X^40)+1)+4

theorem binaryModulusPolynomial_eval (n : ℕ) : binaryModulusPolynomial.eval n=binaryModulusWork n := by
  simp only [binaryModulusPolynomial,binaryModulusTestPolynomial,binaryPrimeWorkPolynomial,
    eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X,binaryModulusWork,binaryModulusTestWork,
    binaryPrimeWork,powerCounterWork]
  norm_num

theorem binaryModulus_polynomial_work (n : ℕ) (hn : 2≤n) :
    (binaryModulus n).work≤binaryModulusPolynomial.eval n := by
  rw [binaryModulusPolynomial_eval]
  exact binaryModulus_work n hn

def binaryRootPopulation (n : ℕ) : UnaryCounterResult :=
  let security := securityCounter n
  let modulus := binaryModulus n
  let bodyScale := powerCounter security.count 20
  let legs := powerCounter security.count 30
  let dimension := multiplyCounter modulus.count bodyScale.count
  let removed := doubleCounter legs.count
  let result := subtractCounter dimension.count removed.count
  ⟨result.count,security.work+modulus.work+bodyScale.work+legs.work+dimension.work+removed.work+result.work+7⟩

theorem binaryRootPopulation_value (n : ℕ) : (binaryRootPopulation n).count=actualRootPopulationProgram n := by
  simp only [binaryRootPopulation,subtractCounter_value,securityCounter_value,binaryModulus_value,
    powerCounter_value,multiplyCounter_value,doubleCounter_value,actualRootPopulationProgram,
    ParameterProgram.modulus_value]

noncomputable def binaryRootPopulationPolynomial : Polynomial ℕ :=
  3+binaryModulusPolynomial+21*(6*(X+1)^22+4)+31*(6*(X+1)^32+4)+
    (2*X^40)*(2*X^20+3)+1+(3*X^30+1)+(2*((2*X^40)*X^20)+2)+7

theorem binaryRootPopulation_polynomial_work (n : ℕ) (hn : 2≤n) :
    (binaryRootPopulation n).work≤binaryRootPopulationPolynomial.eval n := by
  have hs : (securityCounter n).count=n := by rw [securityCounter_value,max_eq_right hn]
  have hw := securityCounter_work n
  have hm := binaryModulus_polynomial_work n hn
  have hb := powerCounter_work n 20
  have hl := powerCounter_work n 30
  have hq : (binaryModulus n).count≤2*n^40 := by
    rw [binaryModulus_value]
    simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2
  have hd := multiplyCounter_work (binaryModulus n).count (n^20)
  have hs' := subtractCounter_work_left ((binaryModulus n).count*n^20) (2*n^30)
  have hdm : (binaryModulus n).count*(2*n^20+3)≤(2*n^40)*(2*n^20+3) := Nat.mul_le_mul_right _ hq
  have hsm : 2*((binaryModulus n).count*n^20)≤2*((2*n^40)*n^20) := by gcongr
  simp only [binaryRootPopulation,hs,powerCounter_value,multiplyCounter_value,doubleCounter_value,doubleCounter_work,
    binaryRootPopulationPolynomial,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one,powerCounterWork] at *
  norm_num only at *
  omega

end AFT.BinaryArithmetic

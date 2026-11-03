import CurrentAFT.BinaryMassLiftKernel

/-! # Polynomial resources for the executed guarded mass lift -/
namespace CurrentAFT.BinaryMassLiftKernel
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000

theorem prepareHeight_mono {count bits largerCount largerBits : ℕ}
    (hc : count ≤ largerCount) (hb : bits ≤ largerBits) :
    prepareHeight count bits ≤ prepareHeight largerCount largerBits := by
  unfold prepareHeight BinaryRankOneFunctional.height
  gcongr

theorem prepareWork_mono {count bits largerCount largerBits : ℕ}
    (hc : count ≤ largerCount) (hb : bits ≤ largerBits) :
    prepareWork count bits ≤ prepareWork largerCount largerBits := by
  unfold prepareWork prepareHeight BinaryRankOneFunctional.work BinaryRankOneFunctional.height
    primitiveWorkBound BinaryRationalCompare.workBound
  gcongr

theorem height_mono {count bits largerCount largerBits : ℕ}
    (hc : count ≤ largerCount) (hb : bits ≤ largerBits) :
    height count bits ≤ height largerCount largerBits := by
  unfold height operandHeight BinaryMassLiftFormula.height BinaryRankOneFunctional.height
  gcongr

theorem work_mono {count bits largerCount largerBits : ℕ}
    (hc : count ≤ largerCount) (hb : bits ≤ largerBits) :
    work count bits ≤ work largerCount largerBits := by
  unfold work operandHeight BinaryMassLiftFormula.work BinaryMassLiftFormula.height
    BinaryRankOneFunctional.work BinaryRankOneFunctional.height primitiveWorkBound
  gcongr

noncomputable def prepareHeightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.heightPolynomial count bits+bits+5
noncomputable def prepareWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.workPolynomial count bits+3*primitiveWorkPolynomial (prepareHeightPolynomial count bits)+
    BinaryRationalCompare.workPolynomial (prepareHeightPolynomial count bits)+9
noncomputable def operandHeightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.heightPolynomial count bits+bits
noncomputable def heightPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftFormula.heightPolynomial (operandHeightPolynomial count bits)
noncomputable def workPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRankOneFunctional.workPolynomial count bits+9*count+14+
    BinaryMassLiftFormula.workPolynomial (operandHeightPolynomial count bits)

theorem prepareHeightPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (prepareHeightPolynomial count bits).eval security = prepareHeight (count.eval security) (bits.eval security) := by
  simp only [prepareHeightPolynomial, prepareHeight, BinaryRankOneFunctional.heightPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_ofNat]

theorem prepareWorkPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (prepareWorkPolynomial count bits).eval security = prepareWork (count.eval security) (bits.eval security) := by
  simp only [prepareWorkPolynomial, prepareWork, BinaryRankOneFunctional.workPolynomial_eval,
    primitiveWorkPolynomial_eval, BinaryRationalCompare.workPolynomial_eval, prepareHeightPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]

theorem operandHeightPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (operandHeightPolynomial count bits).eval security = operandHeight (count.eval security) (bits.eval security) := by
  simp only [operandHeightPolynomial, operandHeight, BinaryRankOneFunctional.heightPolynomial_eval, Polynomial.eval_add]

theorem heightPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (heightPolynomial count bits).eval security = height (count.eval security) (bits.eval security) := by
  simp only [heightPolynomial, height, BinaryMassLiftFormula.heightPolynomial_eval, operandHeightPolynomial_eval]

theorem workPolynomial_eval (count bits : Polynomial ℕ) (security : ℕ) :
    (workPolynomial count bits).eval security = work (count.eval security) (bits.eval security) := by
  simp only [workPolynomial, work, BinaryRankOneFunctional.workPolynomial_eval,
    BinaryMassLiftFormula.workPolynomial_eval, operandHeightPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat]

end CurrentAFT.BinaryMassLiftKernel

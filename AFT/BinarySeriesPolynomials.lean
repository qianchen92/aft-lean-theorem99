import AFT.BinaryFiniteSeries

/-! Literal polynomial budgets for the executable binary finite-series
algorithms. These polynomials describe the proved runtime counters. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.RationalNumerics

noncomputable def primitiveWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 10000000*(bits+2)^3
noncomputable def seriesTermBitsPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ := (2*terms+2)^2*(bits+1)
noncomputable def seriesStepWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  primitiveWorkPolynomial (seriesTermBitsPolynomial bits terms)+60*(2*terms+2)^2+10
noncomputable def seriesTermWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  10*(terms+1)*seriesStepWorkPolynomial bits terms
noncomputable def seriesWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  terms*(seriesTermWorkPolynomial bits terms+
    primitiveWorkPolynomial ((terms+1)*(seriesTermBitsPolynomial bits terms+1))+2)+2
noncomputable def piHeightPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  2*((bits+3)*(6*(bits+3)+4))+3
noncomputable def piWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  2*seriesWorkPolynomial 2 (bits+3)+2*primitiveWorkPolynomial (piHeightPolynomial bits)+(2*bits+1)+4

@[simp] theorem primitiveWorkPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (primitiveWorkPolynomial bits).eval n=primitiveWorkBound (bits.eval n) := by
  simp only [primitiveWorkPolynomial,primitiveWorkBound,eval_mul,eval_add,eval_pow,eval_ofNat]
@[simp] theorem seriesTermBitsPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesTermBitsPolynomial bits terms).eval n=seriesTermBits (bits.eval n) (terms.eval n) := by
  simp only [seriesTermBitsPolynomial,seriesTermBits,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one]
@[simp] theorem seriesStepWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesStepWorkPolynomial bits terms).eval n=seriesStepWork (bits.eval n) (terms.eval n) := by
  simp only [seriesStepWorkPolynomial,seriesStepWork,eval_mul,eval_add,eval_pow,eval_ofNat,
    primitiveWorkPolynomial_eval,seriesTermBitsPolynomial_eval]
@[simp] theorem seriesTermWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesTermWorkPolynomial bits terms).eval n=seriesTermWork (bits.eval n) (terms.eval n) := by
  simp only [seriesTermWorkPolynomial,seriesTermWork,eval_mul,eval_add,eval_ofNat,eval_one,
    seriesStepWorkPolynomial_eval]
@[simp] theorem seriesWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesWorkPolynomial bits terms).eval n=seriesWork (bits.eval n) (terms.eval n) := by
  simp only [seriesWorkPolynomial,seriesWork,eval_mul,eval_add,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,seriesTermWorkPolynomial_eval,seriesTermBitsPolynomial_eval]
@[simp] theorem piHeightPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (piHeightPolynomial bits).eval n=piHeight (bits.eval n) := by
  simp only [piHeightPolynomial,piHeight,eval_mul,eval_add,eval_ofNat]
@[simp] theorem piWorkPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (piWorkPolynomial bits).eval n=piWork (bits.eval n) := by
  simp only [piWorkPolynomial,piWork,eval_mul,eval_add,eval_ofNat,eval_one,seriesWorkPolynomial_eval,
    primitiveWorkPolynomial_eval,piHeightPolynomial_eval]

theorem seriesWork_mono {b1 b2 t1 t2 : ℕ} (hb : b1 ≤ b2) (ht : t1 ≤ t2) :
    seriesWork b1 t1 ≤ seriesWork b2 t2 := by
  unfold seriesWork seriesTermWork seriesStepWork seriesTermBits primitiveWorkBound
  gcongr

theorem piWork_mono {b1 b2 : ℕ} (hb : b1 ≤ b2) : piWork b1 ≤ piWork b2 := by
  unfold piWork
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (seriesWork_mono le_rfl (by omega))
    · apply Nat.mul_le_mul_left
      apply primitiveWorkBound_mono
      unfold piHeight
      gcongr
  · omega

theorem arctan_polynomial_work (input : RationalBits) (bits terms : ℕ)
    (h : HeightBound input.decode bits) (bitBudget termBudget : Polynomial ℕ) (n : ℕ)
    (hb : bits ≤ bitBudget.eval n) (ht : terms ≤ termBudget.eval n) :
    (arctan input terms).work ≤ (seriesWorkPolynomial bitBudget termBudget).eval n := by
  rw [seriesWorkPolynomial_eval]
  exact (arctan_work input bits terms h).trans (seriesWork_mono hb ht)

theorem taylor_polynomial_work (input : RationalBits) (bits terms : ℕ)
    (h : HeightBound input.decode bits) (bitBudget termBudget : Polynomial ℕ) (n : ℕ)
    (hb : bits ≤ bitBudget.eval n) (ht : terms ≤ termBudget.eval n) :
    (taylor input terms).work ≤ (seriesWorkPolynomial bitBudget termBudget).eval n := by
  rw [seriesWorkPolynomial_eval]
  exact (taylor_work input bits terms h).trans (seriesWork_mono hb ht)

theorem pi_polynomial_work (bits : ℕ) (bitBudget : Polynomial ℕ) (n : ℕ)
    (hb : bits ≤ bitBudget.eval n) :
    (pi bits).work ≤ (piWorkPolynomial bitBudget).eval n := by
  rw [piWorkPolynomial_eval]
  exact (pi_work bits).trans (piWork_mono hb)

end AFT.BinaryArithmetic.RationalBits

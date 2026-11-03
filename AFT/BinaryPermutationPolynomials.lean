import AFT.BinaryPublicPoolScan
import AFT.ActualPermutationProgram

/-! Explicit polynomial costs for the actual stored public permutations. -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits

noncomputable def binaryPermutationChoicePolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(count+2)^2+primitiveWorkPolynomial (count+1)+(count+1)+
    binaryRationalDrawPolynomial (count+1) (count+1) bits+4
noncomputable def binaryPermutationRowsPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(binaryPermutationChoicePolynomial count bits+(count+1)*(9*count+17)+5)+2

@[simp] theorem binaryPermutationChoicePolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationChoicePolynomial count bits).eval n=
      binaryPermutationChoiceWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationChoicePolynomial,binaryPermutationChoiceWork]
@[simp] theorem binaryPermutationRowsPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationRowsPolynomial count bits).eval n=
      binaryPermutationRowsWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationRowsPolynomial,binaryPermutationRowsWork]

theorem binaryPermutationRowsWork_mono {c d b e : ℕ} (hc : c ≤ d) (hb : b ≤ e) :
    binaryPermutationRowsWork c b ≤ binaryPermutationRowsWork d e := by
  have hchoice := binaryPermutationChoiceWork_mono hc hb
  unfold binaryPermutationRowsWork
  gcongr

noncomputable def binaryActualPermutationPolynomial : Polynomial ℕ :=
  binaryPermutationRowsPolynomial (2*X^60) X

theorem binaryActualPermutation_polynomial_work (n count : ℕ) (hc : count ≤ 2*n^60)
    (word : Fin count → Fin n → Fin 2) :
    (binaryPermutationRows n count word).work ≤ binaryActualPermutationPolynomial.eval n := by
  simpa only [binaryActualPermutationPolynomial,binaryPermutationRowsPolynomial_eval,
    eval_mul,eval_ofNat,eval_pow,eval_X] using
    (binaryPermutationRows_work n count word).trans (binaryPermutationRowsWork_mono hc le_rfl)

theorem binaryActualPublicPermutations_work (n : ℕ) (hn : 2 ≤ n)
    (vertexWord : Fin (AFT.PermutationProgram.vertexCount n) → Fin n → Fin 2)
    (bodyWord : Fin (AFT.PermutationProgram.bodyCount n) → Fin n → Fin 2) :
    (binaryPermutationRows n _ vertexWord).work+(binaryPermutationRows n _ bodyWord).work ≤
      (2*binaryActualPermutationPolynomial).eval n := by
  have hv := binaryActualPermutation_polynomial_work n _ (AFT.PermutationProgram.population_bound n hn).1 vertexWord
  have hb := binaryActualPermutation_polynomial_work n _ (AFT.PermutationProgram.population_bound n hn).2 bodyWord
  simp only [eval_mul,eval_ofNat]
  omega

end AFT.BinaryArithmetic

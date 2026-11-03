import CurrentAFT.BinarySparseCycleSemantic
import CurrentAFT.BinaryDistinctTuples

/-! Uniform distinct cycle-root placements are averaged by executed tuple
loops and their computed distinct-selection normalizer. -/
namespace CurrentAFT.BinarySparseCycleAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def current (security cutoff bits body count : ℕ) (hb : 0 < body)
    (test : Vector IntegerBits count → RationalResult) : RationalResult :=
  let numerator := BinaryDistinctTuples.sum body count hb (fun sites =>
    BinarySparseCycleEvaluation.current security cutoff bits hb sites test)
  let denominator := BinaryDistinctTuples.normalizer body count hb
  let result := RationalBits.quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

noncomputable section
open scoped Classical

 theorem current_value (security cutoff bits body count : ℕ) (hb : 0 < body)
    (test : Vector IntegerBits count → RationalResult) (ideal : (Fin count → ℤ) → ℚ)
    (htest : ∀ roots, (test roots).data.decode = ideal (fun slot => (roots.get slot).decode)) :
    (current security cutoff bits body count hb test).data.decode =
      CyclePatternProgram.averagedEvaluate security cutoff bits body count (fun _ => ideal) := by
  simp only [current,RationalBits.quotient_value,BinaryDistinctTuples.sum_value,BinaryDistinctTuples.normalizer_value]
  simp_rw [BinarySparseCycleSemantic.current_value _ _ _ _ _ _ ideal htest]
  unfold CyclePatternProgram.averagedEvaluate
  simp only [Fintype.card_embedding_eq,Fintype.card_fin]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply Finset.sum_congr (by ext sites; simp)
  intro sites _
  rw [BinaryTupleSum.get_ofFn_fun]

end
end CurrentAFT.BinarySparseCycleAverage

import CurrentAFT.CurrentProposalPrecision
import AFT.UnaryPolynomialCounters

/-! The proposal's polynomial padding is computed by actual counters. -/
namespace CurrentAFT.BinaryProposalPrecision
open AFT BinaryArithmetic Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] addCounter powerCounter multiplyCounter

def current (security bits : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let powered := powerCounter base.count 226
  let padding := multiplyCounter (2^44) powered.count
  let result := addCounter bits padding.count
  ⟨result.count, base.work+powered.work+padding.work+result.work+4⟩

theorem current_value (security bits : ℕ) :
    (current security bits).count = CurrentProposalPrecision.tableBits security bits := by
  simp only [current, addCounter_value, powerCounter_value, multiplyCounter_value]

noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  (2*X+1)+227*(6*(X+3)^228+4)+(2^44*(2*(X+2)^226+3)+1)+(2*precision+1)+4

theorem polynomial_work (security : ℕ) (precision : Polynomial ℕ) :
    (current security (precision.eval security)).work ≤ (workPolynomial precision).eval security := by
  have hp := powerCounter_work (security+2) 226
  have hm := multiplyCounter_work (2^44) ((security+2)^226)
  have hb := addCounter_work security 2
  have hr := addCounter_work (precision.eval security) (multiplyCounter (2^44) ((security+2)^226)).count
  change (addCounter security 2).work+(powerCounter (addCounter security 2).count 226).work+
    (multiplyCounter (2^44) (powerCounter (addCounter security 2).count 226).count).work+
    (addCounter (precision.eval security) (multiplyCounter (2^44) (powerCounter (addCounter security 2).count 226).count).count).work+4 ≤ _
  simp only [addCounter_value, powerCounter_value]
  simp only [workPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X, eval_one]
  unfold powerCounterWork at hp
  norm_num only at hp
  rw [show security+2+1 = security+3 by omega] at hp
  omega

end CurrentAFT.BinaryProposalPrecision

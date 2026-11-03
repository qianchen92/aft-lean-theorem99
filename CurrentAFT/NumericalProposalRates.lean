import CurrentAFT.NumericalWeightRates
import CurrentAFT.CurrentProposalPrecision
import CurrentAFT.CurrentProposalResources
import CurrentAFT.CurrentPublicCompletion
import CurrentAFT.BinaryRejectionCap

/-! All proposal, completion and retry errors of the current finite-bit
public sampler are negligible at the dynamic precision `bits = security`. -/
namespace CurrentAFT.NumericalProposalRates
open AFT Filter NumericalWeightRates Polynomial
open scoped Polynomial Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentProposalDimensions.current

theorem polynomial_factor {error : ℕ → ℝ} (h : Negligible error) (polynomial : Polynomial ℕ) :
    Negligible (fun security => ((polynomial.eval security : ℕ) : ℝ)*error security) := by
  induction polynomial using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Nat.cast_add, add_mul] using hp.add hq
  | monomial power coefficient =>
    simpa only [Polynomial.eval_monomial, Nat.cast_mul, Nat.cast_pow, mul_assoc] using
      negligible_const_mul (h.mul_polynomial power) (coefficient : ℝ)

theorem dyadic_negligible : Negligible (fun security => 1/(2 : ℝ)^security) := by
  simpa only [pow_zero, mul_one, one_mul, div_pow, one_pow] using
    CalibrationPrecisionRates.polynomial_geometric_negligible 1 0 (1/2) (by norm_num) (by norm_num) (by norm_num)

theorem bounded_polynomial_factor {error factor : ℕ → ℝ} (h : Negligible error)
    (polynomial : Polynomial ℕ) (hfactor : ∀ security, |factor security| ≤ ((polynomial.eval security : ℕ) : ℝ)) :
    Negligible (fun security => factor security*error security) := by
  apply (polynomial_factor h polynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_mul, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg (polynomial.eval security) : (0 : ℝ) ≤ ((polynomial.eval security : ℕ) : ℝ))]
  exact mul_le_mul_of_nonneg_right (hfactor security) (abs_nonneg _)

def proposalPolynomial : Polynomial ℕ :=
  let size := CurrentProposalResources.countPolynomial
  size*(2+size*(64*(X+2)*size+(64*(X+2)*size*size+2)))+6*size+size+4*size^2

theorem proposal_nonneg (security bits : ℕ) :
    0 ≤ CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits := by
  unfold CurrentCoreProposalRates.error CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
  positivity

theorem proposal_bound (security bits : ℕ) :
    CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits ≤
      ((proposalPolynomial.eval security : ℕ) : ℝ)*(1/(2 : ℝ)^bits) := by
  let size := ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ)
  have hs := CurrentProposalResources.count_bounds security
  have hv := CurrentProposalDimensions.current_values security
  have hc : ((CurrentProposalDimensions.current security).controls : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.1
  have hl : (Parameters.legCount security : ℝ) ≤ size := by rw [← hv.2.1]; dsimp only [size]; exact_mod_cast hs.2.1
  have hq : (Parameters.modulus security : ℝ) ≤ size := by rw [← hv.1]; dsimp only [size]; exact_mod_cast hs.2.2.1
  have hb : ((CurrentProposalDimensions.current security).body : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.2.2.2.1
  have hd : ((CurrentProposalDimensions.current security).dimension : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.2.2.2.2
  have hd' : (Parameters.dimension security : ℝ) ≤ size := by rw [← hv.2.2.2.1]; exact hd
  have hp : 1/(2 : ℝ)^CurrentProposalPrecision.tableBits security bits ≤ 1/(2 : ℝ)^bits := by
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.le_add_right _ _
  have hsize : 0 ≤ size := Nat.cast_nonneg _
  have ht : 0 ≤ 1/(2 : ℝ)^bits := by positivity
  have hctrl : CurrentCoreProposalRates.controlError security (CurrentProposalPrecision.tableBits security bits) bits ≤
      (2+size*(64*(security+2)*size+(64*(security+2)*size*size+2)))*(1/(2 : ℝ)^bits) := by
    unfold CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
    calc
      _ ≤ 2*(1/(2 : ℝ)^bits)+size*(64*(security+2)*size+(64*(security+2)*size*size+2))*(1/(2 : ℝ)^bits) := by
        simp only [Parameters.base]
        push_cast
        gcongr
      _ = _ := by ring
  unfold CurrentCoreProposalRates.error CurrentCoreProposalRates.ticketError
  have hcn : 0 ≤ CurrentCoreProposalRates.controlError security (CurrentProposalPrecision.tableBits security bits) bits := by
    unfold CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
    positivity
  calc
    _ ≤ size*((2+size*(64*(security+2)*size+(64*(security+2)*size*size+2)))*(1/(2 : ℝ)^bits))+
        size*(5*(1/(2 : ℝ)^bits)+1/(2 : ℝ)^bits)+size*(1/(2 : ℝ)^bits)+
        2*size^2*(1/(2 : ℝ)^bits)+2*size^2*(1/(2 : ℝ)^bits) := by
      gcongr
    _ = _ := by
      simp only [proposalPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [size]
      ring

theorem proposal_negligible : Negligible (fun security =>
    CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security security) security) := by
  apply (polynomial_factor dyadic_negligible proposalPolynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (proposal_nonneg security security), abs_of_nonneg (by positivity)]
  exact proposal_bound security security

def completionPolynomial : Polynomial ℕ := 5*CurrentProposalResources.countPolynomial+1

theorem completion_bound (security : ℕ) :
    CurrentPublicCompletion.errorBound security security security security ≤
      ((completionPolynomial.eval security : ℕ) : ℝ)*(1/(2 : ℝ)^security) := by
  have hs := (CurrentProposalResources.count_bounds security).2.1
  rw [(CurrentProposalDimensions.current_values security).2.1] at hs
  have hl : (Parameters.legCount security : ℝ) ≤ ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ) := by exact_mod_cast hs
  unfold CurrentPublicCompletion.errorBound
  calc
    _ ≤ ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ)*
        (1/(2 : ℝ)^security+4*(1/(2 : ℝ)^security))+1/(2 : ℝ)^security := by gcongr
    _ = _ := by
      simp only [completionPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring

theorem completion_negligible : Negligible (fun security =>
    CurrentPublicCompletion.errorBound security security security security) := by
  apply (polynomial_factor dyadic_negligible completionPolynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (by unfold CurrentPublicCompletion.errorBound; positivity), abs_of_nonneg (by positivity)]
  exact completion_bound security

theorem retries_negligible {error : ℕ → ℝ} (h : Negligible error) :
    Negligible (fun security => ((BinaryRejectionCap.current security).count : ℝ)*error security) := by
  exact bounded_polynomial_factor h BinaryRejectionCap.countPolynomial (fun security => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast BinaryRejectionCap.count_bound security)

end
end CurrentAFT.NumericalProposalRates

import CurrentAFT.CurrentCoreProposalWork
import CurrentAFT.CurrentReferenceCacheWork
import AFT.BinarySamplingPolynomials

/-! Closed polynomial envelopes for the executed proposal primitives. -/
namespace CurrentAFT.CurrentProposalSamplerPolynomial
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
open CurrentProposalResources
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus
  CurrentProposalDimensions.current CurrentReferenceDraw.counts addCounter powerCounter

noncomputable def ticketPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  (2 * bits + 1) + binaryRationalDrawPolynomial count height (bits + count + 1) + 3

 theorem ticketPolynomial_eval (count height bits : Polynomial ℕ) (security : ℕ) :
    (ticketPolynomial count height bits).eval security = CurrentProbabilityArrayDraw.workBound
      (count.eval security) (height.eval security) (bits.eval security) := by
  simp only [ticketPolynomial, CurrentProbabilityArrayDraw.workBound, binaryRationalDrawPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]

 theorem ticketWork_mono {count other height larger bits precision : ℕ}
    (hc : count ≤ other) (hh : height ≤ larger) (hb : bits ≤ precision) :
    CurrentProbabilityArrayDraw.workBound count height bits ≤ CurrentProbabilityArrayDraw.workBound other larger precision := by
  have h := binaryRationalDrawWork_mono hc hh (Nat.add_le_add_right (Nat.add_le_add hb hc) 1)
  unfold CurrentProbabilityArrayDraw.workBound
  omega

noncomputable def widthWorkPolynomial : Polynomial ℕ :=
  2 * Polynomial.X + 1 + 49 * (6 * (Polynomial.X + 3)^50 + 4) + 2

 theorem width_work (security : ℕ) : (CurrentAnchorIndexDraw.width security).work ≤ widthWorkPolynomial.eval security := by
  have h := powerCounter_work (security + 2) 48
  simp only [CurrentAnchorIndexDraw.width, addCounter_value, addCounter_work,
    widthWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, powerCounterWork] at h ⊢
  norm_num only at h ⊢
  simpa only [show security + 2 + 1 = security + 3 by omega] using Nat.add_le_add_left (Nat.add_le_add_right h 2) (2*security+1)

 theorem width_count (security : ℕ) : (CurrentAnchorIndexDraw.width security).count ≤ countPolynomial.eval security := by
  rw [CurrentAnchorIndexDraw.width_value]
  have hb : 1 ≤ security + 2 := by omega
  have hp := Nat.pow_le_pow_right hb (by decide : 48 ≤ 160)
  simp only [countPolynomial, BinaryProposalMetadata.sizePolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
    Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]
  norm_num only
  omega

noncomputable def edgeCutoffWorkPolynomial : Polynomial ℕ :=
  2 * Polynomial.X + 1 + 3 * (6 * (Polynomial.X + 3)^4 + 4) + (2 * (Polynomial.X + 2)^2 + 1) +
    500 * ((Polynomial.X + 2)^2 + 4)^2 + 4

 theorem edgeCutoffWorkPolynomial_eval (security : ℕ) :
    edgeCutoffWorkPolynomial.eval security = CurrentEdgeDrawProgram.cutoffWork security := by
  simp only [edgeCutoffWorkPolynomial, CurrentEdgeDrawProgram.cutoffWork, powerCounterWork,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  norm_num only
  simp only [show security + 2 + 1 = security + 3 by omega]

noncomputable def edgeWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  let cutoff := (Polynomial.X + 2)^2
  edgeCutoffWorkPolynomial + CurrentGaussianBits.workPolynomial (bits + 1) +
    binaryRationalDrawPolynomial (2 * cutoff + 1) (500000000 * (cutoff + (bits + 1) + 2)^6)
      (bits + (2 * cutoff + 1) + 2) + 6 * cutoff + 7 + 2

 theorem edge_work (security : ℕ) (bits : Polynomial ℕ) :
    CurrentEdgeDrawProgram.workBound security (bits.eval security) ≤ (edgeWorkPolynomial bits).eval security := by
  have hc : DiffuseProfiles.edgeCutoff security ≤ (security + 2)^2 := by
    unfold DiffuseProfiles.edgeCutoff
    exact (Nat.div_le_self _ 2).trans (by
      simpa only [Parameters.sourceCutoff, Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have ht := binaryRationalDrawWork_mono (show 2 * DiffuseProfiles.edgeCutoff security + 1 ≤ 2 * (security + 2)^2 + 1 by omega)
    (Nat.le_refl (500000000 * (CurrentGaussianBits.budget security (bits.eval security + 1))^6))
    (show AFT.RationalNumerics.windowTicketBits (DiffuseProfiles.edgeCutoff security) (bits.eval security) ≤
      bits.eval security + (2 * (security + 2)^2 + 1) + 2 by
        unfold AFT.RationalNumerics.windowTicketBits; omega)
  simp only [edgeWorkPolynomial, edgeCutoffWorkPolynomial_eval, CurrentGaussianBits.workPolynomial_eval,
    binaryRationalDrawPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
  unfold CurrentEdgeDrawProgram.workBound CurrentWindowDraw.workBound
  unfold CurrentGaussianBits.budget at ht ⊢
  omega

end
end CurrentAFT.CurrentProposalSamplerPolynomial

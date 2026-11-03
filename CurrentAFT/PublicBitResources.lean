import CurrentAFT.PublicBitTapes
import CurrentAFT.CurrentProposalResources
import CurrentAFT.UniformPolynomialBound

/-! The actual flat random tape has polynomial length, including every
bounded rejection attempt and the once-only public placement. -/
namespace CurrentAFT.PublicBitResources
open AFT PublicBitTapes CurrentProposalResources
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

private theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (h : ∀ security, resource security ≤ polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,h⟩

attribute [local irreducible] UniformPolynomialBound

theorem polynomial_bits : UniformPolynomialBound (fun security => (PublicBitTapes.current security).bits) := by
  have hcontrols : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).controls) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).1)
  have hlegs : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).legs) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.1)
  have hcolors : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).colors) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.1)
  have hbody : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).body) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.2.1)
  have hdimension : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).dimension) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.2.2)
  have hq : UniformPolynomialBound Parameters.modulus :=
    hcolors.mono (fun n => by rw [(CurrentProposalDimensions.current_values n).1])
  have hnativeq : UniformPolynomialBound (fun n => (PublicParameterProgram.modulus n).count) :=
    hq.mono (fun n => by rw [PublicParameterProgram.modulus_value])
  have hsafe : UniformPolynomialBound (fun n => (CurrentReferenceDraw.counts n).safe) :=
    hq.mono (fun n => by rw [(CurrentReferenceDraw.counts_values n).2.2]; exact Nat.sub_le ..)
  have hanchor : UniformPolynomialBound (fun n => (CurrentAnchorIndexDraw.width n).count) := by
    refine of_bound _ anchorSizePolynomial (fun n => ?_)
    simp only [CurrentAnchorIndexDraw.width_value, DiffuseProfiles.anchorWidth_eq,
      anchorSizePolynomial, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat, Parameters.base, le_refl]
  have hcutoff : UniformPolynomialBound DiffuseProfiles.edgeCutoff := by
    refine of_bound _ cutoffSizePolynomial (fun n => ?_)
    simp only [cutoffSizePolynomial, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hretry : UniformPolynomialBound (fun n => (BinaryRejectionCap.current n).count) :=
    of_bound _ BinaryRejectionCap.countPolynomial BinaryRejectionCap.count_bound
  unfold PublicBitTapes.current materialized rejection completion charts core leg seed PublicBitTapes.control safe edge
    Encoding.prod Encoding.indexed bits flag RationalNumerics.windowTicketBits
  dsimp only
  repeat' first
    | exact hcontrols
    | exact hlegs
    | exact hcolors
    | exact hbody
    | exact hdimension
    | exact hq
    | exact hnativeq
    | exact hsafe
    | exact hanchor
    | exact hcutoff
    | exact hretry
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.add
    | apply UniformPolynomialBound.mul

end
end CurrentAFT.PublicBitResources

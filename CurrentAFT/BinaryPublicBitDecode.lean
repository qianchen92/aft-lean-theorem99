import CurrentAFT.BinaryPublicBitDecodeProgram
import CurrentAFT.BinaryPublicBitCodecResources

namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current

private theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (bound : ∀ security, resource security≤polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,bound⟩
attribute [local irreducible] UniformPolynomialBound

theorem work_uniform : UniformPolynomialBound workBound := by
  have hcontrols : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).controls) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).1)
  have hlegs : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).legs) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.1)
  have hcolors : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).colors) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.1)
  have hbody : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).body) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.2.1)
  have hdimension : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).dimension) :=
    of_bound _ CurrentProposalResources.countPolynomial (fun n => (CurrentProposalResources.count_bounds n).2.2.2.2)
  have hq : UniformPolynomialBound Parameters.modulus :=
    hcolors.mono (fun n => by rw [(CurrentProposalDimensions.current_values n).1])
  have hnativeq : UniformPolynomialBound (fun n => (PublicParameterProgram.modulus n).count) :=
    hq.mono (fun n => by rw [PublicParameterProgram.modulus_value])
  have hsafe : UniformPolynomialBound (fun n => (CurrentReferenceDraw.counts n).safe) :=
    hq.mono (fun n => by rw [(CurrentReferenceDraw.counts_values n).2.2]; exact Nat.sub_le ..)
  have hanchor : UniformPolynomialBound (fun n => (CurrentAnchorIndexDraw.width n).count) := by
    refine of_bound _ CurrentProposalResources.anchorSizePolynomial (fun n => ?_)
    simp only [CurrentAnchorIndexDraw.width_value,DiffuseProfiles.anchorWidth_eq,
      CurrentProposalResources.anchorSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_ofNat,Parameters.base,le_refl]
  have hcutoff : UniformPolynomialBound DiffuseProfiles.edgeCutoff := by
    refine of_bound _ CurrentProposalResources.cutoffSizePolynomial (fun n => ?_)
    simp only [CurrentProposalResources.cutoffSizePolynomial,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_ofNat,DiffuseProfiles.edgeCutoff,Parameters.sourceCutoff,Parameters.base]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hretry : UniformPolynomialBound (fun n => (BinaryRejectionCap.current n).count) :=
    of_bound _ BinaryRejectionCap.countPolynomial BinaryRejectionCap.count_bound
  have hprep : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).work) :=
    of_bound _ BinaryPublicBitSizes.workPolynomial BinaryPublicBitSizes.current_work
  have hactivation : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).activation) := by
    simpa only [BinaryPublicBitSizes.activation_value] using UniformPolynomialBound.identity.add (UniformPolynomialBound.constant 3)
  have hcontrol : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).control) := by
    simpa only [BinaryPublicBitSizes.control_value] using (UniformPolynomialBound.identity.add hnativeq).add (UniformPolynomialBound.constant 1)
  have hsafeBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).safe) := by
    simpa only [BinaryPublicBitSizes.safe_value] using (UniformPolynomialBound.identity.add hsafe).add (UniformPolynomialBound.constant 1)
  have hanchorBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).anchor) := by
    simpa only [BinaryPublicBitSizes.anchor_value] using (UniformPolynomialBound.identity.add hanchor).add (UniformPolynomialBound.constant 1)
  have hedge : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).edge) := by
    simpa only [BinaryPublicBitSizes.edge_value,RationalNumerics.windowTicketBits] using
      (UniformPolynomialBound.identity.add (((UniformPolynomialBound.constant 2).mul hcutoff).add (UniformPolynomialBound.constant 1))).add (UniformPolynomialBound.constant 2)
  have hchart : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).chart) := by
    simpa only [BinaryPublicBitSizes.chart_value] using
      (UniformPolynomialBound.identity.add (hq.mul (hq.mul hq))).add (UniformPolynomialBound.constant 1)
  have hbodyBits : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).body) := by
    simpa only [BinaryPublicBitSizes.body_value] using hbody.mul UniformPolynomialBound.identity
  have hendpoint : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).endpoint) := by
    simpa only [BinaryPublicBitSizes.endpoint_value] using hdimension.mul UniformPolynomialBound.identity
  have hc : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.controls) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hcontrols
  have hl : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.legs) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hlegs
  have hq' : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).dimensions.colors) := by
    simpa only [BinaryPublicBitSizes.dimensions_value] using hcolors
  have hr : UniformPolynomialBound (fun n => (BinaryPublicBitSizes.current n).retries.count) := by
    simpa only [BinaryPublicBitSizes.retries_value] using hretry
  have hcodec : UniformCodec (fun n => codec n (BinaryPublicBitSizes.current n) rfl) := by
    unfold codec materialized rejection completion charts core leg seed control safe edge withCount
    repeat' first
      | apply prod_uniform
      | apply indexed_uniform
      | apply bitsCast_uniform
      | apply bits_uniform
      | exact flag_uniform
      | exact hactivation
      | exact hcontrol
      | exact hsafeBits
      | exact hanchorBits
      | exact hedge
      | exact hchart
      | exact hbodyBits
      | exact hendpoint
      | exact hc
      | exact hl
      | exact hq'
      | exact hr
      | exact UniformPolynomialBound.identity
  exact (hprep.add (decode_uniform _ hcodec)).add (UniformPolynomialBound.constant 1)

theorem work_exists : ∃ polynomial : Polynomial ℕ, ∀ security, workBound security≤polynomial.eval security := by
  simpa only [UniformPolynomialBound] using work_uniform

noncomputable def workPolynomial : Polynomial ℕ := Classical.choose work_exists

theorem current_work (security : ℕ) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (current security word).work≤workPolynomial.eval security :=
  (current_bound security word).trans (Classical.choose_spec work_exists security)

end
end CurrentAFT.BinaryPublicBitDecode

import CurrentAFT.RootLocalDenominators
import CurrentAFT.PairedRootPlacement

/-! # All actual local denominators reconstruct the same-queue background -/
namespace CurrentAFT.RootBackgroundDenominatorProduct
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedOutputPlacement
  RootLocalDenominators RootUnselectedBlockChannel BackgroundPolynomialEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev InactiveKept {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  {index : selection.kept // index.val ∉ tagged}

def denominator {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => primaryPolynomial security
  | .inl (.inr _) => ordinaryPolynomial security
  | .inr index => positivePolynomial security queue index.val.val

theorem meanLaw_queue (security : ℕ) (queue : ℤ) :
    RootTaggedLocal.meanLaw security .queue queue = queueLaw security queue := by
  unfold RootTaggedLocal.meanLaw RootTaggedLocal.shiftedLaw UniformBodyProfiles.preRootLaw queueLaw
  exact RootIndependentBackground.rootReference_shift_mix security _

theorem all_block_product (security : ℕ) (queue : ℤ) :
    (∏ block : BlockIndex security, positivePolynomial security queue block) = fixedQueueGenerating security queue := by
  simp only [BlockIndex, Fintype.prod_sum_type, positivePolynomial, meanLaw_free, meanLaw_queue,
    uniformReference_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold fixedQueueGenerating
  change LegPolynomialEvaluation.legGenerating security ^ Parameters.legCount security *
    (RepresentedPolynomial.singleGenerating (FringeCertificate.uniformProfile security)
      (BackgroundCertificates.convolvedCenterLaw security).weight ^ BackgroundPopulationBounds.freeCount security * _) = _
  ring

/-- The paired denominator consumes the actual compensator and complete
leg exactly once; every other original block is retained. -/
theorem selected_kept_product {security r s : ℕ} (queue : ℤ) (selection : Selection security r s) :
    (∏ _index : Fin r, primaryPolynomial security) * (∏ _index : Fin s, ordinaryPolynomial security) *
      (∏ index : selection.kept, positivePolynomial security queue index.val) =
      ∏ block : BlockIndex security, positivePolynomial security queue block := by
  have hsplit := Equiv.prod_comp (blockEquiv selection) (positivePolynomial security queue)
  rw [← hsplit]
  simp only [Fintype.prod_sum_type, blockEquiv_removed, blockEquiv_kept,
    RemovedLabel, Selection.removedEmbedding, Function.Embedding.coeFn_mk]
  have hcenter (index : Fin (centerCount security)) :
      positivePolynomial security queue (.inr (.inl index)) = ordinaryPolynomial security :=
    (ordinary_eq_unselected_center security queue index).symm
  simp_rw [hcenter]
  simp only [primaryPolynomial, positivePolynomial, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  ac_rfl

/-- Multiplication restores all mean factors, including roots outside the
active tensor. No denominator is divided or assumed pointwise nonzero. -/
theorem denominator_product {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (∏ group : ActiveGroup selection tagged, denominator queue selection tagged group) *
      (∏ index : InactiveKept selection tagged, positivePolynomial security queue index.val.val) =
      fixedQueueGenerating security queue := by
  have hkept := Fintype.prod_subtype_mul_prod_subtype (fun index : selection.kept => index.val ∈ tagged)
    (fun index : selection.kept => positivePolynomial security queue index.val)
  change (∏ index : HitKept selection tagged, positivePolynomial security queue index.val.val) *
    (∏ index : InactiveKept selection tagged, positivePolynomial security queue index.val.val) =
      ∏ index : selection.kept, positivePolynomial security queue index.val at hkept
  simp only [Fintype.prod_sum_type, denominator]
  rw [mul_assoc, hkept, selected_kept_product, all_block_product]

end
end CurrentAFT.RootBackgroundDenominatorProduct

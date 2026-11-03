import CurrentAFT.CurrentProposalSamplerPolynomial

/-! Closed polynomial bounds for every buffer of the executed current core proposal. -/
namespace CurrentAFT.CurrentCorePolynomialWork
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalNumerics
open CurrentProposalResources CurrentProposalSamplerPolynomial
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
attribute [local irreducible] PublicParameterProgram.modulus CurrentReferenceDraw.counts CurrentProposalDimensions.current

noncomputable def safePolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  CurrentReferenceCacheWork.countsWorkPolynomial + binaryUniformDrawPolynomial countPolynomial bits + 2 * countPolynomial + 3
noncomputable def anchorPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  widthWorkPolynomial + binaryUniformDrawPolynomial countPolynomial bits + 1
noncomputable def activationPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  2 * primitiveWorkPolynomial height + ticketPolynomial 2 (height + 1) bits + 6
noncomputable def seedPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  activationPolynomial height bits + anchorPolynomial bits + 2 * edgeWorkPolynomial bits + 5
noncomputable def controlPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + ticketPolynomial countPolynomial height bits + 1 +
    CurrentReferenceCacheWork.countsWorkPolynomial + ticketPolynomial countPolynomial height bits + 2 * countPolynomial + 3 + 2
noncomputable def legPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  seedPolynomial height bits + safePolynomial bits + 2
noncomputable def permutationPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPermutationFromTapePolynomial countPolynomial bits +
    countPolynomial * (countPolynomial * (9 * countPolynomial + 8) + 3) + 5

 theorem safe_work (security : ℕ) (bits : Polynomial ℕ) :
    CurrentSafeDraw.workBound security (bits.eval security) ≤ (safePolynomial bits).eval security := by
  have hc := (CurrentReferenceCacheWork.native_bounds security).2.1
  have hm := (CurrentReferenceCacheWork.native_bounds security).2.2
  have hw := CurrentReferenceCacheWork.counts_work security
  have hu := binaryUniformDrawWork_mono hc (Nat.le_refl (bits.eval security))
  simp only [safePolynomial, binaryUniformDrawPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  unfold CurrentSafeDraw.workBound
  omega

 theorem anchor_work (security : ℕ) (bits : Polynomial ℕ) :
    CurrentAnchorIndexDraw.workBound security (bits.eval security) ≤ (anchorPolynomial bits).eval security := by
  have hw := width_work security
  have hu := binaryUniformDrawWork_mono (width_count security) (Nat.le_refl (bits.eval security))
  simp only [anchorPolynomial, binaryUniformDrawPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_one]
  unfold CurrentAnchorIndexDraw.workBound
  omega

 theorem activation_work (security : ℕ) (height bits : Polynomial ℕ) :
    CurrentActivationDraw.workBound (height.eval security) (bits.eval security) ≤
      (activationPolynomial height bits).eval security := by
  simp only [activationPolynomial, CurrentActivationDraw.workBound, ticketPolynomial_eval,
    primitiveWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
  exact le_rfl

 theorem seed_work (security : ℕ) (height bits : Polynomial ℕ) :
    CurrentPublicSeedDraw.workBound security (height.eval security) (bits.eval security) ≤
      (seedPolynomial height bits).eval security := by
  have ha := activation_work security height bits
  have hi := anchor_work security bits
  have he := edge_work security bits
  simp only [seedPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  unfold CurrentPublicSeedDraw.workBound
  omega

 theorem control_work (security : ℕ) (height bits : Polynomial ℕ) :
    CurrentCoreProposalWork.controlWork security (height.eval security) (bits.eval security) ≤
      (controlPolynomial height bits).eval security := by
  have hq := (CurrentReferenceCacheWork.native_bounds security).1
  have hs := (CurrentReferenceCacheWork.native_bounds security).2.1
  have hm := (CurrentReferenceCacheWork.native_bounds security).2.2
  have hp := PublicParameterProgram.modulus_polynomial_work security
  have hr := CurrentReferenceCacheWork.counts_work security
  have hfirst := ticketWork_mono hq (Nat.le_refl (height.eval security)) (Nat.le_refl (bits.eval security))
  have hsecond := ticketWork_mono hs (Nat.le_refl (height.eval security)) (Nat.le_refl (bits.eval security))
  simp only [controlPolynomial, ticketPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  unfold CurrentCoreProposalWork.controlWork
  omega

 theorem leg_work (security : ℕ) (height bits : Polynomial ℕ) :
    CurrentCoreProposalWork.legWork security (height.eval security) (bits.eval security) ≤
      (legPolynomial height bits).eval security := by
  have hs := seed_work security height bits
  have hb := safe_work security bits
  simp only [legPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
  unfold CurrentCoreProposalWork.legWork
  omega

private theorem permutationFromTape_mono {count other bits : ℕ} (hc : count ≤ other) :
    binaryPermutationFromTapeWork count bits ≤ binaryPermutationFromTapeWork other bits := by
  have hchoice := binaryPermutationChoiceWork_mono hc (Nat.le_refl bits)
  unfold binaryPermutationFromTapeWork binaryGroupTapeWork binaryTapeCellWork binaryPermutationRowsWork
  gcongr

 theorem permutation_work (security count : ℕ) (bits : Polynomial ℕ)
    (hc : count ≤ countPolynomial.eval security) :
    CurrentPermutationDraw.workBound count (bits.eval security) ≤ (permutationPolynomial bits).eval security := by
  have ht := permutationFromTape_mono (bits := bits.eval security) hc
  simp only [permutationPolynomial, binaryPermutationFromTapePolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  unfold CurrentPermutationDraw.workBound CurrentPermutationDraw.inverseScanWork
  norm_num only [Nat.add_assoc]
  gcongr

noncomputable def workPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial +
    (countPolynomial * (5 * countPolynomial + 5 + controlPolynomial height bits + 4) + 2) +
    (countPolynomial * (legPolynomial height bits + 2) + 2) +
    (countPolynomial * (safePolynomial bits + 2) + 2) +
    permutationPolynomial bits + permutationPolynomial bits +
    (metadataWorkPolynomial + countPolynomial * (6 * countPolynomial + 10) + 4) +
    countPolynomial * bits + countPolynomial * bits + 9

 theorem workBound_polynomial (security : ℕ) (height bits : Polynomial ℕ) :
    CurrentCoreProposalWork.workBound security (height.eval security) (bits.eval security) ≤
      (workPolynomial height bits).eval security := by
  rcases count_bounds security with ⟨hcontrols, hlegs, hcolors, hbody, hdimension⟩
  have hmeta := metadata_work security
  have hcontrol := control_work security height bits
  have hleg := leg_work security height bits
  have hsafe := safe_work security bits
  have hbodyperm := permutation_work security (CurrentProposalDimensions.current security).body bits hbody
  have hendpointperm := permutation_work security (CurrentProposalDimensions.current security).dimension bits hdimension
  have hindex : CurrentPublicIndexProgram.workBound security ≤ 5 * countPolynomial.eval security + 5 := by
    unfold CurrentPublicIndexProgram.workBound
    omega
  have hcb := Nat.add_le_add_right (Nat.mul_le_mul hcontrols
    (Nat.add_le_add_right (Nat.add_le_add hindex hcontrol) 4)) 2
  have hlb := Nat.add_le_add_right (Nat.mul_le_mul hlegs (Nat.add_le_add_right hleg 2)) 2
  have hqb := Nat.add_le_add_right (Nat.mul_le_mul hcolors (Nat.add_le_add_right hsafe 2)) 2
  have hgb : CurrentCoreProposalWork.gatherWork security ≤ metadataWorkPolynomial.eval security +
      countPolynomial.eval security * (6 * countPolynomial.eval security + 10) + 4 := by
    unfold CurrentCoreProposalWork.gatherWork
    gcongr
    omega
  have hb := Nat.mul_le_mul_right (bits.eval security) hbody
  have hd := Nat.mul_le_mul_right (bits.eval security) hdimension
  simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  unfold CurrentCoreProposalWork.workBound
  omega

 theorem draw_polynomial_work (security tableBits : ℕ) (height bits : Polynomial ℕ)
    (cache : CurrentReferenceDraw.Cache security tableBits)
    (hp : ∀ index, HeightBound (cache.primary.data.get index).decode (height.eval security))
    (hb : ∀ index, HeightBound (cache.body.data.get index).decode (height.eval security))
    (ha : HeightBound cache.activation.decode (height.eval security))
    (word : CurrentCoreProposal.Tapes security (bits.eval security)) :
    (CurrentCoreProposal.draw security tableBits (bits.eval security) cache word).work ≤
      (workPolynomial height bits).eval security :=
  (CurrentCoreProposalWork.draw_work security tableBits (bits.eval security) (height.eval security) cache hp hb ha word).trans
    (workBound_polynomial security height bits)

end
end CurrentAFT.CurrentCorePolynomialWork

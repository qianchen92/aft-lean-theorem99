import CurrentAFT.CurrentProposalDimensions
import CurrentAFT.CurrentPublicShiftCost

/-! Explicit polynomial resources for current proposal metadata and public shifts. -/
namespace CurrentAFT.CurrentProposalResources
open AFT AFT.BinaryArithmetic CurrentProposalDimensions
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
attribute [local irreducible] BinaryProposalMetadata.counts CurrentProposalDimensions.current

noncomputable def countPolynomial : Polynomial ℕ := 3 * BinaryProposalMetadata.sizePolynomial
noncomputable def metadataWorkPolynomial : Polynomial ℕ :=
  BinaryProposalMetadata.countsWorkPolynomial + 11 * BinaryProposalMetadata.sizePolynomial + 13

 theorem count_bounds (security : ℕ) :
    (current security).controls ≤ countPolynomial.eval security ∧
    (current security).legs ≤ countPolynomial.eval security ∧
    (current security).colors ≤ countPolynomial.eval security ∧
    (current security).body ≤ countPolynomial.eval security ∧
    (current security).dimension ≤ countPolynomial.eval security := by
  rcases BinaryProposalMetadata.counts_bounds security with ⟨hq, hl, hb⟩
  simp only [countPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat, BinaryProposalMetadata.sizePolynomial_eval]
  simp only [CurrentProposalDimensions.current, addCounter_value, subtractCounter_value, doubleCounter_value]
  omega

 theorem metadata_work (security : ℕ) :
    (current security).work ≤ metadataWorkPolynomial.eval security := by
  let sizes := BinaryProposalMetadata.counts security
  have hs := BinaryProposalMetadata.counts_work security
  have hl : sizes.legs ≤ BinaryProposalMetadata.sizeBound security := (BinaryProposalMetadata.counts_bounds security).2.1
  have hb : sizes.population ≤ BinaryProposalMetadata.sizeBound security := (BinaryProposalMetadata.counts_bounds security).2.2
  have hn := subtractCounter_work_left sizes.population sizes.colors
  have ho := subtractCounter_work_left (subtractCounter sizes.population sizes.colors).count (doubleCounter sizes.legs).count
  have hnc : (subtractCounter sizes.population sizes.colors).count ≤ sizes.population := by
    rw [subtractCounter_value]; exact Nat.sub_le _ _
  change sizes.work ≤ _ at hs
  unfold CurrentProposalDimensions.current
  change sizes.work + (doubleCounter sizes.legs).work +
    (addCounter sizes.population (doubleCounter sizes.legs).count).work +
    (subtractCounter sizes.population sizes.colors).work +
    (subtractCounter (subtractCounter sizes.population sizes.colors).count (doubleCounter sizes.legs).count).work +
    (addCounter sizes.legs _).work + 6 ≤ _
  simp only [doubleCounter_work, addCounter_work, metadataWorkPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    BinaryProposalMetadata.countsWorkPolynomial_eval, BinaryProposalMetadata.sizePolynomial_eval]
  omega

noncomputable def primeSizePolynomial : Polynomial ℕ := 131072 * (Polynomial.X + 2)^64
noncomputable def anchorSizePolynomial : Polynomial ℕ := (Polynomial.X + 2)^48
noncomputable def cutoffSizePolynomial : Polynomial ℕ := (Polynomial.X + 2)^2

noncomputable def shiftWorkPolynomial : Polynomial ℕ :=
  let q := primeSizePolynomial
  let width := anchorSizePolynomial
  let cutoff := cutoffSizePolynomial
  PublicParameterProgram.workPolynomial + 2 * Polynomial.X + 1 +
    49 * (6 * (Polynomial.X + 3)^50 + 4) +
    ((15*q + 8*q + 9) + (2*width + 1) + 50*(width+width+1)^2 +
      (50*(cutoff+1)^2+1) + (50*(cutoff+1)^2+1) +
      (20*(cutoff+cutoff)+13) + (20*(width+width+cutoff+cutoff+1)+9)+7) + 3

 theorem shiftWorkPolynomial_eval (security : ℕ) :
    shiftWorkPolynomial.eval security = CurrentPublicShiftProgram.workBound security := by
  simp only [shiftWorkPolynomial, primeSizePolynomial, anchorSizePolynomial, cutoffSizePolynomial,
    CurrentPublicShiftProgram.workBound, CurrentPublicShiftProgram.programWork, powerCounterWork,
    PublicParameterProgram.workPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  norm_num only
  simp only [show security + 2 + 1 = security + 3 by omega, Nat.add_assoc]

 theorem publicShift_work (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) :
    (CurrentPublicShiftProgram.current security primary seed).work ≤ shiftWorkPolynomial.eval security := by
  rw [shiftWorkPolynomial_eval]
  exact CurrentPublicShiftProgram.current_work security primary seed

end
end CurrentAFT.CurrentProposalResources

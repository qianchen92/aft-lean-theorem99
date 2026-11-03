import CurrentAFT.CurrentReferenceDraw
import CurrentAFT.CurrentProposalResources

/-! Polynomial preparation of the same reference cache for proposal sampling. -/
namespace CurrentAFT.CurrentReferenceCacheWork
open AFT AFT.BinaryArithmetic AFT.RationalNumerics CurrentReferenceDraw
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
attribute [local irreducible] PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  CurrentReferenceDraw.counts BinaryReferenceTables.current
  addCounter multiplyCounter doubleCounter subtractCounter

noncomputable def countsWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + BinaryActivationProgram.cutoffWorkPolynomial +
    (2 * (Polynomial.X + 2)^2 + 1) + (3 * (2 * ((Polynomial.X + 2)^2 + 1) + 3) + 1) +
    (9 * (Polynomial.X + 2)^2 + 1) +
    (2 * CurrentProposalResources.primeSizePolynomial + 2) + 6

 theorem counts_work (security : ℕ) : (counts security).work ≤ countsWorkPolynomial.eval security := by
  let colors := PublicParameterProgram.modulus security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let double := doubleCounter margin.count
  have hc := PublicParameterProgram.modulus_work security
  have hw := BinaryActivationProgram.cutoff_work security
  have hq : colors.count ≤ 131072 * (security + 2)^64 := by
    rw [show colors.count = Parameters.modulus security from PublicParameterProgram.modulus_value security]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hwindow : window.count ≤ (security + 2)^2 := by
    have hv : window.count = (security + 2)^2 - 1 := BinaryActivationProgram.cutoff_value security
    exact hv ▸ Nat.sub_le _ _
  have hs : square.count ≤ (security + 2)^2 + 1 := by
    rw [show square.count = window.count + 1 from addCounter_value _ _]
    exact Nat.add_le_add_right hwindow 1
  have hm : margin.count = 3 * (security + 2)^2 := BinaryBodyProgram.margin_value security
  have hsub := subtractCounter_work_left colors.count double.count
  change colors.work ≤ _ at hc
  change window.work ≤ _ at hw
  unfold CurrentReferenceDraw.counts
  change colors.work + window.work + square.work + margin.work + double.work +
    (subtractCounter colors.count double.count).work + 6 ≤ _
  have hsw : square.work = 2 * window.count + 1 := addCounter_work _ _
  have hmw : margin.work = 3 * (2 * square.count + 3) + 1 := multiplyCounter_work _ _
  have hdw : double.work = 3 * margin.count + 1 := doubleCounter_work _
  have hmwbound : margin.work ≤ 3 * (2 * ((security + 2)^2 + 1) + 3) + 1 := by
    rw [hmw]
    gcongr
  rw [hm] at hdw
  simp only [countsWorkPolynomial, CurrentProposalResources.primeSizePolynomial,
    PublicParameterProgram.workPolynomial_eval, BinaryActivationProgram.cutoffWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

 theorem native_bounds (security : ℕ) :
    (PublicParameterProgram.modulus security).count ≤ CurrentProposalResources.countPolynomial.eval security ∧
    (counts security).safe ≤ CurrentProposalResources.countPolynomial.eval security ∧
    (counts security).margin ≤ CurrentProposalResources.countPolynomial.eval security := by
  have hq := (BinaryProposalMetadata.counts_bounds security).1
  rw [(BinaryProposalMetadata.counts_value security).1] at hq
  have hb : 1 ≤ security + 2 := by omega
  have hbase : (security + 2)^2 ≤ (security + 2)^160 := Nat.pow_le_pow_right hb (by decide)
  rcases counts_values security with ⟨_, hm, hs⟩
  simp only [CurrentProposalResources.countPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    BinaryProposalMetadata.sizePolynomial_eval]
  constructor
  · rw [PublicParameterProgram.modulus_value]
    omega
  constructor
  · rw [hs]
    unfold CurrentSafePaletteIndex.count
    exact (Nat.sub_le _ _).trans (by omega)
  · rw [hm, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
    unfold BinaryProposalMetadata.sizeBound
    omega

 theorem prepare_work (security bits : ℕ) (input : BinaryReferenceTables.Result security)
    (hinput : input = BinaryReferenceTables.current security bits) :
    (prepare security bits input hinput).work ≤ (countsWorkPolynomial.eval security) + centerDataWork security + 3 := by
  have hm := counts_work security
  have hd := centerData_work security input
  change (counts security).work + (centerData security input).work + 3 ≤ _
  omega

 theorem prepare_heights (security : ℕ) (precision : Polynomial ℕ) :
    let input := BinaryReferenceTables.current security (precision.eval security)
    let cache := (prepare security (precision.eval security) input rfl).value
    let height := (BinaryReferenceTables.heightPolynomial precision).eval security
    (∀ index, HeightBound (cache.primary.data.get index).decode height) ∧
    (∀ index, HeightBound (cache.body.data.get index).decode height) ∧ HeightBound cache.activation.decode height := by
  have h := BinaryReferenceTables.current_bounds security precision
  refine ⟨h.1, ?_, h.2.2.2.1⟩
  intro index
  rw [prepare_body, centerData_get]
  exact h.2.1 _

end
end CurrentAFT.CurrentReferenceCacheWork

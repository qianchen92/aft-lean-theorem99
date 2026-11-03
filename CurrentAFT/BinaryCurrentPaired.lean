import CurrentAFT.BinaryReferenceTables
import CurrentAFT.BinaryPairedScore
import CurrentAFT.RationalPairedLiftProgram

/-! # The current paired evaluator with its reference cache generated

Only the score vector is an input.  Every reference table is produced by
`BinaryReferenceTables.current`, including its full production cost.
-/
namespace CurrentAFT.BinaryCurrentPaired
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def scoreAt {count : ℕ} (score : Vector RationalBits count) (output : ℕ) : ℚ :=
  if h : output < count then (score.get ⟨output, h⟩).decode else 0

theorem scoreAt_index {count : ℕ} (score : Vector RationalBits count) (index : Fin count) :
    scoreAt score index.val = (score.get index).decode := by
  simp only [scoreAt, dif_pos index.isLt]

def current (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input output : Fin (PublicParameterProgram.modulus security).count) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let result := BinaryPairedScore.current references.primary references.center score references.anchor references.activation input output
  ⟨result.data, references.work+result.work+2⟩

theorem current_value (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input output : Fin (PublicParameterProgram.modulus security).count) :
    (current security bits score input output).data.decode =
      RationalPairedLiftProgram.current security bits (scoreAt score) input.val output.val := by
  unfold current
  rw [BinaryPairedScore.current_value, BinaryReferenceTables.center_value, BinaryReferenceTables.activation_value]
  simp_rw [BinaryReferenceTables.primary_value, BinaryReferenceTables.anchor_value]
  unfold RationalPairedLiftProgram.current RationalPairedLiftProgram.anchorProfile
  simp only [scoreAt_index]

noncomputable section

noncomputable def boundPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+scoreBits
noncomputable def heightPolynomial (count bound : Polynomial ℕ) : Polynomial ℕ :=
  (count+1)*(3*bound+1)+3*bound+3
noncomputable def evaluationWorkPolynomial (count bound : Polynomial ℕ) : Polynomial ℕ :=
  count*(13*count+18+3*primitiveWorkPolynomial (heightPolynomial count bound))+
    6*count+14+5*primitiveWorkPolynomial (heightPolynomial count bound)
noncomputable def currentHeightPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  heightPolynomial BinaryProposalMetadata.sizePolynomial (boundPolynomial precision scoreBits)
noncomputable def currentWorkPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+
    evaluationWorkPolynomial BinaryProposalMetadata.sizePolynomial (boundPolynomial precision scoreBits)+2

private theorem bounds_mono {count count' bound bound' : ℕ} (hc : count ≤ count') (hb : bound ≤ bound') :
    BinaryPairedScore.height count bound ≤ BinaryPairedScore.height count' bound' ∧
    BinaryPairedScore.work count bound ≤ BinaryPairedScore.work count' bound' := by
  constructor
  · unfold BinaryPairedScore.height; gcongr
  · unfold BinaryPairedScore.work BinaryPairedScore.height primitiveWorkBound; gcongr

theorem current_bounds (security : ℕ) (precision scoreBits : Polynomial ℕ)
    (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input output : Fin (PublicParameterProgram.modulus security).count)
    (hs : ∀ index, HeightBound (score.get index).decode (scoreBits.eval security)) :
    HeightBound (current security (precision.eval security) score input output).data.decode
      ((currentHeightPolynomial precision scoreBits).eval security) ∧
    (current security (precision.eval security) score input output).work ≤
      (currentWorkPolynomial precision scoreBits).eval security := by
  let references := BinaryReferenceTables.current security (precision.eval security)
  let bound := (boundPolynomial precision scoreBits).eval security
  let count := (PublicParameterProgram.modulus security).count
  have href := BinaryReferenceTables.current_bounds security precision
  have br : (BinaryReferenceTables.heightPolynomial precision).eval security ≤ bound := by
    simp only [bound, boundPolynomial, Polynomial.eval_add]; exact Nat.le_add_right _ _
  have bs : scoreBits.eval security ≤ bound := by
    simp only [bound, boundPolynomial, Polynomial.eval_add]; exact Nat.le_add_left _ _
  have hp (index : Fin count) := (href.1 index).mono br
  have hb (index : Fin count) := (href.2.1 index).mono br
  have ha (input output : Fin count) := (href.2.2.1 input output).mono br
  have hr := href.2.2.2.1.mono br
  have hscore (index : Fin count) := (hs index).mono bs
  have hh := BinaryPairedScore.current_height references.primary references.center score references.anchor references.activation
    input output bound hp hb hscore ha hr
  have hw := BinaryPairedScore.current_work references.primary references.center score references.anchor references.activation
    input output bound hp hb hscore ha hr
  have hc : count ≤ BinaryProposalMetadata.sizePolynomial.eval security := by
    change (PublicParameterProgram.modulus security).count ≤ BinaryProposalMetadata.sizePolynomial.eval security
    rw [BinaryProposalMetadata.sizePolynomial_eval, PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.counts_value security).1 ▸ (BinaryProposalMetadata.counts_bounds security).1
  have hm := bounds_mono hc (le_refl bound)
  constructor
  · apply hh.mono
    apply hm.1.trans_eq
    simp only [currentHeightPolynomial, heightPolynomial, BinaryPairedScore.height,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
    rfl
  · have he : BinaryPairedScore.work count bound ≤
        (evaluationWorkPolynomial BinaryProposalMetadata.sizePolynomial (boundPolynomial precision scoreBits)).eval security := by
      apply hm.2.trans_eq
      simp only [evaluationWorkPolynomial, heightPolynomial, BinaryPairedScore.work, BinaryPairedScore.height,
        primitiveWorkPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
      rfl
    change references.work+(BinaryPairedScore.current references.primary references.center score references.anchor references.activation input output).work+2 ≤ _
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    exact Nat.add_le_add_right (Nat.add_le_add href.2.2.2.2 (hw.trans he)) 2

end
end CurrentAFT.BinaryCurrentPaired

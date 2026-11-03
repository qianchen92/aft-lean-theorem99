import CurrentAFT.BinaryPrimaryTable
import CurrentAFT.BinaryAnchorTable
import CurrentAFT.BinaryCenterKernel

/-! # Generated binary caches for all current reference probabilities

The center table reuses the very same primary table, anchor matrix and
activation entry that are returned to the paired-score evaluator.
-/
namespace CurrentAFT.BinaryReferenceTables
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter PublicParameterProgram.modulus BinaryActivationProgram.cutoff

structure Result (security : ℕ) where
  primary : Vector RationalBits (PublicParameterProgram.modulus security).count
  center : Vector RationalBits (PublicParameterProgram.modulus security).count
  anchor : Vector (Vector RationalBits (PublicParameterProgram.modulus security).count) (PublicParameterProgram.modulus security).count
  activation : RationalBits
  work : ℕ

def current (security bits : ℕ) : Result security :=
  let primary := BinaryPrimaryTable.current security bits
  let anchor := BinaryAnchorTable.current security bits
  let metadata := BinaryProposalMetadata.current security
  let activation := BinaryActivationProgram.current security bits
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let center := buildArray (PublicParameterProgram.modulus security).count
    (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data)
  ⟨primary.data, center.data, anchor.data, activation.data,
    primary.work+anchor.work+metadata.work+activation.work+window.work+square.work+margin.work+center.work+8⟩

theorem primary_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).primary.get index).decode = RationalProposalProgram.primary security bits index.val :=
  BinaryPrimaryTable.current_value security bits index

theorem anchor_value (security bits : ℕ) (primary output : Fin (PublicParameterProgram.modulus security).count) :
    (((current security bits).anchor.get primary).get output).decode =
      RationalProposalProgram.anchor security bits primary.val output.val :=
  BinaryAnchorTable.current_value security bits primary output

theorem activation_value (security bits : ℕ) :
    (current security bits).activation.decode = LocalPairProgram.activationApprox security bits :=
  BinaryActivationProgram.current_value security bits

theorem center_value (security bits : ℕ) (output : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).center.get output).decode = RationalProposalProgram.center security bits output.val := by
  have hc : (BinaryProposalMetadata.current security).colors.decode = ((PublicParameterProgram.modulus security).count:ℚ) := by
    rw [PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.current_value security).1
  have hl := (BinaryProposalMetadata.current_value security).2.1
  have hp : (BinaryProposalMetadata.current security).population.decode =
      ((PublicParameterProgram.modulus security).count*(security+2)^96:ℕ) := by
    rw [PublicParameterProgram.modulus_value]
    exact (BinaryProposalMetadata.current_value security).2.2
  change ((buildArray (PublicParameterProgram.modulus security).count
    (BinaryCenterKernel.point (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count
      (BinaryProposalMetadata.current security) (BinaryActivationProgram.current security bits).data
      (BinaryPrimaryTable.current security bits).data (BinaryAnchorTable.current security bits).data)).data.get output).decode = _
  rw [buildArray_get, BinaryCenterKernel.point_value, BinaryBodyProgram.margin_value, hc, hl, hp,
    BinaryActivationProgram.current_value]
  simp_rw [BinaryPrimaryTable.current_value, BinaryAnchorTable.current_value]
  unfold RationalProposalProgram.center RationalProposalProgram.compensationApprox
    RationalProposalProgram.anchorPrimary RationalProposalProgram.safeEntry
  push_cast
  ring

noncomputable section

noncomputable def referenceHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryPrimaryTable.currentHeightPolynomial precision+
    BinaryAnchorTable.currentHeightPolynomial precision+BinaryActivationProgram.currentHeightPolynomial precision+1
noncomputable def marginPolynomial : Polynomial ℕ := 3*(Polynomial.X+2)^2
noncomputable def centerHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCenterKernel.heightPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  referenceHeightPolynomial precision+centerHeightPolynomial precision
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryTable.currentWorkPolynomial precision+BinaryAnchorTable.currentWorkPolynomial precision+
    BinaryProposalMetadata.currentWorkPolynomial+BinaryActivationProgram.currentWorkPolynomial precision+
    BinaryActivationProgram.cutoffWorkPolynomial+(2*(Polynomial.X+2)^2+1)+(3*(2*(Polynomial.X+2)^2+3)+1)+
    BinaryProposalMetadata.sizePolynomial*
      (BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)+2)+10

private theorem centerBounds_mono {count count' margin margin' bound bound' : ℕ}
    (hc : count ≤ count') (hm : margin ≤ margin') (hb : bound ≤ bound') :
    BinaryCenterKernel.height count margin bound ≤ BinaryCenterKernel.height count' margin' bound' ∧
    BinaryCenterKernel.work count margin bound ≤ BinaryCenterKernel.work count' margin' bound' := by
  constructor
  · unfold BinaryCenterKernel.height BinaryCenterFormula.height BinaryCenterKernel.formulaBound BinaryCenterKernel.integerBound
    gcongr
  · unfold BinaryCenterKernel.work BinaryCenterFormula.work BinaryCenterFormula.height
      BinaryCenterKernel.formulaBound BinaryCenterKernel.integerBound BinaryWindowAverage.sumWork BinaryWindowAverage.termWork
      binarySliceProbabilityWork binaryEndpointProbabilityWork binaryIntervalProbabilityWork primitiveWorkBound
    gcongr

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) :
    (∀ index, HeightBound ((current security (precision.eval security)).primary.get index).decode ((heightPolynomial precision).eval security)) ∧
    (∀ index, HeightBound ((current security (precision.eval security)).center.get index).decode ((heightPolynomial precision).eval security)) ∧
    (∀ input output, HeightBound (((current security (precision.eval security)).anchor.get input).get output).decode ((heightPolynomial precision).eval security)) ∧
    HeightBound (current security (precision.eval security)).activation.decode ((heightPolynomial precision).eval security) ∧
    (current security (precision.eval security)).work ≤ (currentWorkPolynomial precision).eval security := by
  let primary := BinaryPrimaryTable.current security (precision.eval security)
  let anchor := BinaryAnchorTable.current security (precision.eval security)
  let metadata := BinaryProposalMetadata.current security
  let activation := BinaryActivationProgram.current security (precision.eval security)
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let colors := (PublicParameterProgram.modulus security).count
  let H := (referenceHeightPolynomial precision).eval security
  let Q := BinaryProposalMetadata.sizePolynomial.eval security
  let M := marginPolynomial.eval security
  have hq : colors ≤ Q := by
    change (PublicParameterProgram.modulus security).count ≤ BinaryProposalMetadata.sizePolynomial.eval security
    rw [BinaryProposalMetadata.sizePolynomial_eval]
    exact (PublicParameterProgram.modulus_value security) ▸ ((BinaryProposalMetadata.counts_value security).1 ▸ (BinaryProposalMetadata.counts_bounds security).1)
  have hm : margin.count = M := by
    change (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count = marginPolynomial.eval security
    rw [BinaryBodyProgram.margin_value]
    simp only [marginPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  have hp := BinaryPrimaryTable.current_bounds security precision
  have ha := BinaryAnchorTable.current_bounds security precision
  have hd := BinaryProposalMetadata.current_height security
  have hr := (BinaryActivationProgram.current_bounds security (precision.eval security)).1
  rw [← BinaryActivationProgram.currentHeightPolynomial_eval precision security] at hr
  have bsize : BinaryProposalMetadata.sizeBound security ≤ H := by
    simp only [H, referenceHeightPolynomial, Polynomial.eval_add, Polynomial.eval_one, BinaryProposalMetadata.sizePolynomial_eval]
    omega
  have bp : (BinaryPrimaryTable.currentHeightPolynomial precision).eval security ≤ H := by
    simp only [H, referenceHeightPolynomial, Polynomial.eval_add, Polynomial.eval_one]; omega
  have ba : (BinaryAnchorTable.currentHeightPolynomial precision).eval security ≤ H := by
    simp only [H, referenceHeightPolynomial, Polynomial.eval_add, Polynomial.eval_one]; omega
  have br : (BinaryActivationProgram.currentHeightPolynomial precision).eval security ≤ H := by
    simp only [H, referenceHeightPolynomial, Polynomial.eval_add, Polynomial.eval_one]; omega
  have primaryHeight (index : Fin colors) : HeightBound (primary.data.get index).decode H := (hp.1 index).mono bp
  have anchorHeight (input output : Fin colors) : HeightBound ((anchor.data.get input).get output).decode H := (ha.1 input output).mono ba
  have rateHeight : HeightBound activation.data.decode H := hr.mono br
  have pointBounds (output : Fin colors) := BinaryCenterKernel.point_bounds margin.count metadata activation.data primary.data anchor.data output H
    (hd.1.mono bsize) (hd.2.1.mono bsize) (hd.2.2.mono bsize) rateHeight primaryHeight anchorHeight
  have hmono := centerBounds_mono hq (Nat.le_of_eq hm) (le_refl H)
  have centerHeight (output : Fin colors) : HeightBound
      (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data output).data.decode
      ((centerHeightPolynomial precision).eval security) := by
    apply (pointBounds output).1.mono
    simpa only [centerHeightPolynomial, BinaryCenterKernel.heightPolynomial_eval] using hmono.1
  have centerWork (output : Fin colors) :
      (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data output).work ≤
      (BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)).eval security := by
    exact ((pointBounds output).2.trans hmono.2).trans_eq
      (BinaryCenterKernel.workPolynomial_eval _ _ _ security).symm
  have bfirst : H ≤ (heightPolynomial precision).eval security := by
    simp only [heightPolynomial, Polynomial.eval_add]; exact Nat.le_add_right _ _
  have bcenter : (centerHeightPolynomial precision).eval security ≤ (heightPolynomial precision).eval security := by
    simp only [heightPolynomial, Polynomial.eval_add]; exact Nat.le_add_left _ _
  refine ⟨fun index => (primaryHeight index).mono bfirst, ?_, fun input output => (anchorHeight input output).mono bfirst,
    rateHeight.mono bfirst, ?_⟩
  · intro index
    simpa only [current, buildArray_get] using (centerHeight index).mono bcenter
  · have wp := hp.2
    have wa := ha.2
    have wd := BinaryProposalMetadata.current_work security
    rw [← BinaryProposalMetadata.currentWorkPolynomial_eval security] at wd
    have wr := BinaryActivationProgram.current_polynomial_work precision security
    have ww := BinaryActivationProgram.cutoff_work security
    rw [← BinaryActivationProgram.cutoffWorkPolynomial_eval security] at ww
    have hwindow : window.count ≤ (security+2)^2 := by rw [BinaryActivationProgram.cutoff_value]; omega
    have hsquare : square.count = (security+2)^2 := by
      have hpos : 1 ≤ (security+2)^2 := Nat.succ_le_of_lt (pow_pos (Nat.zero_lt_succ (security+1)) 2)
      exact (addCounter_value window.count 1).trans
        ((congrArg (fun count => count+1) (BinaryActivationProgram.cutoff_value security)).trans (Nat.sub_add_cancel hpos))
    have ws : square.work ≤ 2*(security+2)^2+1 :=
      (addCounter_work window.count 1).le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hwindow) 1)
    have wm : margin.work ≤ 3*(2*(security+2)^2+3)+1 := by
      exact (multiplyCounter_work 3 square.count).le.trans_eq (by rw [hsquare])
    have wc := buildArray_work colors
      ((BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)).eval security)
      (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data) centerWork
    have wcb := Nat.add_le_add_right (Nat.mul_le_mul_right
      ((BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)).eval security+2) hq) 2
    change primary.work+anchor.work+metadata.work+activation.work+window.work+square.work+margin.work+
      (buildArray colors (BinaryCenterKernel.point margin.count metadata activation.data primary.data anchor.data)).work+8 ≤ _
    dsimp only [primary, anchor, metadata, activation, window, square, margin] at *
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    change _ ≤ (BinaryPrimaryTable.currentWorkPolynomial precision).eval security+(BinaryAnchorTable.currentWorkPolynomial precision).eval security+
      BinaryProposalMetadata.currentWorkPolynomial.eval security+(BinaryActivationProgram.currentWorkPolynomial precision).eval security+
      BinaryActivationProgram.cutoffWorkPolynomial.eval security+(2*(security+2)^2+1)+(3*(2*(security+2)^2+3)+1)+
      Q*((BinaryCenterKernel.workPolynomial BinaryProposalMetadata.sizePolynomial marginPolynomial (referenceHeightPolynomial precision)).eval security+2)+10
    omega

end
end CurrentAFT.BinaryReferenceTables

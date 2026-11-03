import AFT.BinaryChartProjectionCost
import CurrentAFT.BinaryCurrentPaired
import CurrentAFT.BinaryFirstInverseProgram
import CurrentAFT.RationalRootMassProgram

/-! # The genuine weighted paired-score numerator, without division by a center atom -/
namespace CurrentAFT.BinaryRootWeightedScore
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current

def cached {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count) : RationalResult :=
  let profile := sumFin count (BinaryPairedScore.term primary score anchor center)
  let first := readVector zero score input
  let body := readVector zero centerLaw center
  let leading := RationalBits.multiply body.value first.value
  let correction := RationalBits.multiply rate profile.data
  let result := difference leading.data correction.data
  ⟨result.data,profile.work+first.work+body.work+leading.work+correction.work+result.work+5⟩

theorem cached_value {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count) :
    (cached primary centerLaw score anchor rate input center).data.decode=
      (centerLaw.get center).decode*(score.get input).decode-rate.decode*
        ∑ color, (primary.get color).decode*(score.get color).decode*((anchor.get color).get center).decode := by
  simp only [cached,difference_value,RationalBits.multiply_value,readVector_value,sumFin_value,BinaryPairedScore.term_value]

def current (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input center : Fin (PublicParameterProgram.modulus security).count) : RationalResult :=
  let refs := BinaryReferenceTables.current security bits
  let result := cached refs.primary refs.center score refs.anchor refs.activation input center
  ⟨result.data,refs.work+result.work+2⟩

theorem current_value (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input center : Fin (PublicParameterProgram.modulus security).count) :
    (current security bits score input center).data.decode=
      RationalRootMassProgram.weightedScore security bits (BinaryCurrentPaired.scoreAt score) input.val center.val := by
  simp only [current,cached_value,BinaryReferenceTables.center_value,BinaryReferenceTables.activation_value,
    RationalRootMassProgram.weightedScore,RationalRootMassProgram.anchorScore,BinaryCurrentPaired.scoreAt_index]
  congr 2
  apply Finset.sum_congr rfl
  intro color _
  rw [BinaryReferenceTables.primary_value,BinaryReferenceTables.anchor_value]
  ring

theorem current_of_entries (security bits : ℕ) (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (profile : ℕ → ℚ) (input center : Fin (PublicParameterProgram.modulus security).count)
    (hprofile : ∀ color, (score.get color).decode=profile color.val) :
    (current security bits score input center).data.decode=
      RationalRootMassProgram.weightedScore security bits profile input.val center.val := by
  rw [current_value]
  simp only [RationalRootMassProgram.weightedScore,RationalRootMassProgram.anchorScore,
    BinaryCurrentPaired.scoreAt_index,hprofile]

theorem cached_bounds {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count)
    (bits : ℕ) (hp : ∀ color, HeightBound (primary.get color).decode bits)
    (hb : ∀ color, HeightBound (centerLaw.get color).decode bits)
    (hs : ∀ color, HeightBound (score.get color).decode bits)
    (ha : ∀ color center, HeightBound ((anchor.get color).get center).decode bits)
    (hr : HeightBound rate.decode bits) :
    HeightBound (cached primary centerLaw score anchor rate input center).data.decode (BinaryPairedScore.height count bits) ∧
      (cached primary centerLaw score anchor rate input center).work ≤ BinaryPairedScore.work count bits := by
  let profile := sumFin count (BinaryPairedScore.term primary score anchor center)
  let first := readVector zero score input
  let body := readVector zero centerLaw center
  let leading := RationalBits.multiply body.value first.value
  let correction := RationalBits.multiply rate profile.data
  let H := BinaryPairedScore.height count bits
  have hbits : bits ≤ H := by unfold H BinaryPairedScore.height; nlinarith
  have hprofile := sumFin_height count (3*bits) (BinaryPairedScore.term primary score anchor center)
    (fun color => BinaryPairedScore.term_height primary score anchor center color bits hp hs ha)
  have hfirst : HeightBound first.value.decode bits := by rw [readVector_value]; exact hs input
  have hbody : HeightBound body.value.decode bits := by rw [readVector_value]; exact hb center
  have hlead : HeightBound leading.data.decode (2*bits) := by
    rw [RationalBits.multiply_value]; convert hbody.mul hfirst using 1; omega
  have hcorrection : HeightBound correction.data.decode (bits+count*(3*bits+1)) := by
    rw [RationalBits.multiply_value]; exact hr.mul hprofile
  have wp := sumFin_work count (3*bits)
    (13*count+16+2*primitiveWorkBound H) (BinaryPairedScore.term primary score anchor center)
    (fun color => BinaryPairedScore.term_height primary score anchor center color bits hp hs ha)
    (fun color => BinaryPairedScore.term_work primary score anchor center color bits hp hs ha)
  have hmono := primitiveWorkBound_mono (show (count+1)*(3*bits+1) ≤ H by unfold H BinaryPairedScore.height; nlinarith)
  have wp' : profile.work ≤ count*(13*count+18+3*primitiveWorkBound H)+2 := by
    apply wp.trans
    have hm := Nat.mul_le_mul_left count hmono
    nlinarith only [hm]
  have wf := readVector_work zero score input
  have wb := readVector_work zero centerLaw center
  have wl := RationalBits.multiply_work body.value first.value H (hbody.mono hbits) (hfirst.mono hbits)
  have wc := RationalBits.multiply_work rate profile.data H (hr.mono hbits)
    (hprofile.mono (by unfold H BinaryPairedScore.height; nlinarith))
  have wd := difference_work leading.data correction.data H
    (hlead.mono (by unfold H BinaryPairedScore.height; nlinarith))
    (hcorrection.mono (by unfold H BinaryPairedScore.height; nlinarith))
  constructor
  · change HeightBound (difference leading.data correction.data).data.decode _
    rw [difference_value,sub_eq_add_neg]
    exact (hlead.add hcorrection.neg).mono (by unfold BinaryPairedScore.height; nlinarith)
  · change profile.work+first.work+body.work+leading.work+correction.work+(difference leading.data correction.data).work+5 ≤ _
    change first.work ≤ _ at wf
    change body.work ≤ _ at wb
    change leading.work ≤ _ at wl
    change correction.work ≤ _ at wc
    have hpositive : 1 ≤ primitiveWorkBound H := by
      have hp : 0 < (H+2)^3 := pow_pos (by omega) _
      unfold primitiveWorkBound
      omega
    dsimp only [H] at wp' wd wl wc hpositive
    unfold BinaryPairedScore.work
    omega

noncomputable section
noncomputable def operandPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+scoreBits
noncomputable def heightPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCurrentPaired.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial (operandPolynomial precision scoreBits)
noncomputable def workPolynomial (precision scoreBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryCurrentPaired.evaluationWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial (operandPolynomial precision scoreBits)+2

theorem current_bounds (security : ℕ) (precision scoreBits : Polynomial ℕ)
    (score : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (input center : Fin (PublicParameterProgram.modulus security).count)
    (hscore : ∀ color, HeightBound (score.get color).decode (scoreBits.eval security)) :
    HeightBound (current security (precision.eval security) score input center).data.decode
      ((heightPolynomial precision scoreBits).eval security) ∧
    (current security (precision.eval security) score input center).work ≤ (workPolynomial precision scoreBits).eval security := by
  let refs := BinaryReferenceTables.current security (precision.eval security)
  let H := (operandPolynomial precision scoreBits).eval security
  have hH : H=(BinaryReferenceTables.heightPolynomial precision).eval security+scoreBits.eval security := by
    simp only [H,operandPolynomial,Polynomial.eval_add]
  have hr := BinaryReferenceTables.current_bounds security precision
  have h := cached_bounds refs.primary refs.center score refs.anchor refs.activation input center H
    (fun color => (hr.1 color).mono (by rw [hH]; omega))
    (fun color => (hr.2.1 color).mono (by rw [hH]; omega))
    (fun color => (hscore color).mono (by rw [hH]; omega))
    (fun input output => (hr.2.2.1 input output).mono (by rw [hH]; omega))
    (hr.2.2.2.1.mono (by rw [hH]; omega))
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hh : BinaryPairedScore.height (PublicParameterProgram.modulus security).count H ≤ (heightPolynomial precision scoreBits).eval security := by
    simp only [heightPolynomial,BinaryCurrentPaired.heightPolynomial,BinaryPairedScore.height,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    unfold H
    gcongr
  have hw : BinaryPairedScore.work (PublicParameterProgram.modulus security).count H ≤
      (BinaryCurrentPaired.evaluationWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial (operandPolynomial precision scoreBits)).eval security := by
    simp only [BinaryCurrentPaired.evaluationWorkPolynomial,BinaryCurrentPaired.heightPolynomial,BinaryPairedScore.work,
      BinaryPairedScore.height,primitiveWorkPolynomial_eval,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    unfold primitiveWorkBound H
    gcongr
  refine ⟨h.1.mono hh,?_⟩
  have wr : refs.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  change refs.work+(cached refs.primary refs.center score refs.anchor refs.activation input center).work+2 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

end
end CurrentAFT.BinaryRootWeightedScore

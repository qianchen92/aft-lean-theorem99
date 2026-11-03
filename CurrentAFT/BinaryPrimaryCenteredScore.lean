import AFT.BinaryChartProjectionCost
import CurrentAFT.BinaryReferenceTables
import CurrentAFT.BinaryMassLiftColumn
import CurrentAFT.RationalPrimaryColumnProgram

/-! # Actual centered primary point scores, materialized from the common reference -/
namespace CurrentAFT.BinaryPrimaryCenteredScore
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point {count : ℕ} (atom : RationalBits) (source output : Fin count) : RationalResult :=
  let delta := BinaryMassLiftColumn.point source output
  let result := difference delta.data atom
  ⟨result.data,delta.work+result.work+2⟩

theorem point_value {count : ℕ} (atom : RationalBits) (source output : Fin count) :
    (point atom source output).data.decode=(if output=source then (1:ℚ) else 0)-atom.decode := by
  simp only [point,difference_value,BinaryMassLiftColumn.point_value]

def current (security bits : ℕ) (source : Fin (colors security)) : ArrayResult (colors security) :=
  let modulus := PublicParameterProgram.modulus security
  let references := BinaryReferenceTables.current security bits
  let atom := readVector zero references.primary source
  let result := buildArray modulus.count (point atom.value source)
  ⟨result.data,modulus.work+references.work+atom.work+result.work+4⟩

theorem current_value (security bits : ℕ) (source output : Fin (colors security)) :
    ((current security bits source).data.get output).decode=RationalPrimaryColumnProgram.centerDelta security bits source.val output.val := by
  simp only [current,buildArray_get,point_value,readVector_value,BinaryReferenceTables.primary_value,
    RationalPrimaryColumnProgram.centerDelta,Fin.ext_iff]

def pointWork (count bits : ℕ) := 12*count+7+2*primitiveWorkBound (bits+1)+4

theorem point_bounds {count : ℕ} (atom : RationalBits) (source output : Fin count) (bits : ℕ)
    (ha : HeightBound atom.decode bits) :
    HeightBound (point atom source output).data.decode (bits+2) ∧
      (point atom source output).work ≤ pointWork count bits := by
  have hd := BinaryMassLiftColumn.point_height source output
  have wd := BinaryMassLiftColumn.point_work source output
  have wr := difference_work (BinaryMassLiftColumn.point source output).data atom (bits+1)
    (hd.mono (by omega)) (ha.mono (by omega))
  constructor
  · rw [point_value,sub_eq_add_neg]
    split_ifs
    · exact (HeightBound.one.add ha.neg).mono (by omega)
    · exact (HeightBound.zero.add ha.neg).mono (by omega)
  · change (BinaryMassLiftColumn.point source output).work+(difference (BinaryMassLiftColumn.point source output).data atom).work+2 ≤ _
    unfold pointWork
    omega

noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+2
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    3*BinaryFirstInverseProgram.colorsPolynomial+3+
    BinaryFirstInverseProgram.colorsPolynomial*(12*BinaryFirstInverseProgram.colorsPolynomial+7+
      2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+6)+2+4

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) (source : Fin (colors security)) :
    (∀ output, HeightBound ((current security (precision.eval security) source).data.get output).decode
      ((heightPolynomial precision).eval security)) ∧
    (current security (precision.eval security) source).work ≤ (workPolynomial precision).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let refs := BinaryReferenceTables.current security (precision.eval security)
  let atom := readVector zero refs.primary source
  have hr := BinaryReferenceTables.current_bounds security precision
  have ha : HeightBound atom.value.decode ((BinaryReferenceTables.heightPolynomial precision).eval security) := by
    rw [readVector_value]; exact hr.1 source
  have hp (output : Fin (colors security)) := point_bounds atom.value source output _ ha
  have hb := buildArray_work (colors security) (pointWork (colors security) ((BinaryReferenceTables.heightPolynomial precision).eval security))
    (point atom.value source) (fun output => (hp output).2)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have wa := readVector_work zero refs.primary source
  have wq := PublicParameterProgram.modulus_work security
  have wr : refs.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  have wb := hb.trans (show colors security*(pointWork (colors security) ((BinaryReferenceTables.heightPolynomial precision).eval security)+2)+2 ≤
      BinaryFirstInverseProgram.colorsPolynomial.eval security*(12*BinaryFirstInverseProgram.colorsPolynomial.eval security+7+
        2*primitiveWorkBound ((BinaryReferenceTables.heightPolynomial precision).eval security+1)+6)+2 by unfold pointWork; gcongr)
  constructor
  · intro output
    change HeightBound ((buildArray _ (point atom.value source)).data.get output).decode _
    rw [buildArray_get]
    simpa only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat] using (hp output).1
  · change modulus.work+refs.work+atom.work+(buildArray _ (point atom.value source)).work+4 ≤ _
    change modulus.work ≤ _ at wq
    change atom.work ≤ _ at wa
    change (PublicParameterProgram.modulus security).count ≤ _ at hq
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval,
      PublicParameterProgram.workPolynomial_eval,Polynomial.eval_one]
    dsimp only [refs,modulus,atom] at wr wa wb wq ⊢
    omega

end
end CurrentAFT.BinaryPrimaryCenteredScore

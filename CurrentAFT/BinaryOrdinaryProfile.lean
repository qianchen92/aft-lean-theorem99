import CurrentAFT.BinaryShiftedProfile
import CurrentAFT.BinaryMassLiftColumn
import CurrentAFT.RationalOrdinaryProfileProgram

/-! # Actual ordinary centered columns retain their shifted joint mass -/
namespace CurrentAFT.BinaryOrdinaryProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryShiftedProfile.current BinaryMassLiftInput.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def preRoot (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let reference := BinaryReferenceTables.current security bits
  let sourceValue := readVector zero reference.center source
  let outputValue := readVector zero reference.center output
  let point := BinaryMassLiftColumn.point source output
  let centered := difference point.data outputValue.value
  let result := RationalBits.multiply sourceValue.value centered.data
  ⟨result.data,reference.work+sourceValue.work+outputValue.work+point.work+centered.work+result.work+6⟩

theorem preRoot_value (security bits : ℕ) (source output : Fin (colors security)) :
    (preRoot security bits source output).data.decode =
      RationalOrdinaryProfileProgram.preRoot security bits source.val output.val := by
  simp only [preRoot,RationalBits.multiply_value,difference_value,readVector_value,
    BinaryReferenceTables.center_value,BinaryMassLiftColumn.point_value,Fin.ext_iff,
    RationalOrdinaryProfileProgram.preRoot]

def shifted (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits) (output : ℕ) : RationalResult :=
  BinaryShiftedProfile.current security (preRoot security bits source) root output

theorem shifted_value (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits) (output : ℕ) :
    (shifted security bits source root output).data.decode =
      RationalOrdinaryProfileProgram.shifted security bits source.val root.decode output :=
  BinaryShiftedProfile.current_value security _ _ (preRoot_value security bits source) root output

def density (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (fun color => shifted security bits source root color.val) output

theorem density_value (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits)
    (output : Fin (colors security)) :
    (density security bits source root output).data.decode =
      RationalOrdinaryProfileProgram.density security bits source.val root.decode output.val := by
  apply BinaryMassLiftInput.current_value
  intro color
  exact shifted_value security bits source root color.val

noncomputable section
def preRootHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryReferenceTables.heightPolynomial precision+2
def preRootWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+18*BinaryFirstInverseProgram.colorsPolynomial+21+
    2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+
    primitiveWorkPolynomial (preRootHeightPolynomial precision)

theorem preRoot_bounds (security : ℕ) (precision : Polynomial ℕ) (source output : Fin (colors security)) :
    HeightBound (preRoot security (precision.eval security) source output).data.decode
      ((preRootHeightPolynomial precision).eval security) ∧
      (preRoot security (precision.eval security) source output).work ≤ (preRootWorkPolynomial precision).eval security := by
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let sourceValue := readVector zero reference.center source
  let outputValue := readVector zero reference.center output
  let point := BinaryMassLiftColumn.point source output
  let centered := difference point.data outputValue.value
  let result := RationalBits.multiply sourceValue.value centered.data
  let H := (BinaryReferenceTables.heightPolynomial precision).eval security
  have hh := BinaryReferenceTables.current_bounds security precision
  have hs : HeightBound sourceValue.value.decode H := by rw [readVector_value]; exact hh.2.1 source
  have ho : HeightBound outputValue.value.decode H := by rw [readVector_value]; exact hh.2.1 output
  have hp : HeightBound point.data.decode 1 := BinaryMassLiftColumn.point_height source output
  have hc : HeightBound centered.data.decode (H+2) := by
    rw [difference_value,sub_eq_add_neg]
    exact (hp.add ho.neg).mono (by omega)
  have wr : reference.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hh.2.2.2.2
  have ws : sourceValue.work ≤ 3*colors security+3 := readVector_work zero reference.center source
  have wo : outputValue.work ≤ 3*colors security+3 := readVector_work zero reference.center output
  have wp : point.work ≤ 12*colors security+7 := BinaryMassLiftColumn.point_work source output
  have wc : centered.work ≤ 2*primitiveWorkBound (H+1)+2 := difference_work point.data outputValue.value (H+1)
    (hp.mono (by omega)) (ho.mono (by omega))
  have wm : result.work ≤ primitiveWorkBound (2*H+2) := RationalBits.multiply_work sourceValue.value centered.data (2*H+2)
    (hs.mono (by omega)) (hc.mono (by omega))
  have hq := BinaryFirstInverseProgram.colors_bound security
  change colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security at hq
  constructor
  · change HeightBound result.data.decode _
    rw [RationalBits.multiply_value]
    apply (hs.mul hc).mono
    simp only [preRootHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    dsimp only [H]
    omega
  · change reference.work+sourceValue.work+outputValue.work+point.work+centered.work+result.work+6 ≤ _
    simp only [preRootWorkPolynomial,preRootHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_one,primitiveWorkPolynomial_eval]
    dsimp only [H] at wc wm
    omega

def shiftedHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedProfile.heightPolynomial (preRootHeightPolynomial precision)
def shiftedWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedProfile.workPolynomial rootBits (preRootHeightPolynomial precision) (preRootWorkPolynomial precision)

theorem shifted_bounds (security : ℕ) (precision rootBits : Polynomial ℕ) (source : Fin (colors security))
    (root : IntegerBits) (output : ℕ) (hr : root.digits.length ≤ rootBits.eval security) (ho : output<colors security) :
    HeightBound (shifted security (precision.eval security) source root output).data.decode
      ((shiftedHeightPolynomial precision).eval security) ∧
      (shifted security (precision.eval security) source root output).work ≤
        (shiftedWorkPolynomial precision rootBits).eval security :=
  BinaryShiftedProfile.current_bounds security rootBits (preRootHeightPolynomial precision) (preRootWorkPolynomial precision)
    (preRoot security (precision.eval security) source) root output hr ho
    (fun color => (preRoot_bounds security precision source color).1)
    (fun color => (preRoot_bounds security precision source color).2)

def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (shiftedHeightPolynomial precision)
def workPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (shiftedHeightPolynomial precision) (shiftedWorkPolynomial precision rootBits)

theorem density_bounds (security : ℕ) (precision rootBits : Polynomial ℕ) (source : Fin (colors security))
    (root : IntegerBits) (output : Fin (colors security)) (hr : root.digits.length ≤ rootBits.eval security) :
    HeightBound (density security (precision.eval security) source root output).data.decode ((heightPolynomial precision).eval security) ∧
      (density security (precision.eval security) source root output).work ≤ (workPolynomial precision rootBits).eval security :=
  BinaryMassLiftInput.current_bounds security precision (shiftedHeightPolynomial precision) (shiftedWorkPolynomial precision rootBits)
    (fun color => shifted security (precision.eval security) source root color.val) output
    (fun color => (shifted_bounds security precision rootBits source root color.val hr color.isLt).1)
    (fun color => (shifted_bounds security precision rootBits source root color.val hr color.isLt).2)

end
end CurrentAFT.BinaryOrdinaryProfile

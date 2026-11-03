import CurrentAFT.BinaryMassLiftInput
import CurrentAFT.BinaryFirstFamily
import CurrentAFT.RationalPrimaryDeviationProgram

/-! # The actual primary-minus-uniform mass certificate on binary data -/
namespace CurrentAFT.BinaryPrimaryDeviation
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current BinaryMassLiftInput.current BinaryFirstFamily.current

def point {count : ℕ} (primary : Vector RationalBits count) (colors : RationalBits) (output : Fin count) : RationalResult :=
  let atom := readVector zero primary output
  let uniform := RationalBits.inverse colors
  let negative := RationalBits.negate uniform.data
  let result := RationalBits.add atom.value negative.data
  ⟨result.data,atom.work+uniform.work+negative.work+result.work+4⟩

theorem point_value {count : ℕ} (primary : Vector RationalBits count) (colors : RationalBits) (output : Fin count) :
    (point primary colors output).data.decode=(primary.get output).decode-1/colors.decode := by
  simp only [point,RationalBits.add_value,RationalBits.negate_value,inverse_value,readVector_value,one_div,sub_eq_add_neg]

def density (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security bits
  let result := BinaryMassLiftInput.current security bits (point reference.primary count.data) output
  ⟨result.data,modulus.work+count.work+reference.work+result.work+4⟩

theorem density_value (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (density security bits output).data.decode=RationalMassLiftProgram.current security bits
      (RationalPrimaryDeviationProgram.profile security bits) output.val := by
  change (BinaryMassLiftInput.current _ _ _ _).data.decode=_
  apply BinaryMassLiftInput.current_value
  intro color
  simp only [point_value,BinaryReferenceTables.primary_value,ofCounter_value,RationalPrimaryDeviationProgram.profile]

def current (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val (density security bits) (fun _ => ⟨zero,2⟩) inputs centers

theorem current_value (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (current security bits order arity inputs centers).data.decode=RationalPrimaryDeviationProgram.current security bits order arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) :=
  BinaryFirstFamily.current_value security order arity _ _ _ _ inputs centers (density_value security bits) (fun _ => zero_value)

def pointWork (count bits : ℕ) := 3*count+3*primitiveWorkBound bits+7

theorem point_bounds {count : ℕ} (primary : Vector RationalBits count) (colors : RationalBits) (output : Fin count) (bits : ℕ)
    (hp : ∀ color, HeightBound (primary.get color).decode bits) (hq : HeightBound colors.decode bits) :
    HeightBound (point primary colors output).data.decode (2*bits+1) ∧
      (point primary colors output).work≤pointWork count bits := by
  let atom := readVector zero primary output
  let uniform := RationalBits.inverse colors
  let negative := RationalBits.negate uniform.data
  have ha : HeightBound atom.value.decode bits := by rw [readVector_value]; exact hp output
  have hu : HeightBound uniform.data.decode bits := by rw [inverse_value]; exact hq.inv
  have hn : HeightBound negative.data.decode bits := by rw [RationalBits.negate_value]; exact hu.neg
  have wa := readVector_work zero primary output
  have wu : uniform.work≤primitiveWorkBound bits := inverse_work colors bits
  have wn : negative.work≤primitiveWorkBound bits := RationalBits.negate_work uniform.data bits
  have wr := RationalBits.add_work atom.value negative.data bits ha hn
  constructor
  · change HeightBound (RationalBits.add atom.value negative.data).data.decode _
    rw [RationalBits.add_value]
    exact (ha.add hn).mono (by omega)
  · change atom.work+uniform.work+negative.work+(RationalBits.add atom.value negative.data).work+4≤_
    change atom.work≤_ at wa
    unfold pointWork
    omega

noncomputable section
noncomputable def operandHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := 2*operandHeightPolynomial precision+1
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  3*BinaryFirstInverseProgram.colorsPolynomial+3*primitiveWorkPolynomial (operandHeightPolynomial precision)+7
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def densityWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)+4
noncomputable def workPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ := densityWorkPolynomial precision+Polynomial.C (15*order+52)

theorem density_bounds (security : ℕ) (precision : Polynomial ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (density security (precision.eval security) output).data.decode ((heightPolynomial precision).eval security) ∧
      (density security (precision.eval security) output).work≤(densityWorkPolynomial precision).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let H := (operandHeightPolynomial precision).eval security
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hr := BinaryReferenceTables.current_bounds security precision
  have hH : H=(BinaryReferenceTables.heightPolynomial precision).eval security+BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    simp only [H,operandHeightPolynomial,Polynomial.eval_add]
  have hp (color : Fin (BinaryFirstInverseProgram.colors security)) : HeightBound (reference.primary.get color).decode H :=
    (hr.1 color).mono (by rw [hH]; omega)
  have hcount : HeightBound count.data.decode H := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse modulus.count).mono (hq.trans (by rw [hH]; omega))
  have ht (color : Fin (BinaryFirstInverseProgram.colors security)) := point_bounds reference.primary count.data color H hp hcount
  have hh (color : Fin (BinaryFirstInverseProgram.colors security)) : HeightBound (point reference.primary count.data color).data.decode
      ((pointHeightPolynomial precision).eval security) := by
    simpa only [pointHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one] using (ht color).1
  have hw (color : Fin (BinaryFirstInverseProgram.colors security)) :
      (point reference.primary count.data color).work≤(pointWorkPolynomial precision).eval security := by
    apply (ht color).2.trans
    simp only [pointWorkPolynomial,pointWork,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hq) _) _
  have hi := BinaryMassLiftInput.current_bounds security precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)
    (point reference.primary count.data) output hh hw
  have wq := PublicParameterProgram.modulus_work security
  change modulus.work≤_ at wq
  have wc : count.work≤60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (ofCounter_work modulus.count).trans (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wr : reference.work≤(BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  constructor
  · exact hi.1
  · change modulus.work+count.work+reference.work+(BinaryMassLiftInput.current security (precision.eval security)
      (point reference.primary count.data) output).work+4≤_
    simp only [densityWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval]
    omega

theorem current_bounds (security order : ℕ) (precision : Polynomial ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (current security (precision.eval security) order arity inputs centers).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) order arity inputs centers).work≤(workPolynomial order precision).eval security := by
  have h := BinaryFirstFamily.current_bounds security arity.val.1.val arity.val.2.val (density security (precision.eval security))
    (fun _ => ⟨zero,2⟩) inputs centers ((heightPolynomial precision).eval security) 0 ((densityWorkPolynomial precision).eval security) 2
    (fun color => (density_bounds security precision color).1) (fun _ => by rw [zero_value]; exact HeightBound.zero)
    (fun color => (density_bounds security precision color).2) (fun _ => le_refl _)
  constructor
  · simpa only [add_zero] using h.1
  · apply h.2.trans
    have hd := arity.property
    simp only [BinaryFirstFamily.work,workPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

end
end CurrentAFT.BinaryPrimaryDeviation

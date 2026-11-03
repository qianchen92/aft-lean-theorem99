import CurrentAFT.BinaryUnselectedLegResources

/-! # The full unselected leg channel on the stored three-slot source buffer -/
namespace CurrentAFT.BinaryLegGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security
abbrev Descriptor := BinaryUnselectedLeg.Descriptor

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order := fun arity colors centers =>
  let root := readVector (BinaryFirstFamily.first security) source 0
  let code := canonicalCounter root.value.val
  let result := BinaryUnselectedLeg.current security bits order programs fallback entries ⟨false,code.digits⟩ arity colors centers
  ⟨result.value,root.work+code.work+result.work+3⟩

noncomputable section
open scoped Classical

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Descriptor) (entries : Vector Descriptor 8) (ordering : Fin 8 ≃ Finset (Fin 3))
    (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryLegSelectedCoefficient.Valid (entries.get index))
    (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs fallback entries source arity colors centers).value.decode=
      RationalUnselectedLegProgram.current security bits order (source.get 0).val arity colors.get centers.get := by
  simp only [current,readVector_value,BinaryUnselectedLeg.current_value security bits order programs hcorrect hcomplete
      fallback entries ordering hselected hvalid _ _ _ _ hc hd,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnselectedLeg.heightPolynomial order programs entries precision BinaryFirstInverseProgram.colorsPolynomial
def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnselectedLeg.workPolynomial order programs entries precision BinaryFirstInverseProgram.colorsPolynomial+15

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ) (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs fallback entries source arity colors centers).value.decode
      ((heightPolynomial order programs entries precision).eval security) ∧
      (current security (precision.eval security) order programs fallback entries source arity colors centers).work ≤
        (workPolynomial order programs entries precision).eval security := by
  let root := readVector (BinaryFirstFamily.first security) source 0
  let code := canonicalCounter root.value.val
  have hr := root.value.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=root.value.val))).trans hr
  have h := BinaryUnselectedLeg.current_bounds security order programs fallback entries precision BinaryFirstInverseProgram.colorsPolynomial
    ⟨false,code.digits⟩ hl arity colors centers hc hd
  have wr : root.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 0
  have wc : code.work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work root.value.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  constructor
  · exact h.1
  · change root.work+code.work+
      (BinaryUnselectedLeg.current security (precision.eval security) order programs fallback entries ⟨false,code.digits⟩ arity colors centers).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega

end
end CurrentAFT.BinaryLegGroup

import CurrentAFT.BinaryPrimaryMass
import CurrentAFT.BinaryPositivePrimary

/-! The actual normalized primary channel, including its centered point score. -/
namespace CurrentAFT.BinaryNormalizedPrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security
abbrev Descriptor := BinaryPrimarySelectedCoefficient.Entry

def numerator (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment : IntegerBits) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryPrimaryFamily.sum security bits order 1 fallback entries (BinaryPrimaryMass.current security bits compensator attachment source)

def atRoots (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment : IntegerBits) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (numerator security bits order fallback entries compensator attachment source)
    (BinaryPositivePrimary.inverse security bits order programs fallback entries)

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment source : Fin (colors security)) : CoefficientProgram order := fun arity inputs centers =>
  let left := canonicalCounter compensator.val
  let right := canonicalCounter attachment.val
  let value := atRoots security bits order programs fallback entries ⟨false,left.digits⟩ ⟨false,right.digits⟩ source arity inputs centers
  ⟨value.value,left.work+right.work+value.work+4⟩

noncomputable section
open scoped BigOperators Classical

theorem numerator_value (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (ordering : Fin 16 ≃ Finset (Fin 4)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryPrimarySelectedCoefficient.Valid (entries.get index))
    (compensator attachment : IntegerBits) (source : Fin (colors security))
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    (numerator security bits order fallback entries compensator attachment source arity inputs centers).value.decode=
      RationalLocalFamilyProgram.numerator security bits order compensator.decode attachment.decode source.val arity inputs.get centers.get := by
  rw [numerator,BinaryPrimaryFamily.sum_value security bits order 1 (by norm_num) fallback entries ordering hselected hvalid
    (BinaryPrimaryMass.current security bits compensator attachment source)
    (RationalRootMassProgram.primaryMass security bits compensator.decode attachment.decode (RationalPrimaryColumnProgram.centerDelta security bits source.val))
    (BinaryPrimaryMass.current_value security bits compensator attachment source) arity inputs centers hc hd]
  have heq : (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 1≤selected.card)=
      (Finset.univ : Finset (Finset (Fin 4))).erase ∅ := by
    ext selected
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,and_true]
    exact Finset.card_pos.trans Finset.nonempty_iff_ne_empty
  rw [heq]
  rfl

theorem atRoots_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Descriptor) (entries : Vector Descriptor 16) (ordering : Fin 16 ≃ Finset (Fin 4))
    (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryPrimarySelectedCoefficient.Valid (entries.get index))
    (compensator attachment : IntegerBits) (source : Fin (colors security))
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    (atRoots security bits order programs fallback entries compensator attachment source arity inputs centers).value.decode=
      RationalPositiveFamilyProgram.primaryChannel security bits order compensator.decode attachment.decode source.val arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (colors security) programs hcorrect hcomplete _ _ _ _
    (numerator_value security bits order fallback entries ordering hselected hvalid compensator attachment source)
    (BinaryPositivePrimary.inverse_value security bits order programs hcorrect hcomplete fallback entries ordering hselected hvalid)
    arity inputs centers hc hd

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Descriptor) (entries : Vector Descriptor 16) (ordering : Fin 16 ≃ Finset (Fin 4))
    (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, BinaryPrimarySelectedCoefficient.Valid (entries.get index))
    (compensator attachment source : Fin (colors security))
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    (current security bits order programs fallback entries compensator attachment source arity inputs centers).value.decode=
      RationalPositiveFamilyProgram.primaryChannel security bits order compensator.val attachment.val source.val arity inputs.get centers.get := by
  unfold current
  rw [atRoots_value security bits order programs hcorrect hcomplete fallback entries ordering hselected hvalid _ _ source arity inputs centers hc hd]
  simp only [IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

noncomputable def numeratorHeight (entries : Vector Descriptor 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.heightPolynomial entries precision (BinaryPrimaryMass.heightPolynomial precision inputBits)
noncomputable def numeratorWork (order : ℕ) (entries : Vector Descriptor 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.workPolynomial order 1 entries precision (BinaryPrimaryMass.heightPolynomial precision inputBits)
    (BinaryPrimaryMass.workPolynomial precision inputBits)

theorem numerator_bounds (security order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) (compensator attachment : IntegerBits) (source : Fin (colors security))
    (hcomp : compensator.digits.length ≤ inputBits.eval security) (hattach : attachment.digits.length ≤ inputBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    HeightBound (numerator security (precision.eval security) order fallback entries compensator attachment source arity inputs centers).value.decode
      ((numeratorHeight entries precision inputBits).eval security) ∧
      (numerator security (precision.eval security) order fallback entries compensator attachment source arity inputs centers).work ≤
        (numeratorWork order entries precision inputBits).eval security :=
  BinaryPrimaryFamily.sum_bounds security order 1 fallback entries precision
    (BinaryPrimaryMass.heightPolynomial precision inputBits) (BinaryPrimaryMass.workPolynomial precision inputBits)
    (BinaryPrimaryMass.current security (precision.eval security) compensator attachment source)
    (fun word => (BinaryPrimaryMass.current_bounds security precision inputBits compensator attachment source word hcomp hattach).1)
    (fun word => (BinaryPrimaryMass.current_bounds security precision inputBits compensator attachment source word hcomp hattach).2)
    arity inputs centers hc hd

noncomputable def jointHeight (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorHeight entries precision inputBits+BinaryPositivePrimary.heightPolynomial order programs entries precision
noncomputable def jointWork (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorWork order entries precision inputBits+BinaryPositivePrimary.workPolynomial order programs entries precision
noncomputable def atRootsHeight (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (jointHeight order programs entries precision inputBits)
noncomputable def atRootsWork (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (jointHeight order programs entries precision inputBits)
    (jointWork order programs entries precision inputBits)

theorem atRoots_bounds (security order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) (compensator attachment : IntegerBits) (source : Fin (colors security))
    (hcomp : compensator.digits.length ≤ inputBits.eval security) (hattach : attachment.digits.length ≤ inputBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    HeightBound (atRoots security (precision.eval security) order programs fallback entries compensator attachment source arity inputs centers).value.decode
      ((atRootsHeight order programs entries precision inputBits).eval security) ∧
      (atRoots security (precision.eval security) order programs fallback entries compensator attachment source arity inputs centers).work ≤
        (atRootsWork order programs entries precision inputBits).eval security := by
  unfold atRootsHeight atRootsWork
  rw [BinaryFamilyArithmetic.heightPolynomial_eval,BinaryFamilyArithmetic.workPolynomial_eval]
  apply BinaryFamilyArithmetic.multiply_bounds order (colors security)
  · intro arity inputs centers hc hd
    have h := numerator_bounds security order fallback entries precision inputBits compensator attachment source hcomp hattach arity inputs centers hc hd
    exact ⟨h.1.mono (by simp only [jointHeight,Polynomial.eval_add]; omega),h.2.trans (by simp only [jointWork,Polynomial.eval_add]; omega)⟩
  · intro arity inputs centers hc hd
    have h := BinaryPositivePrimary.inverse_bounds security order programs fallback entries precision arity inputs centers hc hd
    exact ⟨h.1.mono (by simp only [jointHeight,Polynomial.eval_add]; omega),h.2.trans (by simp only [jointWork,Polynomial.eval_add]; omega)⟩
  · exact hc
  · exact hd

noncomputable def rootBits : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+1
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision : Polynomial ℕ) : Polynomial ℕ := atRootsHeight order programs entries precision rootBits
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  100*(BinaryFirstInverseProgram.colorsPolynomial+2)^2+atRootsWork order programs entries precision rootBits+4

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (precision : Polynomial ℕ) (compensator attachment source : Fin (colors security))
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, inputs.get i<colors security) (hd : ∀ i, centers.get i<colors security) :
    HeightBound (current security (precision.eval security) order programs fallback entries compensator attachment source arity inputs centers).value.decode
      ((heightPolynomial order programs entries precision).eval security) ∧
      (current security (precision.eval security) order programs fallback entries compensator attachment source arity inputs centers).work ≤
        (workPolynomial order programs entries precision).eval security := by
  have hq := BinaryFirstInverseProgram.colors_bound security
  change colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security at hq
  have hcb := canonicalCounter_length compensator.val
  have hab := canonicalCounter_length attachment.val
  have hcl : (canonicalCounter compensator.val).digits.length ≤ rootBits.eval security := by
    simp only [rootBits,Polynomial.eval_add,Polynomial.eval_one]
    rw [hcb]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=compensator.val))).trans (by have h := compensator.isLt; omega)
  have hal : (canonicalCounter attachment.val).digits.length ≤ rootBits.eval security := by
    simp only [rootBits,Polynomial.eval_add,Polynomial.eval_one]
    rw [hab]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=attachment.val))).trans (by have h := attachment.isLt; omega)
  have h := atRoots_bounds security order programs fallback entries precision rootBits
    ⟨false,(canonicalCounter compensator.val).digits⟩ ⟨false,(canonicalCounter attachment.val).digits⟩ source hcl hal arity inputs centers hc hd
  have wc := canonicalCounter_work compensator.val
  have wa := canonicalCounter_work attachment.val
  constructor
  · exact h.1
  · change _+_+_+4 ≤ _
    have hc' : compensator.val ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := (Nat.le_of_lt compensator.isLt).trans hq
    have ha' : attachment.val ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := (Nat.le_of_lt attachment.isLt).trans hq
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow]
    have wc' := wc.trans (show _ ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+2)^2 by gcongr; omega)
    have wa' := wa.trans (show _ ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+2)^2 by gcongr; omega)
    omega

end
end CurrentAFT.BinaryNormalizedPrimary

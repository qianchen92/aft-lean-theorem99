import CurrentAFT.BinaryUnsafeProfile

/-! # A generated unsafe profile cache and its exact total mass -/
namespace CurrentAFT.BinaryUnsafeArray
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryUnsafeProfile.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point (security : ℕ) (shift : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := BinaryUnsafeProfile.current security shift code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security : ℕ) (shift : IntegerBits) (output : Fin (colors security)) :
    (point security shift output).data.decode=RationalBackgroundProfiles.unsafeProfile security shift.decode output.val := by
  simp only [point, BinaryUnsafeProfile.current_value, canonicalCounter_value]

def read {count : ℕ} (profile : Vector RationalBits count) (index : Fin count) : RationalResult :=
  let result := readVector zero profile index
  ⟨result.value, result.work+1⟩

structure Result (security : ℕ) where
  profile : Vector RationalBits (colors security)
  total : RationalBits
  work : ℕ

def current (security : ℕ) (shift : IntegerBits) : Result security :=
  let modulus := PublicParameterProgram.modulus security
  let profile := buildArray modulus.count (point security shift)
  let total := sumFin modulus.count (read profile.data)
  ⟨profile.data, total.data, modulus.work+profile.work+total.work+4⟩

theorem profile_value (security : ℕ) (shift : IntegerBits) (output : Fin (colors security)) :
    ((current security shift).profile.get output).decode=RationalBackgroundProfiles.unsafeProfile security shift.decode output.val := by
  simp only [current, buildArray_get, point_value]

theorem total_value (security : ℕ) (shift : IntegerBits) :
    (current security shift).total.decode=RationalBackgroundProfiles.unsafeTotal security shift.decode := by
  simp only [current, sumFin_value, read, readVector_value, buildArray_get, point_value,
    RationalBackgroundProfiles.unsafeTotal]

noncomputable section
noncomputable def pointHeightPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeProfile.heightPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnsafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  pointHeightPolynomial shiftBits+BinaryFirstInverseProgram.colorsPolynomial*(pointHeightPolynomial shiftBits+1)
noncomputable def workPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(pointWorkPolynomial shiftBits+2)+2+
    Q*(3*Q+6+primitiveWorkPolynomial ((Q+1)*(pointHeightPolynomial shiftBits+1)))+2+4

theorem point_bounds (security : ℕ) (shift : IntegerBits) (shiftBits : Polynomial ℕ)
    (hs : shift.digits.length ≤ shiftBits.eval security) (output : Fin (colors security)) :
    HeightBound (point security shift output).data.decode ((pointHeightPolynomial shiftBits).eval security) ∧
      (point security shift output).work ≤ (pointWorkPolynomial shiftBits).eval security := by
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter output.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have h := BinaryUnsafeProfile.current_bounds security shift (canonicalCounter output.val).digits shiftBits
    BinaryFirstInverseProgram.colorsPolynomial hs hl
  constructor
  · exact h.1
  · have wc := (canonicalCounter_work output.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
    change _+_+2 ≤ _
    simp only [pointWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

theorem current_bounds (security : ℕ) (shift : IntegerBits) (shiftBits : Polynomial ℕ)
    (hs : shift.digits.length ≤ shiftBits.eval security) :
    (∀ color, HeightBound ((current security shift).profile.get color).decode ((heightPolynomial shiftBits).eval security)) ∧
    HeightBound (current security shift).total.decode ((heightPolynomial shiftBits).eval security) ∧
      (current security shift).work ≤ (workPolynomial shiftBits).eval security := by
  let q := colors security
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  let H := (pointHeightPolynomial shiftBits).eval security
  let profile := buildArray q (point security shift)
  have hq : q≤Q := BinaryFirstInverseProgram.colors_bound security
  have hp (color : Fin q) : HeightBound (profile.data.get color).decode H := by
    rw [buildArray_get]
    exact (point_bounds security shift shiftBits hs color).1
  have hr (color : Fin q) : HeightBound (read profile.data color).data.decode H := by
    rw [read, readVector_value]
    exact hp color
  have wr (color : Fin q) : (read profile.data color).work≤3*q+4 := by
    have h := readVector_work zero profile.data color
    change _+1≤_
    omega
  have htotal := sumFin_height q H (read profile.data) hr
  have wtotal := sumFin_work q H (3*q+4) (read profile.data) hr wr
  have wtotal' := wtotal.trans (show q*(3*q+4+primitiveWorkBound ((q+1)*(H+1))+2)+2≤
      Q*(3*Q+6+primitiveWorkBound ((Q+1)*(H+1)))+2 by
    calc
      _ = q*(3*q+6+primitiveWorkBound ((q+1)*(H+1)))+2 := by ring
      _ ≤ _ := by unfold primitiveWorkBound; gcongr)
  have wp := (buildArray_work q ((pointWorkPolynomial shiftBits).eval security) (point security shift)
    (fun color => (point_bounds security shift shiftBits hs color).2)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 2)
  have wq := PublicParameterProgram.modulus_work security
  have hheight : (heightPolynomial shiftBits).eval security=H+Q*(H+1) := by
    simp only [heightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, H, Q]
  refine ⟨?_, ?_, ?_⟩
  · intro color
    change HeightBound (profile.data.get color).decode _
    exact (hp color).mono (by rw [hheight]; omega)
  · change HeightBound (sumFin q (read profile.data)).data.decode _
    exact htotal.mono ((Nat.mul_le_mul_right (H+1) hq).trans (by rw [hheight]; omega))
  · change (PublicParameterProgram.modulus security).work+profile.work+(sumFin q (read profile.data)).work+4≤_
    change profile.work≤_ at wp
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, PublicParameterProgram.workPolynomial_eval, primitiveWorkPolynomial_eval]
    change _≤PublicParameterProgram.workBound security+Q*((pointWorkPolynomial shiftBits).eval security+2)+2+
      Q*(3*Q+6+primitiveWorkBound ((Q+1)*(H+1)))+2+4
    omega

end
end CurrentAFT.BinaryUnsafeArray

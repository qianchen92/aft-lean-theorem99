import CurrentAFT.BinaryFirstInverseResources

/-! # Actual binary columns of the current first mass lift -/
namespace CurrentAFT.BinaryMassLiftColumn
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter BinaryFirstInverseProgram.current PublicParameterProgram.modulus

def point {count : ℕ} (source output : Fin count) : RationalResult :=
  let forward := lessCounter source.val output.val
  let backward := lessCounter output.val source.val
  ⟨if forward.value || backward.value then zero else one, forward.work+backward.work+3⟩

theorem point_value {count : ℕ} (source output : Fin count) :
    (point source output).data.decode = if output=source then (1:ℚ) else 0 := by
  have hne : ((lessCounter source.val output.val).value || (lessCounter output.val source.val).value) = true ↔ output ≠ source := by
    simp only [Bool.or_eq_true, lessCounter_value]
    constructor
    · intro h heq
      subst output
      omega
    · intro h
      have hn : output.val ≠ source.val := fun hv => h (Fin.ext hv)
      omega
  unfold point
  dsimp only
  by_cases h : ((lessCounter source.val output.val).value || (lessCounter output.val source.val).value) = true
  · simp only [if_pos h, zero_value, if_neg (hne.mp h)]
  · simp only [if_neg h, one_value, if_pos (not_not.mp (fun hn => h (hne.mpr hn)))]

theorem point_height {count : ℕ} (source output : Fin count) : HeightBound (point source output).data.decode 1 := by
  rw [point_value]
  split_ifs <;> norm_num [HeightBound]

theorem point_work {count : ℕ} (source output : Fin count) : (point source output).work ≤ 12*count+7 := by
  have hf := lessCounter_work source.val output.val
  have hb := lessCounter_work output.val source.val
  change _+_+3 ≤ _
  omega

def delta {count : ℕ} (source : Fin count) : ArrayResult count := buildArray count (point source)

theorem delta_value {count : ℕ} (source output : Fin count) :
    ((delta source).data.get output).decode = if output=source then (1:ℚ) else 0 := by
  rw [delta, buildArray_get, point_value]

theorem delta_inputAt (security : ℕ) (source : Fin (BinaryFirstInverseProgram.colors security)) :
    BinaryFirstInverseProgram.inputAt security (delta source).data =
      fun output => if output=source.val then (1:ℚ) else 0 := by
  funext output
  by_cases h : output<BinaryFirstInverseProgram.colors security
  · simp only [BinaryFirstInverseProgram.inputAt, dif_pos h, delta_value]
    simp only [Fin.ext_iff]
  · have hn : output ≠ source.val := by intro he; subst output; exact h source.isLt
    simp only [BinaryFirstInverseProgram.inputAt, dif_neg h, if_neg hn]

def current (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let input := delta source
  let result := BinaryFirstInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩

theorem current_value (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits source output).data.decode =
      RationalMassLiftProgram.current security bits (fun color => if color=source.val then 1 else 0) output.val := by
  change (BinaryFirstInverseProgram.current _ _ _ _).data.decode = _
  rw [BinaryFirstInverseProgram.current_value, delta_inputAt]

noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.currentHeightPolynomial precision 1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(12*Q+9)+2+BinaryFirstInverseProgram.currentWorkPolynomial precision 1+3

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ)
    (source output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) source output).data.decode
      ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) source output).work ≤ (workPolynomial precision).eval security := by
  have hd (color : Fin (BinaryFirstInverseProgram.colors security)) :
      HeightBound ((delta source).data.get color).decode ((1:Polynomial ℕ).eval security) := by
    rw [delta, buildArray_get]
    simpa only [Polynomial.eval_one] using point_height source color
  have hi := BinaryFirstInverseProgram.current_bounds security precision 1 (delta source).data output hd
  have wd := buildArray_work (BinaryFirstInverseProgram.colors security)
    (12*BinaryFirstInverseProgram.colors security+7) (point source) (point_work source)
  constructor
  · exact hi.1
  · change _+_+3 ≤ _
    have hq := BinaryFirstInverseProgram.colors_bound security
    have wdelta : (delta source).work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*
        (12*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2 := by
      apply wd.trans
      gcongr
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega

end
end CurrentAFT.BinaryMassLiftColumn

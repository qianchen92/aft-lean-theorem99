import AFT.MeanOutput

/-! # Genuine composition of integer body translations inside the safe margin -/

namespace AFT.V7Calibration
open GaussianSource SafeConvolution
open scoped BigOperators Classical
noncomputable section
attribute [local instance] actualModulusNeZero

theorem integerShiftProfile_comp (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ)
    (first second : ℤ)
    (hfirst : ∀ color, profile color ≠ 0 → 0 ≤ (color.val : ℤ)+first ∧ (color.val : ℤ)+first < Parameters.modulus n)
    (hcombined : ∀ color, profile color ≠ 0 → 0 ≤ (color.val : ℤ)+(first+second) ∧
      (color.val : ℤ)+(first+second) < Parameters.modulus n) :
    integerShiftProfile n (integerShiftProfile n profile first) second = integerShiftProfile n profile (first+second) := by
  have hsecond : ∀ color, integerShiftProfile n profile first color ≠ 0 →
      0 ≤ (color.val : ℤ)+second ∧ (color.val : ℤ)+second < Parameters.modulus n := by
    intro color hc
    unfold integerShiftProfile at hc
    obtain ⟨center,_,hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    split_ifs at hh with heq
    · have hb := hcombined center hh
      constructor <;> omega
    · exact (hh rfl).elim
  funext output
  rw [integerShiftProfile_eq_group n _ second hsecond,
    integerShiftProfile_eq_group n _ first hfirst,integerShiftProfile_eq_group n _ (first+second) hcombined]
  congr 1
  rw [map_add]
  abel

theorem rootProfileOperator_shift (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ)
    (shift : ℤ) (hsupport : ∀ color, color ∉ safePalette n → profile color = 0)
    (hshift : |shift|+v7RootCutoff n ≤ (Parameters.safeMargin n : ℤ)) (output : Fin (Parameters.modulus n)) :
    rootProfileOperator n (integerShiftProfile n profile shift) output =
      ∑ root : Window (v7RootCutoff n),
        (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)).weight root*
          integerShiftProfile n profile ((root : ℤ)+shift) output := by
  have hfirst (color) (hc : profile color ≠ 0) :
      0 ≤ (color.val : ℤ)+shift ∧ (color.val : ℤ)+shift < Parameters.modulus n := by
    have hin : color ∈ safePalette n := by by_contra hh; exact hc (hsupport color hh)
    simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,TrimmedSlice.mem_slice] at hin
    have habs := abs_le.mp (le_refl |shift|)
    constructor <;> omega
  change (∑ root : Window (v7RootCutoff n), _*_) = _
  apply Finset.sum_congr rfl
  intro root _
  congr 1
  have hcombined (color) (hc : profile color ≠ 0) :
      0 ≤ (color.val : ℤ)+(shift+(root : ℤ)) ∧ (color.val : ℤ)+(shift+(root : ℤ)) < Parameters.modulus n := by
    have hin : color ∈ safePalette n := by by_contra hh; exact hc (hsupport color hh)
    simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,TrimmedSlice.mem_slice] at hin
    have habs := abs_le.mp (le_refl |shift|)
    have hr := Finset.mem_Icc.mp root.property
    constructor <;> omega
  rw [integerShiftProfile_comp n profile shift root hfirst hcombined,add_comm shift]

/-- The attached body definition equals the root output of its true
source-plus-queue translated center, including the palette boundary. -/
theorem attachedBodyAtSource_root_image (C : ℝ) (n : ℕ) (beta : ℝ) (queue source : ℤ)
    (hsupport : ∀ color, color ∉ safePalette n → actualBodyCenter C n beta color = 0)
    (hshift : |source+queue|+v7RootCutoff n ≤ (Parameters.safeMargin n : ℤ)) :
    rootProfileOperator n (integerShiftProfile n (actualBodyCenter C n beta) (source+queue)) =
      attachedBodyAtSource C n beta queue source := by
  funext output
  rw [rootProfileOperator_shift n _ _ hsupport hshift]
  unfold attachedBodyAtSource
  apply Finset.sum_congr rfl
  intro root _
  rw [add_assoc]

end
end AFT.V7Calibration

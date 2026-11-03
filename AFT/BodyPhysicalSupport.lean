import AFT.BodyFringeParameters

/-! # No mass is lost at the integer palette in a physical body shift -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem integerShiftProfile_mass_of_support (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (shift : ℤ) (hs : ∀ color, profile color ≠ 0 →
      0 ≤ (color.val : ℤ) + shift ∧ (color.val : ℤ) + shift < Parameters.modulus parameter) :
    (∑ output, integerShiftProfile parameter profile shift output) = ∑ center, profile center := by
  unfold integerShiftProfile
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro center _
  by_cases hc : profile center = 0
  · simp only [hc, ite_self, Finset.sum_const_zero]
  · have ht := hs center hc
    let target : Fin (Parameters.modulus parameter) := ⟨((center.val : ℤ) + shift).toNat, by omega⟩
    have htarget : (target.val : ℤ) = (center.val : ℤ) + shift := by dsimp [target]; omega
    have heq (output : Fin (Parameters.modulus parameter)) :
        (output.val : ℤ) = (center.val : ℤ) + shift ↔ output = target := by
      constructor
      · intro hh
        apply paletteInteger_injective parameter
        change (output.val : ℤ) = target.val
        omega
      · rintro rfl
        exact htarget
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem integerShiftProfile_support (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter))
    (hout : (output.val : ℤ) < (Parameters.safeMargin parameter : ℤ) - |shift| ∨
      (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter + |shift| ≤ output.val) :
    integerShiftProfile parameter profile shift output = 0 := by
  apply Finset.sum_eq_zero
  intro center _
  split_ifs with heq
  · apply hs center
    intro hc
    simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
      TrimmedSlice.mem_slice] at hc
    have ha := le_abs_self shift
    have hb := neg_abs_le shift
    omega
  · rfl

theorem rootProfileOperator_mass_of_support (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hs : ∀ color, profile color ≠ 0 →
      (v7RootCutoff parameter : ℤ) ≤ color.val ∧
        (color.val : ℤ) < (Parameters.modulus parameter : ℤ) - v7RootCutoff parameter) :
    (∑ output, rootProfileOperator parameter profile output) = ∑ color, profile color := by
  change (∑ output, ∑ root : Window (v7RootCutoff parameter), _ * _) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hmass (root : Window (v7RootCutoff parameter)) :
      (∑ output, integerShiftProfile parameter profile root output) = ∑ color, profile color := by
    apply integerShiftProfile_mass_of_support
    intro color hc
    have hh := hs color hc
    have hr := Finset.mem_Icc.mp root.property
    omega
  simp_rw [hmass]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- The original safe margin covers both the fixed physical shift and the
remaining actual root source, so the outside mass remains its exact mass. -/
theorem bodyOutside_root_mass (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0)
    (shift : ℤ) (hshift : |shift| + v7RootCutoff parameter ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ output, rootProfileOperator parameter (bodyOutside parameter profile shift) output) =
      bodyOutsideMass parameter profile shift := by
  apply rootProfileOperator_mass_of_support
  intro color hc
  have hh : (Parameters.safeMargin parameter : ℤ) - |shift| ≤ color.val ∧
      (color.val : ℤ) < (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter + |shift| := by
    by_contra hh
    have hz := integerShiftProfile_support parameter profile hs shift color (by omega)
    have hz' : bodyOutside parameter profile shift color = 0 := by
      unfold bodyOutside
      split_ifs <;> simp only [hz]
    exact hc hz'
  omega

end
end AFT.V7Calibration

import AFT.MarkedOutput
import AFT.MaskedWindowTranslation

/-! # The exact safe/interior split of physical body translations -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem paletteInteger_injective (parameter : ℕ) :
    Function.Injective (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) := by
  intro first second heq
  apply Fin.ext
  change (first.val : ℤ) = second.val at heq
  exact_mod_cast heq

theorem interval_palette_translation_l1_le (parameter : ℕ) (start shift : ℤ) (width : ℕ) :
    (∑ color : Fin (Parameters.modulus parameter),
      |intervalAnchorLaw start width ((color.val : ℤ) - shift) - intervalAnchorLaw start width color.val|) ≤
      2 * (shift.natAbs : ℝ) / width := by
  simp_rw [← intervalAnchorLaw_translate]
  have hh := finitePalette_sum_le_support
    (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) (paletteInteger_injective parameter)
    (anchorInterval start width ∪ anchorInterval (start + shift) width)
    (fun color => |intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color|)
    (fun _ => abs_nonneg _) (by
      intro color hout
      have hn : color ∉ anchorInterval start width ∧ color ∉ anchorInterval (start + shift) width := by simpa only [Finset.mem_union, not_or] using hout
      simp only [intervalAnchorLaw, if_neg hn.1, if_neg hn.2, sub_self, abs_zero])
  rw [TrimmedSlice.interval_translation_l1] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right width shift.natAbs) (by norm_num)) (by positivity))

theorem integerShiftProfile_nonneg (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    0 ≤ integerShiftProfile parameter profile shift output := by
  apply Finset.sum_nonneg
  intro center _
  split_ifs
  · exact hn center
  · exact le_rfl

theorem integerShiftProfile_mono (parameter : ℕ) (first second : Fin (Parameters.modulus parameter) → ℝ)
    (h : ∀ color, first color ≤ second color) (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter first shift output ≤ integerShiftProfile parameter second shift output := by
  apply Finset.sum_le_sum
  intro center _
  split_ifs <;> simp_all

theorem integerShiftProfile_smul (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (scalar : ℝ) (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter (fun color => scalar * profile color) shift output =
      scalar * integerShiftProfile parameter profile shift output := by
  unfold integerShiftProfile
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _
  split_ifs <;> ring

theorem integerShiftProfile_bound (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (h : ∀ color, profile color ≤ bound)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter profile shift output ≤ bound := by
  by_cases ht : ∃ center : Fin (Parameters.modulus parameter), (output.val : ℤ) = (center.val : ℤ) + shift
  · obtain ⟨center, hc⟩ := ht
    have heq (other : Fin (Parameters.modulus parameter)) :
        (output.val : ℤ) = (other.val : ℤ) + shift ↔ other = center := by
      constructor
      · intro hh
        apply paletteInteger_injective parameter
        change (other.val : ℤ) = center.val
        omega
      · rintro rfl
        exact hc
    simpa only [integerShiftProfile, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h center
  · have hn (center : Fin (Parameters.modulus parameter)) : ¬ (output.val : ℤ) = (center.val : ℤ) + shift :=
      fun hh => ht ⟨center, hh⟩
    simpa only [integerShiftProfile, if_neg (hn _), Finset.sum_const_zero] using hb

theorem integerShiftProfile_mass_le (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (shift : ℤ) :
    (∑ output, integerShiftProfile parameter profile shift output) ≤ ∑ center, profile center := by
  unfold integerShiftProfile
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro center _
  by_cases ht : 0 ≤ (center.val : ℤ) + shift ∧ (center.val : ℤ) + shift < Parameters.modulus parameter
  · let target : Fin (Parameters.modulus parameter) := ⟨((center.val : ℤ) + shift).toNat, by omega⟩
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
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true, le_refl]
  · have hn' (output : Fin (Parameters.modulus parameter)) :
        ¬ (output.val : ℤ) = (center.val : ℤ) + shift := by have hh := output.isLt; omega
    simpa only [if_neg (hn' _), Finset.sum_const_zero] using hn center

theorem integerShiftProfile_mass (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ output, integerShiftProfile parameter profile shift output) = ∑ center, profile center := by
  unfold integerShiftProfile
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro center _
  by_cases hc : center ∈ safePalette parameter
  · have hm := hc
    simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
      TrimmedSlice.mem_slice] at hm
    have ht : 0 ≤ (center.val : ℤ) + shift ∧ (center.val : ℤ) + shift < Parameters.modulus parameter := by
      have hh := abs_le.mp hshift
      omega
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
  · simp only [hs center hc, ite_self, Finset.sum_const_zero]

def bodyOutside (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  fun output => if output ∈ safePalette parameter then 0 else integerShiftProfile parameter profile shift output

def bodyOutsideMass (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) : ℝ :=
  ∑ output, bodyOutside parameter profile shift output

def bodyInside (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  fun output => (if output ∈ safePalette parameter then integerShiftProfile parameter profile shift output else 0) -
    (1 - bodyOutsideMass parameter profile shift) * profile output

theorem body_shift_split (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter profile shift output - profile output =
      bodyInside parameter profile shift output + bodyOutside parameter profile shift output -
        bodyOutsideMass parameter profile shift * profile output := by
  unfold bodyInside bodyOutside
  split_ifs <;> ring

theorem bodyOutside_nonneg (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    0 ≤ bodyOutside parameter profile shift output := by
  unfold bodyOutside
  split_ifs
  · exact le_rfl
  · exact integerShiftProfile_nonneg parameter profile hn shift output

theorem bodyOutsideMass_bounds (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (hm : ∑ color, profile color = 1) (shift : ℤ) :
    0 ≤ bodyOutsideMass parameter profile shift ∧ bodyOutsideMass parameter profile shift ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun color _ => bodyOutside_nonneg parameter profile hn shift color, ?_⟩
  apply le_trans (Finset.sum_le_sum (fun color _ => ?_)) ((integerShiftProfile_mass_le parameter profile hn shift).trans_eq hm)
  unfold bodyOutside
  split_ifs
  · exact integerShiftProfile_nonneg parameter profile hn shift color
  · exact le_rfl

theorem bodyInside_mass (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hm : ∑ color, profile color = 1)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ color, bodyInside parameter profile shift color) = 0 := by
  have hh := integerShiftProfile_mass parameter profile hs shift hshift
  have hsplit (color) := body_shift_split parameter profile shift color
  have hsum := congrArg (fun f : Fin (Parameters.modulus parameter) → ℝ => ∑ color, f color) (funext hsplit)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hh, hm,
    ] at hsum
  unfold bodyOutsideMass at hsum
  linarith

theorem bodyInside_support (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) (hout : output ∉ safePalette parameter) :
    bodyInside parameter profile shift output = 0 := by
  simp only [bodyInside, if_neg hout, hs output hout, mul_zero, sub_zero]

end
end AFT.V7Calibration

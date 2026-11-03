import AFT.ActualLeadingOutput
import AFT.MarkedOutput
import AFT.V7SafePairInput

/-! # Equality of the genuine integer root channel and palette convolution -/

namespace AFT.V7Calibration
open GaussianSource SafeConvolution RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
attribute [local instance] actualModulusNeZero

/-- A finite signed profile whose shifted support stays inside the palette
has exactly the same integer and group translations. -/
theorem integerShiftProfile_eq_group (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ)
    (shift : ℤ) (hsupport : ∀ center, profile center ≠ 0 →
      0 ≤ (center.val : ℤ)+shift ∧ (center.val : ℤ)+shift < Parameters.modulus n)
    (output : Fin (Parameters.modulus n)) :
    integerShiftProfile n profile shift output = profile (output-paletteEmbedding n shift) := by
  unfold integerShiftProfile
  have hterm (center : Fin (Parameters.modulus n)) :
      (if (output.val : ℤ) = (center.val : ℤ)+shift then profile center else 0) =
        if center = output-paletteEmbedding n shift then profile center else 0 := by
    by_cases hz : profile center = 0
    · simp only [hz,ite_self]
    have hb := hsupport center hz
    have heq : (output.val : ℤ) = (center.val : ℤ)+shift ↔ center = output-paletteEmbedding n shift := by
      constructor
      · intro h
        have hh := congrArg (paletteEmbedding n) h
        rw [map_add,paletteEmbedding_color,paletteEmbedding_color] at hh
        exact (eq_sub_iff_add_eq).mpr hh.symm
      · intro h
        have hh : paletteEmbedding n ((center.val : ℤ)+shift) = output := by
          rw [map_add,paletteEmbedding_color,h]
          abel
        have hv := congrArg (fun color : Fin (Parameters.modulus n) => (color.val : ℤ)) hh
        dsimp only at hv
        rw [paletteEmbedding_val n _ hb.1 hb.2] at hv
        exact hv.symm
    simp only [heq]
  simp_rw [hterm]
  simp

/-- The reserved safe margin proves no wrap for every real root sample;
this is an exact channel identity, without a Gaussian approximation. -/
theorem safe_root_convolution_eq (n : ℕ) (profile : Fin (Parameters.modulus n) → ℝ)
    (hsupport : ∀ center, center ∉ safePalette n → profile center = 0)
    (hmargin : v7RootCutoff n ≤ Parameters.safeMargin n) :
    convolution (actualRootLaw n).weight profile = rootProfileOperator n profile := by
  funext output
  rw [actualRootLaw,convolution_map_apply]
  change (∑ root : Window (v7RootCutoff n), _*_) = ∑ root : Window (v7RootCutoff n), _*_
  apply Finset.sum_congr rfl
  intro root _
  congr 1
  symm
  apply integerShiftProfile_eq_group
  intro center hc
  have hin : center ∈ safePalette n := by
    by_contra hn
    exact hc (hsupport center hn)
  simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
    TrimmedSlice.mem_slice] at hin
  have hr := Finset.mem_Icc.mp root.property
  constructor <;> omega

/-- The actual leading body seed evaluates to the original integer root
operator, including profiles with signed values and zero reference atoms. -/
theorem actualLeadingOutput_safe_body (C : ℝ) (n : ℕ) (beta : ℝ)
    (profile : Fin (Parameters.modulus n) → ℝ)
    (hrecover : ∀ color, (actualBodyLaw C n beta).weight color*
      (profile color/(actualBodyLaw C n beta).weight color) = profile color)
    (hsupport : ∀ color, color ∉ safePalette n → profile color = 0)
    (hmargin : v7RootCutoff n ≤ Parameters.safeMargin n) :
    actualLeadingOutput C n beta (MvPolynomial.X (bodySingletonInput
      (fun color => profile color/(actualBodyLaw C n beta).weight color))) =
    ∑ output, MvPolynomial.C (rootProfileOperator n profile output)*MvPolynomial.X output := by
  rw [actualLeadingOutput_body]
  have heq : (fun color => (actualBodyLaw C n beta).weight color*
      (profile color/(actualBodyLaw C n beta).weight color)) = profile := funext hrecover
  rw [heq,safe_root_convolution_eq n profile hsupport hmargin]

end
end AFT.V7Calibration

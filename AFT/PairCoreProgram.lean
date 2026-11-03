import AFT.SafePairCore
import AFT.V7SafePairInput
import AFT.ActualBodyMeanProgram

/-! # Exact rational core restriction and canonicalization for pair certificates -/
namespace AFT.RationalNumerics
open scoped BigOperators
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def rationalUniformProfile (core : Finset Color) (color : Color) : ℚ :=
  if color∈core then (core.card : ℚ)⁻¹ else 0

def rationalCanonicalPair (reference : Color → ℚ) (mass : Color → Color → ℚ) (first second : Color) : ℚ :=
  mass first second-reference first*(∑ x,mass x second)-(∑ y,mass first y)*reference second+
    (∑ x,∑ y,mass x y)*reference first*reference second

def rationalPairCoreSeed (core : Finset Color) (mass : Color → Color → ℚ) : Color → Color → ℚ :=
  rationalCanonicalPair (rationalUniformProfile core) (fun first second => if first∈core ∧ second∈core then mass first second else 0)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

omit [Fintype Color] in
theorem rationalUniformProfile_cast (core : Finset Color) (color : Color) :
    (rationalUniformProfile core color : ℝ)=uniformFiniteProfile core color := by
  unfold rationalUniformProfile uniformFiniteProfile
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]

omit [DecidableEq Color] in
theorem rationalCanonicalPair_cast (reference : Color → ℚ) (mass : Color → Color → ℚ) (first second : Color) :
    (rationalCanonicalPair reference mass first second : ℝ)=
      SafePair.canonicalPair (fun color => (reference color : ℝ)) (fun first second => (mass first second : ℝ)) first second := by
  simp only [rationalCanonicalPair,SafePair.canonicalPair,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum]

theorem rationalPairCoreSeed_cast (core : Finset Color) (mass : Color → Color → ℚ) (first second : Color) :
    (rationalPairCoreSeed core mass first second : ℝ)=SafePair.coreSeed core (fun first second => (mass first second : ℝ)) first second := by
  simp only [rationalPairCoreSeed,rationalCanonicalPair_cast,rationalUniformProfile_cast,apply_ite,Rat.cast_zero,
    SafePair.coreSeed]
  congr 1

omit [Fintype Color] in
theorem uniformFiniteProfile_abs_le_one (core : Finset Color) (color : Color) : |uniformFiniteProfile core color|≤1 := by
  unfold uniformFiniteProfile
  split_ifs with h
  · rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Finset.one_le_card.mpr ⟨color,h⟩)
  · norm_num

omit [DecidableEq Color] in
theorem canonicalPair_sub (reference : Color → ℝ) (first second : Color → Color → ℝ) (x y : Color) :
    SafePair.canonicalPair reference (fun x y => first x y-second x y) x y=
      SafePair.canonicalPair reference first x y-SafePair.canonicalPair reference second x y := by
  simp only [SafePair.canonicalPair,Finset.sum_sub_distrib]
  ring

omit [DecidableEq Color] in
theorem canonicalPair_bound (reference : Color → ℝ) (mass : Color → Color → ℝ) (bound : ℝ)
    (hb : 0≤bound) (href : ∀ color,|reference color|≤1) (hm : ∀ first second,|mass first second|≤bound)
    (first second : Color) : |SafePair.canonicalPair reference mass first second|≤
      ((Fintype.card Color : ℝ)+1)^2*bound := by
  have hcol (second) : |∑ first,mass first second|≤(Fintype.card Color : ℝ)*bound := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun first _ => hm first second)).trans_eq (by simp))
  have hrow (first) : |∑ second,mass first second|≤(Fintype.card Color : ℝ)*bound := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun second _ => hm first second)).trans_eq (by simp))
  have hall : |∑ first,∑ second,mass first second|≤(Fintype.card Color : ℝ)^2*bound := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun first _ => hrow first)).trans_eq (by simp;ring)
  have hfirst : |reference first*(∑ x,mass x second)|≤(Fintype.card Color : ℝ)*bound := by
    rw [abs_mul]
    exact (mul_le_mul (href first) (hcol second) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsecond : |(∑ y,mass first y)*reference second|≤(Fintype.card Color : ℝ)*bound := by
    rw [abs_mul]
    exact (mul_le_mul (hrow first) (href second) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have htotal : |(∑ x,∑ y,mass x y)*reference first*reference second|≤(Fintype.card Color : ℝ)^2*bound := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul ((mul_le_mul hall (href first) (abs_nonneg _) (by positivity)).trans_eq (mul_one _))
      (href second) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  unfold SafePair.canonicalPair
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hm first second) hfirst)) hsecond)) htotal).trans
  ring_nf
  exact le_refl _

theorem rationalPairCoreSeed_error (core : Finset Color) (program : Color → Color → ℚ)
    (mass : Color → Color → ℝ) (error : ℝ) (he : 0≤error)
    (happrox : ∀ first second,|(program first second : ℝ)-mass first second|≤error) (first second : Color) :
    |(rationalPairCoreSeed core program first second : ℝ)-SafePair.coreSeed core mass first second|≤
      ((Fintype.card Color : ℝ)+1)^2*error := by
  rw [rationalPairCoreSeed_cast]
  unfold SafePair.coreSeed
  rw [←canonicalPair_sub]
  apply canonicalPair_bound _ _ error he (uniformFiniteProfile_abs_le_one core)
  intro x y
  unfold SafePair.restrictPair
  split_ifs
  · exact happrox x y
  · simpa only [sub_self,abs_zero] using he

end
end AFT.RationalNumerics

namespace AFT.V7Calibration
open GaussianSource RationalNumerics

def pairCoreDepthProgram (n depth : ℕ) : ℕ := actualSafeMarginProgram n+(depth+1)*n^3+depth*(3*n^2-1)

def pairCoreProgram (n depth : ℕ) : Finset (Fin (ParameterProgram.modulus n).value) :=
  Finset.univ.filter fun color => pairCoreDepthProgram n depth≤color.val ∧ color.val<(ParameterProgram.modulus n).value-pairCoreDepthProgram n depth

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem pairCoreDepthProgram_eq (n depth : ℕ) : pairCoreDepthProgram n depth=pairCoreDepth n depth := rfl

theorem pairCoreProgram_membership (n depth : ℕ) (color : Fin (ParameterProgram.modulus n).value) :
    color∈pairCoreProgram n depth ↔
      (Fin.cast (ParameterProgram.modulus_value n) color)∈pairCore n depth := by
  simp only [pairCoreProgram,Finset.mem_filter,Finset.mem_univ,true_and,pairCore,TrimmedSlice.paletteSlice,
    TrimmedSlice.slice,max_self,min_self,add_zero,Finset.mem_Ico,pairCoreDepthProgram_eq,Fin.val_cast,
    ParameterProgram.modulus_value]
  omega

end
end AFT.V7Calibration

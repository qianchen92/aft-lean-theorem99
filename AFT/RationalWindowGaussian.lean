import AFT.RationalGaussianProgram
import AFT.RootConvolutionProgram
import AFT.SignedConditioning

/-! # Executable rational normalization of the actual protected Gaussian -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- Guard precision absorbs the number of atoms before normalization. -/
def windowApproxPrecision (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+1

def windowApproxRaw (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  gaussianApprox squaredWidth point (windowApproxPrecision cutoff bits)

def windowApproxNormalizer (squaredWidth : ℚ) (cutoff bits : ℕ) : ℚ :=
  ∑ point : Window cutoff,windowApproxRaw squaredWidth cutoff bits point

/-- This normalized table uses rational arithmetic only, including its denominator. -/
def windowApproxWeight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  windowApproxRaw squaredWidth cutoff bits point/windowApproxNormalizer squaredWidth cutoff bits

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem windowApproxNormalizer_ge_one (squaredWidth : ℚ) (cutoff bits : ℕ) :
    1 ≤ windowApproxNormalizer squaredWidth cutoff bits := by
  have h := Finset.single_le_sum (f:=windowApproxRaw squaredWidth cutoff bits)
    (fun point _ => (gaussianApprox_positive _ _ _).le) (Finset.mem_univ (windowZero cutoff))
  simpa only [windowApproxRaw,windowZero,gaussianApprox_zero] using h

theorem windowApproxWeight_positive (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    0 < windowApproxWeight squaredWidth cutoff bits point :=
  div_pos (gaussianApprox_positive _ _ _) (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _))

theorem windowApproxWeight_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ point : Window cutoff,windowApproxWeight squaredWidth cutoff bits point=1 := by
  simp only [windowApproxWeight,← Finset.sum_div]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _)))

/-- The law represented by the executable rational table. -/
def windowApproxLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) where
  weight point := (windowApproxWeight squaredWidth cutoff bits point : ℝ)
  nonneg point := by exact_mod_cast (windowApproxWeight_positive squaredWidth cutoff bits point).le
  sum_one := by exact_mod_cast windowApproxWeight_sum squaredWidth cutoff bits

theorem windowApproxLaw_l1 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|) ≤ 1/(2 : ℝ)^bits := by
  let raw : Window cutoff → ℝ := fun point => (windowApproxRaw squaredWidth cutoff bits point : ℝ)
  have hraw : 1 ≤ ∑ point,raw point := by
    have hh := windowApproxNormalizer_ge_one squaredWidth cutoff bits
    unfold windowApproxNormalizer at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hnormal := SignedConditioning.normalized_signed_l1 raw (fun point => GaussianSource.weight width point)
    (fun point => (weight_pos _ _).le) (zero_lt_one.trans_le hraw)
    (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff))
  have herr : (∑ point,|raw point-GaussianSource.weight width point|) ≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Window cutoff))) =>
      gaussianApprox_weight_error squaredWidth width point (windowApproxPrecision cutoff bits) hwidth hsquare)
    have hc : Fintype.card (Window cutoff)=2*cutoff+1 := by
      rw [← Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    simpa only [raw,windowApproxRaw,Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,mul_one_div] using hh
  have hden : 0 ≤ ∑ point,|raw point-GaussianSource.weight width point| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have heq : (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|)=
      ∑ point,|raw point/(∑ x,raw x)-GaussianSource.weight width point/(∑ x:Window cutoff,GaussianSource.weight width x)| := by
    apply Finset.sum_congr rfl
    intro point _
    simp only [windowApproxLaw,windowApproxWeight,windowApproxNormalizer,windowGaussian,FiniteDist.normalize,raw,Rat.cast_div,Rat.cast_sum]
  rw [heq]
  calc
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/(∑ x,raw x) := hnormal
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hraw
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by rw [div_one]; gcongr
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by
      gcongr
      exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
    _ = _ := by
      unfold windowApproxPrecision
      rw [pow_add,pow_add]
      field_simp
      ring

end
end AFT.RationalNumerics

import AFT.CenteredGaussianProgram
import AFT.RationalWindowTickets

/-! # Rational normalization of every rational-centered scalar Gaussian

The finite support is translated by the computed rational floor. Thus the
normalizing mass has a uniform lower bound, even when the center itself
is large or depends on the entire previously sampled integer prefix.
-/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

def centeredWindowPrecision (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+8

def centeredWindowRaw (squaredWidth center : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  centeredGaussianApprox squaredWidth center (centeredGaussianAnchor center+point) (centeredWindowPrecision cutoff bits)

def centeredWindowNormalizer (squaredWidth center : ℚ) (cutoff bits : ℕ) : ℚ :=
  ∑ point : Window cutoff,centeredWindowRaw squaredWidth center cutoff bits point

def centeredWindowWeight (squaredWidth center : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  centeredWindowRaw squaredWidth center cutoff bits point/centeredWindowNormalizer squaredWidth center cutoff bits

theorem centeredWindowNormalizer_pos (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    0<centeredWindowNormalizer squaredWidth center cutoff bits := by
  apply Finset.sum_pos'
  · intro point _
    exact (centeredGaussianApprox_positive _ _ _ _).le
  · exact ⟨windowZero cutoff,Finset.mem_univ _,centeredGaussianApprox_positive _ _ _ _⟩

theorem centeredWindowWeight_positive (squaredWidth center : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    0<centeredWindowWeight squaredWidth center cutoff bits point :=
  div_pos (centeredGaussianApprox_positive _ _ _ _) (centeredWindowNormalizer_pos _ _ _ _)

theorem centeredWindowWeight_sum (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    ∑ point : Window cutoff,centeredWindowWeight squaredWidth center cutoff bits point=1 := by
  simp only [centeredWindowWeight,←Finset.sum_div]
  exact div_self (centeredWindowNormalizer_pos _ _ _ _).ne'

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def centeredWindowApproxLaw (squaredWidth center : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) where
  weight point := (centeredWindowWeight squaredWidth center cutoff bits point : ℝ)
  nonneg point := by exact_mod_cast (centeredWindowWeight_positive squaredWidth center cutoff bits point).le
  sum_one := by exact_mod_cast centeredWindowWeight_sum squaredWidth center cutoff bits

def centeredWindowMass (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : Window cutoff) : ℝ :=
  shiftedWeight width center (centeredGaussianAnchor center+point)

theorem centeredWindowMass_pos (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : Window cutoff) :
    0<centeredWindowMass width center cutoff point := Real.exp_pos _

def centeredWindowLaw (width : ℝ) (center : ℚ) (cutoff : ℕ) : FiniteDist (Window cutoff) :=
  FiniteDist.normalize (centeredWindowMass width center cutoff)
    (fun point => (centeredWindowMass_pos width center cutoff point).le)
    (Finset.sum_pos' (fun point _ => (centeredWindowMass_pos width center cutoff point).le)
      ⟨windowZero cutoff,Finset.mem_univ _,centeredWindowMass_pos _ _ _ _⟩)

theorem exp_pi_le_81 : Real.exp Real.pi≤81 := by
  calc
    _ ≤ Real.exp (4 : ℝ) := Real.exp_le_exp.mpr Real.pi_lt_four.le
    _ = (Real.exp 1)^4 := by rw [←Real.exp_nat_mul];norm_num
    _ ≤ (3 : ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
    _ = _ := by norm_num

/-- The floor-centered window always contains an atom of mass at least
`exp(-pi)` whenever the scalar width is at least one. -/
theorem centeredWindowMass_sum_lower (width : ℝ) (center : ℚ) (cutoff : ℕ) (hw : 1≤width) :
    Real.exp (-Real.pi)≤∑ point,centeredWindowMass width center cutoff point := by
  apply le_trans _ (Finset.single_le_sum
    (fun point _ => (centeredWindowMass_pos width center cutoff point).le) (Finset.mem_univ (windowZero cutoff)))
  have hc := centeredGaussianAnchor_bounds center
  have hdist : ((centeredGaussianAnchor center : ℝ)-(center : ℝ))^2≤1 := by nlinarith
  have hw2 : 1≤width^2 := by nlinarith
  have hratio : ((centeredGaussianAnchor center : ℝ)-(center : ℝ))^2/width^2≤1 := by
    apply (div_le_one (by positivity : 0<width^2)).mpr
    exact hdist.trans hw2
  apply Real.exp_le_exp.mpr
  simp only [windowZero,Int.add_zero]
  calc
    -Real.pi ≤ -Real.pi*(((centeredGaussianAnchor center : ℝ)-(center : ℝ))^2/width^2) := by
      nlinarith [Real.pi_pos]
    _ = _ := by ring

/-- Full normalized error, uniform in the rational center and width.
Neither a real normalizer nor its approximation is an input hypothesis. -/
theorem centeredWindowApproxLaw_l1 (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hw : 1≤width) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(centeredWindowApproxLaw squaredWidth center cutoff bits).weight point-
      (centeredWindowLaw width center cutoff).weight point|)≤1/(2 : ℝ)^bits := by
  have hwidth : 0<squaredWidth := by
    have hh : (0 : ℝ)<squaredWidth := by rw [←hsquare];positivity
    exact_mod_cast hh
  let raw : Window cutoff → ℝ := fun point => (centeredWindowRaw squaredWidth center cutoff bits point : ℝ)
  let exactMass := centeredWindowMass width center cutoff
  have hraw : 0<∑ point,raw point := by
    have hh := centeredWindowNormalizer_pos squaredWidth center cutoff bits
    unfold centeredWindowNormalizer at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hlower := centeredWindowMass_sum_lower width center cutoff hw
  have hnormal := SignedConditioning.normalized_signed_l1 exactMass raw
    (fun point => by
      dsimp only [raw,centeredWindowRaw]
      exact_mod_cast (centeredGaussianApprox_positive squaredWidth center
        (centeredGaussianAnchor center+point) (centeredWindowPrecision cutoff bits)).le)
    ((Real.exp_pos _).trans_le hlower) hraw
  have herr : (∑ point,|exactMass point-raw point|)≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(centeredWindowPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point∈(Finset.univ : Finset (Window cutoff))) =>
      centeredGaussianApprox_shifted_error squaredWidth center width (centeredGaussianAnchor center+point)
        (centeredWindowPrecision cutoff bits) hwidth hsquare)
    have hc : Fintype.card (Window cutoff)=2*cutoff+1 := by
      rw [←Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    simpa only [raw,exactMass,centeredWindowRaw,centeredWindowMass,abs_sub_comm,
      Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,mul_one_div] using hh
  have heq : (∑ point,|(centeredWindowApproxLaw squaredWidth center cutoff bits).weight point-
      (centeredWindowLaw width center cutoff).weight point|)=
      ∑ point,|exactMass point/(∑x,exactMass x)-raw point/(∑x,raw x)| := by
    apply Finset.sum_congr rfl
    intro point _
    simp only [centeredWindowApproxLaw,centeredWindowWeight,centeredWindowNormalizer,
      centeredWindowLaw,FiniteDist.normalize,raw,exactMass,Rat.cast_div,Rat.cast_sum,abs_sub_comm]
  rw [heq]
  calc
    _ ≤ 2*(∑ point,|exactMass point-raw point|)/(∑point,exactMass point) := hnormal
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(centeredWindowPrecision cutoff bits))/Real.exp (-Real.pi) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left herr (by norm_num))
        ((Real.exp_pos _).le.trans hlower)).trans
      exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hlower
    _ = 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(centeredWindowPrecision cutoff bits))*Real.exp Real.pi := by
      rw [div_eq_mul_inv,Real.exp_neg,inv_inv]
    _ ≤ 162*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(centeredWindowPrecision cutoff bits)) := by
      have hc : ((2*cutoff+1 : ℕ) : ℝ)≤(2 : ℝ)^(2*cutoff+1) := by
        exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ)≤(2 : ℝ)^(centeredWindowPrecision cutoff bits))) (by norm_num : (0 : ℝ)≤2)) exp_pi_le_81
        (Real.exp_pos _).le (by positivity)
      exact hh.trans_eq (by ring)
    _ ≤ _ := by
      have hexp : (2 : ℝ)^centeredWindowPrecision cutoff bits=
          (2 : ℝ)^bits*(2 : ℝ)^(2*cutoff+1)*256 := by
        unfold centeredWindowPrecision
        rw [pow_add,pow_add]
        norm_num
      rw [hexp]
      have heq : 162*((2 : ℝ)^(2*cutoff+1)/((2 : ℝ)^bits*(2 : ℝ)^(2*cutoff+1)*256))=
          (162/256 : ℝ)/(2 : ℝ)^bits := by field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right (by norm_num : (162/256 : ℝ)≤1) (by positivity)


end
end AFT.RationalNumerics

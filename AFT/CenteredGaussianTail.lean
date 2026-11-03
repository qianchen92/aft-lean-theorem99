import AFT.CenteredGaussianTickets

/-! # Uniform infinite-lattice tails for the computed-center scalar steps -/
namespace AFT.RationalNumerics
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def centeredClippingMass (width : ℝ) (center : ℚ) (cutoff : ℝ) : ℝ :=
  ∑' point : ℤ,if cutoff≤|(point : ℝ)-(centeredGaussianAnchor center : ℝ)| then
    shiftedWeight width center point else 0

theorem summable_centeredClippingMass (width : ℝ) (center : ℚ) (cutoff : ℝ) (hw : 0<width) :
    Summable (fun point : ℤ => if cutoff≤|(point : ℝ)-(centeredGaussianAnchor center : ℝ)| then
      shiftedWeight width center point else 0) := by
  apply Summable.of_nonneg_of_le _ _ (summable_shiftedWeight width center hw)
  · intro point
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · intro point
    split_ifs
    · rfl
    · exact (Real.exp_pos _).le

theorem centeredClippingMass_le (width : ℝ) (center : ℚ) (cutoff : ℝ)
    (hw : 0<width) (hc : 1≤cutoff) :
    centeredClippingMass width center cutoff≤
      Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2))*theta (Real.sqrt 2*width) center := by
  have hw2 : 0<Real.sqrt 2*width := by positivity
  have hsquare : (Real.sqrt 2*width)^2=2*width^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  have hcenter := centeredGaussianAnchor_bounds center
  have hres : |(center : ℝ)-(centeredGaussianAnchor center : ℝ)|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hcenter.1)]
    linarith
  have hpoint (point : ℤ) :
      (if cutoff≤|(point : ℝ)-(centeredGaussianAnchor center : ℝ)| then shiftedWeight width center point else 0)≤
      Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2))*shiftedWeight (Real.sqrt 2*width) center point := by
    split_ifs with hp
    · have habs : cutoff-1≤|(point : ℝ)-(center : ℝ)| := by
        have ht := abs_sub_le (point : ℝ) (center : ℝ) (centeredGaussianAnchor center : ℝ)
        linarith
      have hsq : (cutoff-1)^2≤((point : ℝ)-(center : ℝ))^2 := by
        nlinarith [sq_abs ((point : ℝ)-(center : ℝ)),abs_nonneg ((point : ℝ)-(center : ℝ))]
      simp only [shiftedWeight,hsquare,←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : 0≤Real.pi/width^2 := by positivity
      have he : -Real.pi*(cutoff-1)^2/(2*width^2)+
          -(Real.pi/(2*width^2))*((point : ℝ)-(center : ℝ))^2=
          -(Real.pi/width^2)*((cutoff-1)^2+((point : ℝ)-(center : ℝ))^2)/2 := by ring
      rw [he]
      nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hsq)]
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hh := (summable_centeredClippingMass width center cutoff hw).tsum_le_tsum hpoint
    ((summable_shiftedWeight (Real.sqrt 2*width) center hw2).mul_left _)
  exact hh.trans_eq tsum_mul_left

/-- Poisson's already proved uniform theta estimate supplies an explicit
polynomial prefactor for every rational center, not just center zero. -/
theorem theta_le_five_width (width center : ℝ) (hw : 1≤width) : theta width center≤5*width := by
  have hw0 : 0<width := lt_of_lt_of_le zero_lt_one hw
  have ht := (theta_relative_error_exp width center hw0).trans (thetaError_le_four_exp width hw)
  have hexp : Real.exp (-Real.pi*width^2)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))
  have hu := (abs_le.mp ht).2
  have hquot : theta width center/width≤5 := by nlinarith
  exact (div_le_iff₀ hw0).mp hquot

theorem theta_rational_center_lower (width : ℝ) (center : ℚ) (hw : 1≤width) :
    Real.exp (-Real.pi)≤theta width center := by
  have hh := centeredWindowMass_sum_lower width center 0 hw
  have he : (∑ point : Window 0,centeredWindowMass width center 0 point)=
      shiftedWeight width center (centeredGaussianAnchor center) := by
    rw [Finset.sum_eq_single (windowZero 0)]
    · simp only [centeredWindowMass,windowZero,add_zero]
    · intro point _ hn
      exfalso
      apply hn
      apply Subtype.ext
      have hp := Finset.mem_Icc.mp point.property
      change point.val=0
      norm_num at hp
      omega
    · simp
  rw [he] at hh
  exact hh.trans ((summable_shiftedWeight width center (lt_of_lt_of_le zero_lt_one hw)).le_tsum
    (centeredGaussianAnchor center) (fun point _ => (Real.exp_pos _).le))

def centeredClippingProbability (width : ℝ) (center : ℚ) (cutoff : ℝ) : ℝ :=
  centeredClippingMass width center cutoff/theta width center

/-- The exact infinite scalar law discarded outside the translated window
is uniformly exponentially small, with a polynomial width prefactor. -/
theorem centeredClippingProbability_le (width : ℝ) (center : ℚ) (cutoff : ℝ)
    (hw : 1≤width) (hc : 1≤cutoff) :
    centeredClippingProbability width center cutoff≤
      810*width*Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2)) := by
  have hw0 : 0<width := lt_of_lt_of_le zero_lt_one hw
  have hsqrt : 1≤Real.sqrt 2 := by exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hsqrt2 : Real.sqrt 2≤2 := by exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hw2 : 1≤Real.sqrt 2*width := by
    simpa only [one_mul] using mul_le_mul hsqrt hw (by norm_num : (0 : ℝ)≤1) (by positivity : 0≤Real.sqrt 2)
  have hm := centeredClippingMass_le width center cutoff hw0 hc
  have ht := theta_le_five_width (Real.sqrt 2*width) center hw2
  have ht' : theta (Real.sqrt 2*width) center≤10*width := by nlinarith
  have hnum := hm.trans (mul_le_mul_of_nonneg_left ht' (Real.exp_pos _).le)
  have hden := theta_rational_center_lower width center hw
  unfold centeredClippingProbability
  calc
    _ ≤ (Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2))*(10*width))/Real.exp (-Real.pi) := by
      apply (div_le_div_of_nonneg_right hnum (theta_pos width center hw0).le).trans
      exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hden
    _ = (Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2))*(10*width))*Real.exp Real.pi := by
      rw [div_eq_mul_inv,Real.exp_neg,inv_inv]
    _ ≤ (Real.exp (-Real.pi*(cutoff-1)^2/(2*width^2))*(10*width))*81 :=
      mul_le_mul_of_nonneg_left exp_pi_le_81 (by positivity)
    _ = _ := by ring

end
end AFT.RationalNumerics

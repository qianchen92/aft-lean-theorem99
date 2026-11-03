import AFT.GaussianConvolutionTV

/-! # Finite-dimensional triangular Gaussian sums from scalar Poisson bounds

The center of each scalar Gaussian may depend on every later integer
coordinate. Thus these are correlated elliptic Gaussian weights, rather
than a product-independence assumption.
-/
namespace AFT.GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Reverse conditional Gaussian coordinates. Triangular quadratic forms
are represented by linear choices of `center`; the summation theorem even
allows arbitrary dependence on the complete later vector. -/
inductive GaussianChain : ℕ → Type
  | nil : GaussianChain 0
  | cons {count : ℕ} (width : ℝ) (center : (Fin count → ℤ) → ℝ)
      (tail : GaussianChain count) : GaussianChain (count+1)

def GaussianChain.weight : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      shiftedWeight width (center (Fin.tail word)) (word 0) * tail.weight (Fin.tail word)

def GaussianChain.volume : {count : ℕ} → GaussianChain count → ℝ
  | 0,.nil => 1
  | _+1,.cons width _ tail => width*tail.volume

def GaussianChain.Wide (base : ℝ) : {count : ℕ} → GaussianChain count → Prop
  | 0,.nil => True
  | _+1,.cons width _ tail => base≤width ∧ tail.Wide base

theorem GaussianChain.weight_pos {count : ℕ} (chain : GaussianChain count) (word : Fin count → ℤ) :
    0<chain.weight word := by
  induction chain with
  | nil => exact zero_lt_one
  | cons width center tail ih => exact mul_pos (Real.exp_pos _) (ih _)

theorem GaussianChain.volume_pos {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) : 0<chain.volume := by
  induction chain with
  | nil => exact zero_lt_one
  | cons width center tail ih => exact mul_pos (hb.trans_le hw.1) (ih hw.2)

/-- Summability and normalization bounds are proved together on the actual
integer vector sum. All centers are allowed to depend on the remaining
coordinates; no multivariate Poisson theorem is assumed. -/
theorem GaussianChain.summable_and_bounds {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) :
    Summable chain.weight ∧
      chain.volume*(1-error)^count ≤ ∑' word,chain.weight word ∧
      (∑' word,chain.weight word) ≤ chain.volume*(1+error)^count := by
  induction chain with
  | nil =>
    simp only [GaussianChain.weight,GaussianChain.volume,pow_zero,mul_one]
    exact ⟨(hasSum_fintype _).summable,by simp,by simp⟩
  | @cons count width center tail ih =>
    obtain ⟨hts,htlo,hthi⟩ := ih hw.2
    have hwidth : 0<width := hb.trans_le hw.1
    have hlocal (rest : Fin count → ℤ) :
        width*(1-error)≤theta width (center rest) ∧
          theta width (center rest)≤width*(1+error) := by
      have h := (theta_relative_error_exp width (center rest) hwidth).trans
        ((thetaError_antitone base width hb hw.1).trans htheta)
      obtain ⟨hl,hu⟩ := abs_le.mp h
      constructor
      · have hh := (le_div_iff₀ hwidth).mp (show 1-error≤theta width (center rest)/width by linarith)
        nlinarith
      · have hh := (div_le_iff₀ hwidth).mp (show theta width (center rest)/width≤1+error by linarith)
        nlinarith
    have hs (rest : Fin count → ℤ) :
        Summable (fun first : ℤ => shiftedWeight width (center rest) first * tail.weight rest) :=
      (summable_shiftedWeight width (center rest) hwidth).mul_right _
    have hp : Summable (fun rest : Fin count → ℤ => theta width (center rest)*tail.weight rest) :=
      Summable.of_nonneg_of_le
        (fun rest => mul_nonneg (theta_pos width (center rest) hwidth).le (tail.weight_pos rest).le)
        (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).2 (tail.weight_pos rest).le)
        (hts.mul_left (width*(1+error)))
    have hpair : Summable (fun point : (Fin count → ℤ) × ℤ =>
        shiftedWeight width (center point.1) point.2*tail.weight point.1) := by
      apply (summable_prod_of_nonneg (fun point =>
        mul_nonneg (Real.exp_pos _).le (tail.weight_pos _).le)).mpr
      constructor
      · exact hs
      · simpa only [tsum_mul_right] using hp
    let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
    have heq (point : (Fin count → ℤ) × ℤ) :
        (GaussianChain.cons width center tail).weight (equiv point) =
          shiftedWeight width (center point.1) point.2*tail.weight point.1 := by
      simp [equiv,GaussianChain.weight,Fin.consEquiv]
    have hsall : Summable (GaussianChain.cons width center tail).weight := by
      apply equiv.summable_iff.mp
      simpa only [heq] using hpair
    have hsum : (∑' word,(GaussianChain.cons width center tail).weight word) =
        ∑' rest : Fin count → ℤ,theta width (center rest)*tail.weight rest := by
      rw [← equiv.tsum_eq]
      simp only [heq]
      rw [hpair.tsum_prod]
      apply tsum_congr
      intro rest
      change (∑' first : ℤ,shiftedWeight width (center rest) first*tail.weight rest)=_
      exact tsum_mul_right
    refine ⟨hsall,?_,?_⟩
    · rw [hsum]
      calc
        (GaussianChain.cons width center tail).volume*(1-error)^(count+1) =
            width*(1-error)*(tail.volume*(1-error)^count) := by
          simp only [GaussianChain.volume,pow_succ]; ring
        _ ≤ width*(1-error)*(∑' rest,tail.weight rest) :=
          mul_le_mul_of_nonneg_left htlo (mul_nonneg hwidth.le (by linarith))
        _ = ∑' rest,width*(1-error)*tail.weight rest := tsum_mul_left.symm
        _ ≤ _ := (hts.mul_left _).tsum_le_tsum
          (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).1 (tail.weight_pos rest).le) hp
    · rw [hsum]
      calc
        _ ≤ ∑' rest,width*(1+error)*tail.weight rest := hp.tsum_le_tsum
          (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).2 (tail.weight_pos rest).le) (hts.mul_left _)
        _ = width*(1+error)*(∑' rest,tail.weight rest) := tsum_mul_left
        _ ≤ width*(1+error)*(tail.volume*(1+error)^count) :=
          mul_le_mul_of_nonneg_left hthi (by positivity)
        _ = _ := by simp only [GaussianChain.volume,pow_succ]; ring

/-- Uniform relative theta error for an arbitrary triangular Gaussian.
This is the finite-dimensional multiplier `(1+error)^count-1` used in V7. -/
theorem GaussianChain.relative_normalizer_error {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) :
    |(∑' word,chain.weight word)/chain.volume-1|≤(1+error)^count-1 := by
  obtain ⟨_,hlo,hhi⟩ := chain.summable_and_bounds base error hb he he1 htheta hw
  have hv := chain.volume_pos base hb hw
  have hl : (1-error)^count≤(∑' word,chain.weight word)/chain.volume :=
    (le_div_iff₀ hv).mpr (by simpa only [mul_comm] using hlo)
  have hu : (∑' word,chain.weight word)/chain.volume≤(1+error)^count :=
    (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hhi)
  have hplus := one_add_mul_le_pow (show (-2 : ℝ)≤error by linarith) count
  have hminus := one_add_mul_le_pow (show (-2 : ℝ)≤ -error by linarith) count
  simp only [mul_neg,← sub_eq_add_neg] at hminus
  apply abs_le.mpr
  constructor <;> linarith

/-- In the convolution conditional covariance, every scalar width at
least `sigma/sqrt(2)` gives the exact V7 exponentially small error. -/
theorem GaussianChain.v7_conditional_theta_error {count : ℕ} (chain : GaussianChain count)
    (sigma : ℝ) (hsigma : Real.sqrt 2≤sigma)
    (hsmall : 4*Real.exp (-Real.pi*sigma^2/2)≤1)
    (hw : chain.Wide (sigma/Real.sqrt 2)) :
    |(∑' word,chain.weight word)/chain.volume-1|≤
      (1+4*Real.exp (-Real.pi*sigma^2/2))^count-1 := by
  have hs : 0<sigma := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ)<2)).trans_le hsigma
  have hbase : 1≤sigma/Real.sqrt 2 :=
    (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ)<2))).mpr (by simpa using hsigma)
  apply chain.relative_normalizer_error (sigma/Real.sqrt 2) _ (by positivity) (by positivity) hsmall _ hw
  have hh := thetaError_le_four_exp (sigma/Real.sqrt 2) hbase
  rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] at hh
  rw [show -Real.pi*(sigma^2/2)= -Real.pi*sigma^2/2 by ring] at hh
  exact hh

end
end AFT.GaussianSource

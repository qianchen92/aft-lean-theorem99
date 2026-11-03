import AFT.TriangularGaussian

/-! # The actual sequential scalar Gaussian sampler and its correlated target law -/
namespace AFT.GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Each step draws its integer coordinate from the normalized scalar
Gaussian whose center is determined by all later realized coordinates. -/
def GaussianChain.sequentialMass : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      shiftedWeight width (center (Fin.tail word)) (word 0) / theta width (center (Fin.tail word)) *
        tail.sequentialMass (Fin.tail word)

/-- The target is the genuinely normalized correlated integer Gaussian. -/
def GaussianChain.normalizedMass {count : ℕ} (chain : GaussianChain count) (word : Fin count → ℤ) : ℝ :=
  chain.weight word/(∑' vector,chain.weight vector)

theorem GaussianChain.sequentialMass_nonneg {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) (word : Fin count → ℤ) :
    0≤chain.sequentialMass word := by
  induction chain with
  | nil => exact zero_le_one
  | cons width center tail ih =>
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (theta_pos width _ (hb.trans_le hw.1)).le) (ih hw.2 _)

/-- This finite recursive sequence is a probability law before any
comparison with its elliptic Gaussian target. -/
theorem GaussianChain.sequentialMass_probability {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) :
    Summable chain.sequentialMass ∧ (∑' word,chain.sequentialMass word)=1 := by
  induction chain with
  | nil => exact ⟨(hasSum_fintype _).summable,by simp [sequentialMass]⟩
  | @cons count width center tail ih =>
    obtain ⟨hts,htone⟩ := ih hw.2
    have hwidth : 0<width := hb.trans_le hw.1
    have hlocal (rest : Fin count → ℤ) :
        Summable (fun first : ℤ => shiftedWeight width (center rest) first/theta width (center rest)) ∧
        (∑' first : ℤ,shiftedWeight width (center rest) first/theta width (center rest))=1 := by
      refine ⟨(summable_shiftedWeight width (center rest) hwidth).div_const _,?_⟩
      rw [tsum_div_const]
      exact div_self (theta_pos width (center rest) hwidth).ne'
    have hinner (rest : Fin count → ℤ) :
        (∑' first : ℤ, shiftedWeight width (center rest) first/theta width (center rest)*tail.sequentialMass rest)=tail.sequentialMass rest := by
      rw [tsum_mul_right,(hlocal rest).2,one_mul]
    have hpair : Summable (fun point : (Fin count → ℤ) × ℤ =>
        shiftedWeight width (center point.1) point.2/theta width (center point.1)*tail.sequentialMass point.1) := by
      apply (summable_prod_of_nonneg (fun point => mul_nonneg
        (div_nonneg (Real.exp_pos _).le (theta_pos width _ hwidth).le)
        (tail.sequentialMass_nonneg base hb hw.2 _))).mpr
      constructor
      · intro rest
        exact (hlocal rest).1.mul_right (tail.sequentialMass rest)
      · change Summable (fun rest : Fin count → ℤ => ∑' first : ℤ,
          shiftedWeight width (center rest) first/theta width (center rest)*tail.sequentialMass rest)
        simpa only [hinner] using hts
    let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
    have heq (point : (Fin count → ℤ) × ℤ) :
        (GaussianChain.cons width center tail).sequentialMass (equiv point)=
          shiftedWeight width (center point.1) point.2/theta width (center point.1)*tail.sequentialMass point.1 := by
      simp [equiv,sequentialMass,Fin.consEquiv]
    constructor
    · apply equiv.summable_iff.mp
      simpa only [heq] using hpair
    · rw [← equiv.tsum_eq]
      simp only [heq]
      rw [hpair.tsum_prod]
      simpa only [hinner] using htone

/-- The sampler's actual normalizing factors along one realized vector. -/
def GaussianChain.localNormalizer : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word)

theorem GaussianChain.weight_eq_sequential {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) (word : Fin count → ℤ) :
    chain.weight word=chain.localNormalizer word*chain.sequentialMass word := by
  induction chain with
  | nil => simp [weight,localNormalizer,sequentialMass]
  | cons width center tail ih =>
    change shiftedWeight width (center (Fin.tail word)) (word 0)*tail.weight (Fin.tail word)=
      (theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word))*
        (shiftedWeight width (center (Fin.tail word)) (word 0)/theta width (center (Fin.tail word))*tail.sequentialMass (Fin.tail word))
    rw [ih hw.2]
    have ht := (theta_pos width (center (Fin.tail word)) (hb.trans_le hw.1)).ne'
    field_simp

theorem GaussianChain.localNormalizer_bounds {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) (word : Fin count → ℤ) :
    chain.volume*(1-error)^count≤chain.localNormalizer word ∧
      chain.localNormalizer word≤chain.volume*(1+error)^count := by
  induction chain with
  | nil => simp [volume,localNormalizer]
  | @cons count width center tail ih =>
    have hwidth : 0<width := hb.trans_le hw.1
    have h := (theta_relative_error_exp width (center (Fin.tail word)) hwidth).trans
      ((thetaError_antitone base width hb hw.1).trans htheta)
    obtain ⟨hl,hu⟩ := abs_le.mp h
    have hlo : width*(1-error)≤theta width (center (Fin.tail word)) := by
      have hh := (le_div_iff₀ hwidth).mp (show 1-error≤theta width (center (Fin.tail word))/width by linarith)
      nlinarith
    have hhi : theta width (center (Fin.tail word))≤width*(1+error) := by
      have hh := (div_le_iff₀ hwidth).mp (show theta width (center (Fin.tail word))/width≤1+error by linarith)
      nlinarith
    obtain ⟨htlo,hthi⟩ := ih hw.2 (Fin.tail word)
    have hv := (tail.volume_pos base hb hw.2).le
    constructor
    · calc
        (GaussianChain.cons width center tail).volume*(1-error)^(count+1)=
            (width*(1-error))*(tail.volume*(1-error)^count) := by simp only [volume,pow_succ]; ring
        _ ≤ theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word) :=
          mul_le_mul hlo htlo (mul_nonneg hv (pow_nonneg (by linarith) _)) (theta_pos width _ hwidth).le
        _ = _ := rfl
    · calc
        (GaussianChain.cons width center tail).localNormalizer word≤
            (width*(1+error))*(tail.volume*(1+error)^count) := by
          exact mul_le_mul hhi hthi
            ((mul_nonneg hv (pow_nonneg (by linarith) _)).trans htlo)
            (by positivity)
        _ = _ := by simp only [volume,pow_succ]; ring

/-- The error uses all dimensions, with the same multiplicative theta
factor as the frozen V7 sequential-sampling argument. -/
theorem GaussianChain.weight_sequential_error {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) (word : Fin count → ℤ) :
    |chain.weight word-chain.volume*chain.sequentialMass word|≤
      ((1+error)^count-1)*chain.volume*chain.sequentialMass word := by
  obtain ⟨hlo,hhi⟩ := chain.localNormalizer_bounds base error hb he he1 htheta hw word
  have hv := chain.volume_pos base hb hw
  have hp := one_add_mul_le_pow (show (-2 : ℝ)≤error by linarith) count
  have hn := one_add_mul_le_pow (show (-2 : ℝ)≤ -error by linarith) count
  simp only [mul_neg,← sub_eq_add_neg] at hn
  have hs : |chain.localNormalizer word-chain.volume|≤((1+error)^count-1)*chain.volume := by
    apply abs_le.mpr
    constructor
    · have hh := mul_le_mul_of_nonneg_left (show 2-(1+error)^count≤(1-error)^count by linarith) hv.le
      nlinarith
    · nlinarith
  rw [chain.weight_eq_sequential base hb hw word,← sub_mul,abs_mul,
    abs_of_nonneg (chain.sequentialMass_nonneg base hb hw word)]
  exact mul_le_mul_of_nonneg_right hs (chain.sequentialMass_nonneg base hb hw word)

/-- Total variation between the true sequential normalized scalar draws
and the true normalized correlated target. Neither normalizer is omitted. -/
theorem GaussianChain.sequential_total_variation {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base)
    (hsmall : (1+error)^count-1<1) :
    (∑' word,|chain.normalizedMass word-chain.sequentialMass word|)/2≤
      ((1+error)^count-1)/(1-((1+error)^count-1)) := by
  obtain ⟨hweight,_,_⟩ := chain.summable_and_bounds base error hb he he1 htheta hw
  obtain ⟨hseq,hseqone⟩ := chain.sequentialMass_probability base hb hw
  have hz : 0<∑' word,chain.weight word := by
    exact (chain.weight_pos (fun _ => 0)).trans_le (hweight.le_tsum (fun _ => 0) (fun word _ => (chain.weight_pos word).le))
  have hactual : Summable chain.normalizedMass := hweight.div_const _
  have hactualone : (∑' word,chain.normalizedMass word)=1 := by
    unfold normalizedMass
    rw [tsum_div_const,div_self hz.ne']
  have herr : 0≤(1+error)^count-1 := by
    have hh : 1≤(1+error)^count := one_le_pow₀ (by linarith)
    linarith
  apply normalized_tilt_total_variation chain.sequentialMass chain.normalizedMass
    (chain.sequentialMass_nonneg base hb hw) hseq hactual hseqone hactualone
    (chain.volume/(∑' word,chain.weight word)) _ herr hsmall
  intro word
  have hp := div_le_div_of_nonneg_right (chain.weight_sequential_error base error hb he he1 htheta hw word) hz.le
  convert hp using 1
  · rw [normalizedMass,div_mul_eq_mul_div,div_sub_div_same,abs_div,abs_of_pos hz]
  · ring

end
end AFT.GaussianSource

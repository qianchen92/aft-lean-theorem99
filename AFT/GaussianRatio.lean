import AFT.GaussianConvolution
import AFT.QuadraticRootBounds

/-!
# Gaussian marginal-ratio algebra

The normalizers cancel exactly from the ratio relative to the true
one-coordinate marginals. The remaining exponent is the quadratic
polynomial used by the canonical root bounds.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def sumModel (width normalization : ℝ) (count : ℕ) (target : ℤ) : ℝ :=
  (width / normalization) ^ count / (Real.sqrt (count : ℝ) * width) *
    Real.exp (-Real.pi * (target : ℝ) ^ 2 / ((count : ℝ) * width ^ 2))

noncomputable def sumAmplitude (width normalization : ℝ) (count : ℕ) : ℝ :=
  (width / normalization) ^ count / (Real.sqrt (count : ℝ) * width)

theorem sumModel_pos (width normalization : ℝ) (count : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (hc : 0 < count) (target : ℤ) :
    0 < sumModel width normalization count target := by
  unfold sumModel
  positivity

theorem gaussianSumApprox_model (width : ℝ) (hw : 0 < width) (merges : ℕ) (target : ℤ) :
    (width / realNormalizer width) ^ (merges + 1) *
        gaussianKernel (powerWidth width merges) target =
      sumModel width (realNormalizer width) (merges + 1) target := by
  rw [gaussianKernel, weight, powerWidth_eq width hw merges]
  unfold sumModel
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (merges + 1 : ℕ))]
  push_cast
  have he : -(Real.pi / (((merges : ℝ) + 1) * width ^ 2)) * (target : ℝ) ^ 2 =
      -Real.pi * (target : ℝ) ^ 2 / (((merges : ℝ) + 1) * width ^ 2) := by ring
  rw [he]
  ring

/-- The exact scalar prefactor before simplifying its square roots. -/
noncomputable def rootModelPrefactor (width normalization : ℝ) (population order : ℕ) : ℝ :=
  sumAmplitude width normalization (population - order) *
    sumAmplitude width normalization population ^ (order - 1) /
      sumAmplitude width normalization (population - 1) ^ order

/-- The ordinary lattice-width form of the root quadratic exponent. -/
noncomputable def rootExponent (width : ℝ) (population : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ℤ) : ℝ :=
  Real.pi / width ^ 2 * ((∑ i, (value i : ℝ) ^ 2) / ((population : ℝ) - 1) -
    (∑ i, (value i : ℝ)) ^ 2 / ((population : ℝ) - Fintype.card ι))

/-- Exact conversion to the standard-deviation variables used by the
canonical polynomial moment bounds. -/
theorem rootExponent_eq_quadratic (width : ℝ) (population : ℕ) {ι : Type*} [Fintype ι]
    (value : ι → ℤ) :
    rootExponent width population value =
      MvPolynomial.eval (fun i => Real.sqrt (2 * Real.pi) * (value i : ℝ) / width)
        (RootSlice.quadraticExponent (population : ℝ)) := by
  rw [RootSlice.quadraticExponent_eval]
  have hs : (∑ i, (Real.sqrt (2 * Real.pi) * (value i : ℝ) / width) ^ 2) =
      (2 * Real.pi / width ^ 2) * ∑ i, (value i : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    ring
  have hl : (∑ i, Real.sqrt (2 * Real.pi) * (value i : ℝ) / width) =
      Real.sqrt (2 * Real.pi) / width * ∑ i, (value i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, hl, mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  unfold rootExponent
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

/-- The Gaussian density relative to its own one-coordinate marginal is
exactly a scalar times `exp Q`; no approximation occurs in this algebra. -/
theorem sumModel_root_ratio (width normalization : ℝ) (population order : ℕ)
    (hp : order < population) (ho : 0 < order) (value : Fin order → ℤ) :
    sumModel width normalization (population - order) (-∑ i, value i) *
        sumModel width normalization population 0 ^ (order - 1) /
        (∏ i, sumModel width normalization (population - 1) (-value i)) =
      rootModelPrefactor width normalization population order *
        Real.exp (rootExponent width population value) := by
  have hn1 : 1 ≤ population := by omega
  have hnk : order ≤ population := hp.le
  have hsum : ((∑ i, value i : ℤ) : ℝ) = ∑ i, (value i : ℝ) := by push_cast; rfl
  have hmodel (count : ℕ) (t : ℤ) : sumModel width normalization count t =
      sumAmplitude width normalization count * Real.exp (-Real.pi * (t : ℝ) ^ 2 /
        ((count : ℝ) * width ^ 2)) := rfl
  simp_rw [hmodel]
  simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, Real.exp_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  simp only [Int.cast_neg, neg_sq]
  rw [hsum]
  have hexp : Real.exp (-Real.pi * (∑ i, (value i : ℝ)) ^ 2 /
        (((population - order : ℕ) : ℝ) * width ^ 2)) /
      Real.exp (∑ i, -Real.pi * (value i : ℝ) ^ 2 / (((population - 1 : ℕ) : ℝ) * width ^ 2)) =
      Real.exp (rootExponent width population value) := by
    rw [← Real.exp_sub]
    congr 1
    rw [Nat.cast_sub hnk, Nat.cast_sub hn1]
    simp only [Nat.cast_one]
    unfold rootExponent
    rw [Fintype.card_fin]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold rootModelPrefactor
  calc
    _ = (sumAmplitude width normalization (population - order) *
          sumAmplitude width normalization population ^ (order - 1) /
          sumAmplitude width normalization (population - 1) ^ order) *
        (Real.exp (-Real.pi * (∑ i, (value i : ℝ)) ^ 2 /
          (((population - order : ℕ) : ℝ) * width ^ 2)) /
        Real.exp (∑ i, -Real.pi * (value i : ℝ) ^ 2 / (((population - 1 : ℕ) : ℝ) * width ^ 2))) := by ring
    _ = _ := by rw [hexp]

/-- Exact cancellation of the source normalizer and the scalar width. -/
theorem rootModelPrefactor_eq (width normalization : ℝ) (population order : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (hp : order < population) (ho : 0 < order) :
    rootModelPrefactor width normalization population order =
      Real.sqrt ((population - 1 : ℕ) : ℝ) ^ order /
        (Real.sqrt ((population - order : ℕ) : ℝ) * Real.sqrt (population : ℝ) ^ (order - 1)) := by
  have hn1 : 1 ≤ population := by omega
  have hk1 : 1 ≤ order := ho
  have hmulN : population ≤ population * order := by
    calc
      population = population * 1 := by omega
      _ ≤ population * order := Nat.mul_le_mul_left population hk1
  have hmulK : order ≤ population * order := by
    calc
      order = 1 * order := by omega
      _ ≤ population * order := Nat.mul_le_mul_right order hn1
  have hbalance : (population - order) + population * (order - 1) = (population - 1) * order := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_mul]
    simp only [Nat.mul_one, Nat.one_mul]
    omega
  have hrate : width / normalization ≠ 0 := (div_pos hw hz).ne'
  have hpow : (width / normalization) ^ (population - order) *
      ((width / normalization) ^ population) ^ (order - 1) =
      ((width / normalization) ^ (population - 1)) ^ order := by
    rw [← pow_mul, ← pow_add, hbalance, pow_mul]
  have hNp : 0 < Real.sqrt (population : ℝ) := by positivity
  have hNkp : 0 < Real.sqrt ((population - order : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.sub_pos_of_lt hp
  have hN1p : 0 < Real.sqrt ((population - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (by omega : 0 < population - 1)
  unfold rootModelPrefactor sumAmplitude
  generalize hrateDef : width / normalization = rate at hpow hrate ⊢
  simp only [div_pow, mul_pow]
  have hwPow : width * width ^ (order - 1) = width ^ order := by
    rw [← pow_succ', Nat.sub_add_cancel hk1]
  have hfrac :
      rate ^ (population - order) /
          (Real.sqrt ((population - order : ℕ) : ℝ) * width) *
        ((rate ^ population) ^ (order - 1) /
          (Real.sqrt (population : ℝ) ^ (order - 1) * width ^ (order - 1))) /
        ((rate ^ (population - 1)) ^ order /
          (Real.sqrt ((population - 1 : ℕ) : ℝ) ^ order * width ^ order)) =
      (rate ^ (population - order) *
        (rate ^ population) ^ (order - 1)) /
        (rate ^ (population - 1)) ^ order *
      (Real.sqrt ((population - 1 : ℕ) : ℝ) ^ order /
        (Real.sqrt ((population - order : ℕ) : ℝ) * Real.sqrt (population : ℝ) ^ (order - 1))) *
      (width ^ order / (width * width ^ (order - 1))) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hfrac, hpow, div_self (pow_ne_zero _ (pow_ne_zero _ hrate)), one_mul,
    hwPow, div_self (pow_ne_zero _ hw.ne'), mul_one]

/-- The scalar prefactor is uniformly bounded for retained order at most
half the root population. -/
theorem rootModelPrefactor_le_sqrt_two (width normalization : ℝ) (population order : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (ho : 0 < order)
    (hhalf : 2 * order ≤ population) :
    rootModelPrefactor width normalization population order ≤ Real.sqrt 2 := by
  have hp : order < population := by omega
  have hpop : 0 < (population : ℝ) := by exact_mod_cast (by omega : 0 < population)
  have hrem : 0 < ((population - order : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hp
  rw [rootModelPrefactor_eq width normalization population order hw hz hp ho]
  have hsq1 : Real.sqrt ((population - 1 : ℕ) : ℝ) ≤ Real.sqrt (population : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le population 1)
  have hpower := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq1 order
  have hden : 0 < Real.sqrt ((population - order : ℕ) : ℝ) * Real.sqrt (population : ℝ) ^ (order - 1) := by positivity
  have hpowN : Real.sqrt (population : ℝ) ^ order =
      Real.sqrt (population : ℝ) * Real.sqrt (population : ℝ) ^ (order - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ho]
  calc
    _ ≤ Real.sqrt (population : ℝ) ^ order /
        (Real.sqrt ((population - order : ℕ) : ℝ) * Real.sqrt (population : ℝ) ^ (order - 1)) :=
      div_le_div_of_nonneg_right hpower hden.le
    _ = Real.sqrt (population : ℝ) / Real.sqrt ((population - order : ℕ) : ℝ) := by
      rw [hpowN]
      field_simp
    _ ≤ Real.sqrt 2 := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hrem)).mpr
      have hreal : (population : ℝ) ≤ 2 * ((population - order : ℕ) : ℝ) := by
        exact_mod_cast (by omega : population ≤ 2 * (population - order))
      have hsqrt := Real.sqrt_le_sqrt hreal
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hsqrt
      exact hsqrt

/-- Propagation of relative errors through a quotient of two equal-size
products. The bound keeps the exact finite degree. -/
theorem product_quotient_relative_bounds {ι : Type*} [Fintype ι]
    (numerator denominator modelNumerator modelDenominator : ι → ℝ) (error : ℝ)
    (he0 : 0 ≤ error) (he1 : error < 1)
    (hmn : ∀ i, 0 < modelNumerator i) (hmd : ∀ i, 0 < modelDenominator i)
    (hn : ∀ i, |numerator i / modelNumerator i - 1| ≤ error)
    (hd : ∀ i, |denominator i / modelDenominator i - 1| ≤ error) :
    (1 - error) ^ Fintype.card ι / (1 + error) ^ Fintype.card ι ≤
      ((∏ i, numerator i) / (∏ i, denominator i)) /
        ((∏ i, modelNumerator i) / (∏ i, modelDenominator i)) ∧
    ((∏ i, numerator i) / (∏ i, denominator i)) /
        ((∏ i, modelNumerator i) / (∏ i, modelDenominator i)) ≤
      (1 + error) ^ Fintype.card ι / (1 - error) ^ Fintype.card ι := by
  have hnL (i : ι) : 1 - error ≤ numerator i / modelNumerator i := by
    have h := (abs_le.mp (hn i)).1
    linarith
  have hnU (i : ι) : numerator i / modelNumerator i ≤ 1 + error := by
    have h := (abs_le.mp (hn i)).2
    linarith
  have hdL (i : ι) : 1 - error ≤ denominator i / modelDenominator i := by
    have h := (abs_le.mp (hd i)).1
    linarith
  have hdU (i : ι) : denominator i / modelDenominator i ≤ 1 + error := by
    have h := (abs_le.mp (hd i)).2
    linarith
  have hl : 0 < 1 - error := by linarith
  have hu : 0 < 1 + error := by linarith
  have hn0 (i : ι) : 0 < numerator i / modelNumerator i := hl.trans_le (hnL i)
  have hd0 (i : ι) : 0 < denominator i / modelDenominator i := hl.trans_le (hdL i)
  have hNP : (1 - error) ^ Fintype.card ι ≤ ∏ i, numerator i / modelNumerator i := by
    simpa using Finset.prod_le_prod (fun _ _ => hl.le) (fun i _ => hnL i)
  have hNU : (∏ i, numerator i / modelNumerator i) ≤ (1 + error) ^ Fintype.card ι := by
    simpa using Finset.prod_le_prod (fun i _ => (hn0 i).le) (fun i _ => hnU i)
  have hDP : (1 - error) ^ Fintype.card ι ≤ ∏ i, denominator i / modelDenominator i := by
    simpa using Finset.prod_le_prod (fun _ _ => hl.le) (fun i _ => hdL i)
  have hDU : (∏ i, denominator i / modelDenominator i) ≤ (1 + error) ^ Fintype.card ι := by
    simpa using Finset.prod_le_prod (fun i _ => (hd0 i).le) (fun i _ => hdU i)
  have hDP0 : 0 < ∏ i, denominator i / modelDenominator i := Finset.prod_pos (fun i _ => hd0 i)
  have hmn0 : (∏ i, modelNumerator i) ≠ 0 := (Finset.prod_pos (fun i _ => hmn i)).ne'
  have hmd0 : (∏ i, modelDenominator i) ≠ 0 := (Finset.prod_pos (fun i _ => hmd i)).ne'
  have hden (i : ι) : 0 < denominator i := (div_pos_iff.mp (hd0 i)).resolve_right
    (by intro h; exact (not_lt_of_gt (hmd i)) h.2) |>.1
  have hden0 : (∏ i, denominator i) ≠ 0 := (Finset.prod_pos (fun i _ => hden i)).ne'
  have heq : ((∏ i, numerator i) / (∏ i, denominator i)) /
      ((∏ i, modelNumerator i) / (∏ i, modelDenominator i)) =
      (∏ i, numerator i / modelNumerator i) / (∏ i, denominator i / modelDenominator i) := by
    simp only [Finset.prod_div_distrib]
    field_simp
  rw [heq]
  constructor
  · calc
      _ ≤ (1 - error) ^ Fintype.card ι / (∏ i, denominator i / modelDenominator i) :=
        div_le_div_of_nonneg_left (pow_pos hl _).le hDP0 hDU
      _ ≤ _ := div_le_div_of_nonneg_right hNP hDP0.le
  · calc
      _ ≤ (1 + error) ^ Fintype.card ι / (∏ i, denominator i / modelDenominator i) :=
        div_le_div_of_nonneg_right hNU hDP0.le
      _ ≤ _ := div_le_div_of_nonneg_left (pow_pos hu _).le (pow_pos hl _) hDP

noncomputable def ratioError (error : ℝ) (order : ℕ) : ℝ :=
  (1 + error) ^ order / (1 - error) ^ order - (1 - error) ^ order / (1 + error) ^ order

theorem product_quotient_relative_error {ι : Type*} [Fintype ι]
    (numerator denominator modelNumerator modelDenominator : ι → ℝ) (error : ℝ)
    (he0 : 0 ≤ error) (he1 : error < 1)
    (hmn : ∀ i, 0 < modelNumerator i) (hmd : ∀ i, 0 < modelDenominator i)
    (hn : ∀ i, |numerator i / modelNumerator i - 1| ≤ error)
    (hd : ∀ i, |denominator i / modelDenominator i - 1| ≤ error) :
    |((∏ i, numerator i) / (∏ i, denominator i)) /
        ((∏ i, modelNumerator i) / (∏ i, modelDenominator i)) - 1| ≤
      ratioError error (Fintype.card ι) := by
  have hb := product_quotient_relative_bounds numerator denominator modelNumerator modelDenominator
    error he0 he1 hmn hmd hn hd
  have hl : 0 < 1 - error := by linarith
  have hu : 0 < 1 + error := by linarith
  have hp : (1 - error) ^ Fintype.card ι ≤ (1 + error) ^ Fintype.card ι :=
    pow_le_pow_left₀ hl.le (by linarith) _
  have hL : (1 - error) ^ Fintype.card ι / (1 + error) ^ Fintype.card ι ≤ 1 :=
    (div_le_one (pow_pos hu _)).mpr hp
  have hU : 1 ≤ (1 + error) ^ Fintype.card ι / (1 - error) ^ Fintype.card ι :=
    (le_div_iff₀ (pow_pos hl _)).mpr (by simpa using hp)
  unfold ratioError
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

end AFT.GaussianSource

import AFT.GaussianConvolution
import AFT.ClippedSource

/-!
# Finite clipped Gaussian sum probabilities

This file relates the actual finite root sum to integer convolutions, with
an explicit clipping defect and the uniform theta error from Poisson summation.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

/-- Actual convolution powers on the integer lattice; `count` is the number
of independent summands. -/
noncomputable def convolutionPower (mass : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun target => if target = 0 then 1 else 0
  | n + 1 => fun target => ∑' z : ℤ, mass z * convolutionPower mass n (target - z)

theorem convolutionPower_nonneg (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z)
    (count : ℕ) (target : ℤ) : 0 ≤ convolutionPower mass count target := by
  induction count generalizing target with
  | zero => simp only [convolutionPower]; split_ifs <;> norm_num
  | succ n ih => exact tsum_nonneg (fun z => mul_nonneg (hm z) (ih _))

/-- Every convolution of a subprobability mass is again pointwise at most one. -/
theorem convolutionPower_le_one (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z)
    (hs : Summable mass) (h1 : (∑' z, mass z) ≤ 1) (count : ℕ) (target : ℤ) :
    convolutionPower mass count target ≤ 1 := by
  induction count generalizing target with
  | zero => simp only [convolutionPower]; split_ifs <;> norm_num
  | succ n ih =>
    have hpoint (z : ℤ) : mass z * convolutionPower mass n (target - z) ≤ mass z := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ih (target - z)) (hm z)
    have hs' : Summable (fun z : ℤ => mass z * convolutionPower mass n (target - z)) :=
      Summable.of_nonneg_of_le
        (fun z => mul_nonneg (hm z) (convolutionPower_nonneg mass hm n _)) hpoint hs
    exact (hs'.tsum_le_tsum hpoint hs).trans h1

theorem summable_power_integrand (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z)
    (hs : Summable mass) (h1 : (∑' z, mass z) ≤ 1) (count : ℕ) (target : ℤ) :
    Summable (fun z : ℤ => mass z * convolutionPower mass count (target - z)) := by
  apply Summable.of_nonneg_of_le
    (fun z => mul_nonneg (hm z) (convolutionPower_nonneg mass hm count _)) _ hs
  intro z
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (convolutionPower_le_one mass hm hs h1 count _) (hm z)

/-- Deleting total one-coordinate mass `defect` changes every `count`-fold
sum probability by at most `count * defect`. This is a pointwise bound on
actual integer convolution masses. -/
theorem convolutionPower_deletion (mass retained : ℤ → ℝ)
    (hm : ∀ z, 0 ≤ mass z) (hr : ∀ z, 0 ≤ retained z)
    (hle : ∀ z, retained z ≤ mass z) (hs : Summable mass)
    (h1 : (∑' z, mass z) ≤ 1) (count : ℕ) (target : ℤ) :
    0 ≤ convolutionPower mass count target - convolutionPower retained count target ∧
    convolutionPower mass count target - convolutionPower retained count target ≤
      count * ∑' z : ℤ, (mass z - retained z) := by
  have hrs : Summable retained := Summable.of_nonneg_of_le hr hle hs
  have hr1 : (∑' z, retained z) ≤ 1 := (hrs.tsum_le_tsum hle hs).trans h1
  let defect := ∑' z : ℤ, (mass z - retained z)
  have hd : 0 ≤ defect := tsum_nonneg (fun z => sub_nonneg.mpr (hle z))
  induction count generalizing target with
  | zero => simp [convolutionPower]
  | succ count ih =>
    have hms := summable_power_integrand mass hm hs h1 count target
    have hqs := summable_power_integrand retained hr hrs hr1 count target
    have hpoint0 (z : ℤ) : 0 ≤ mass z * convolutionPower mass count (target - z) -
        retained z * convolutionPower retained count (target - z) := by
      apply sub_nonneg.mpr
      exact mul_le_mul (hle z) (sub_nonneg.mp (ih _).1)
        (convolutionPower_nonneg retained hr count _) (hm z)
    have hpointU (z : ℤ) : mass z * convolutionPower mass count (target - z) -
        retained z * convolutionPower retained count (target - z) ≤
        (mass z - retained z) + retained z * ((count : ℝ) * defect) := by
      have hp := convolutionPower_le_one mass hm hs h1 count (target - z)
      have hA := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr (hle z))
      have hB := mul_le_mul_of_nonneg_left (ih (target - z)).2 (hr z)
      change _ ≤ (mass z - retained z) + retained z * ((count : ℝ) * defect)
      change _ ≤ retained z * ((count : ℝ) * defect) at hB
      nlinarith
    have hupper := (hms.sub hqs).tsum_le_tsum hpointU
      ((hs.sub hrs).add (hrs.mul_right ((count : ℝ) * defect)))
    rw [Summable.tsum_sub hms hqs, Summable.tsum_add (hs.sub hrs)
      (hrs.mul_right ((count : ℝ) * defect)), tsum_mul_right] at hupper
    constructor
    · rw [convolutionPower, convolutionPower, ← Summable.tsum_sub hms hqs]
      exact tsum_nonneg hpoint0
    · change (∑' z : ℤ, mass z * convolutionPower mass count (target - z)) -
        (∑' z : ℤ, retained z * convolutionPower retained count (target - z)) ≤ _
      apply hupper.trans
      change defect + (∑' z : ℤ, retained z) * ((count : ℝ) * defect) ≤ (count + 1 : ℕ) * defect
      have hh := mul_le_mul_of_nonneg_right hr1 (mul_nonneg (Nat.cast_nonneg count) hd)
      push_cast
      nlinarith

/-- Scalar normalization commutes exactly with each finite convolution power. -/
theorem convolutionPower_scale (mass : ℤ → ℝ) (scale : ℝ) (count : ℕ) (target : ℤ) :
    convolutionPower (fun z => scale * mass z) count target =
      scale ^ count * convolutionPower mass count target := by
  induction count generalizing target with
  | zero => simp [convolutionPower]
  | succ count ih =>
    simp only [convolutionPower, ih]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [pow_succ]
    ring

theorem integer_convolution_comm (first second : ℤ → ℝ) (target : ℤ) :
    (∑' z : ℤ, first z * second (target - z)) =
      ∑' z : ℤ, second z * first (target - z) := by
  have h := (Equiv.subLeft target).tsum_eq (fun z => first z * second (target - z))
  change (∑' z : ℤ, first (target - z) * second (target - (target - z))) = _ at h
  simpa only [sub_sub_cancel, mul_comm] using h.symm

theorem convolutionPower_one (mass : ℤ → ℝ) (target : ℤ) :
    convolutionPower mass 1 target = mass target := by
  unfold convolutionPower
  rw [tsum_eq_single target]
  · simp [convolutionPower]
  · intro z hz
    have h : target - z ≠ 0 := by omega
    simp [convolutionPower, h]

theorem convolutionPower_kernel (width : ℝ) (merges : ℕ) (target : ℤ) :
    convolutionPower (gaussianKernel width) (merges + 1) target = kernelPower width merges target := by
  induction merges generalizing target with
  | zero => exact convolutionPower_one _ _
  | succ merges ih =>
    change (∑' z : ℤ, gaussianKernel width z * convolutionPower (gaussianKernel width)
      (merges + 1) (target - z)) =
      ∑' z : ℤ, kernelPower width merges z * gaussianKernel width (target - z)
    simp only [ih]
    exact integer_convolution_comm _ _ _

noncomputable def integerMass (width : ℝ) (z : ℤ) : ℝ := weight width z / realNormalizer width

theorem integerMass_eq_pmf (width : ℝ) (hw : 0 < width) (z : ℤ) :
    integerMass width z = (integerGaussian width hw z).toReal := (integerGaussian_toReal width hw z).symm

theorem integerMass_nonneg (width : ℝ) (hw : 0 < width) (z : ℤ) : 0 ≤ integerMass width z :=
  div_nonneg (weight_pos width z).le (le_trans zero_le_one (realNormalizer_ge_one width hw))

theorem summable_integerMass (width : ℝ) (hw : 0 < width) : Summable (integerMass width) :=
  (summable_weight width hw).div_const _

theorem integerMass_sum (width : ℝ) (hw : 0 < width) : (∑' z : ℤ, integerMass width z) = 1 := by
  unfold integerMass
  rw [tsum_div_const]
  exact div_self (lt_of_lt_of_le zero_lt_one (realNormalizer_ge_one width hw)).ne'

/-- The infinite probability convolution is exactly the kernel analyzed
by Poisson summation, including every normalizing factor. -/
theorem convolutionPower_integerMass (width : ℝ) (hw : 0 < width) (merges : ℕ) (target : ℤ) :
    convolutionPower (integerMass width) (merges + 1) target =
      (width / realNormalizer width) ^ (merges + 1) * kernelPower width merges target := by
  have hm : integerMass width = fun z => (width / realNormalizer width) * gaussianKernel width z := by
    funext z
    unfold integerMass gaussianKernel
    field_simp
  rw [hm, convolutionPower_scale, convolutionPower_kernel]

/-- A finite unnormalized integer-window sum. -/
noncomputable def windowSum (mass : ℤ → ℝ) (cutoff count : ℕ) (target : ℤ) : ℝ :=
  ∑ x : Fin count → Window cutoff,
    if (∑ i, (x i : ℤ)) = target then ∏ i, mass (x i) else 0

/-- The finite recurrence is derived by splitting the first coordinate. -/
theorem windowSum_succ (mass : ℤ → ℝ) (cutoff count : ℕ) (target : ℤ) :
    windowSum mass cutoff (count + 1) target =
      ∑ head : Window cutoff, mass head * windowSum mass cutoff count (target - head) := by
  unfold windowSum
  rw [← (Fin.consEquiv (fun _ : Fin (count + 1) => Window cutoff)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro head _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have h : (head : ℤ) + (∑ i, (tail i : ℤ)) = target ↔
      (∑ i, (tail i : ℤ)) = target - head := by omega
  simp only [h]
  split_ifs <;> simp

noncomputable def restrictWindow (mass : ℤ → ℝ) (cutoff : ℕ) (z : ℤ) : ℝ :=
  if z ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then mass z else 0

/-- The infinite convolution of the window restriction equals exactly the
finite sum on the actual clipped alphabet. -/
theorem convolutionPower_restrictWindow (mass : ℤ → ℝ) (cutoff count : ℕ) (target : ℤ) :
    convolutionPower (restrictWindow mass cutoff) count target = windowSum mass cutoff count target := by
  induction count generalizing target with
  | zero => simp [convolutionPower, windowSum, eq_comm]
  | succ count ih =>
    rw [convolutionPower, windowSum_succ]
    simp_rw [ih]
    rw [tsum_eq_sum (s := Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
      (fun z hz => by simp [restrictWindow, hz])]
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro z _
    unfold restrictWindow
    split_ifs with hz
    · rfl
    · exact False.elim (hz z.property)

/-- Exact link to the root event probability of the finite clipped source. -/
theorem window_root_probability_eq (width : ℝ) (cutoff count : ℕ) (target : ℤ) :
    RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
      (fun z => (z : ℤ)) target =
      windowSum (weight width) cutoff count target / windowNormalizer width cutoff ^ count := by
  unfold RootSlice.probability FiniteDist.eventMass RootSlice.integerSum windowSum
  rw [Finset.sum_div]
  dsimp only [FiniteDist.independent]
  apply Finset.sum_congr (by ext; simp)
  intro x _
  by_cases hx : (∑ i, (x i : ℤ)) = target
  · simp only [windowGaussian, FiniteDist.normalize, if_pos hx,
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  · simp only [if_neg hx, zero_div]

theorem windowSum_scale (mass : ℤ → ℝ) (scale : ℝ) (cutoff count : ℕ) (target : ℤ) :
    windowSum (fun z => scale * mass z) cutoff count target =
      scale ^ count * windowSum mass cutoff count target := by
  unfold windowSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · rw [Finset.prod_mul_distrib]
    simp
  · simp

noncomputable def retainedFraction (width : ℝ) (cutoff : ℕ) : ℝ :=
  windowNormalizer width cutoff / realNormalizer width

theorem retainedFraction_pos (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    0 < retainedFraction width cutoff :=
  div_pos (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff))
    (zero_lt_one.trans_le (realNormalizer_ge_one width hw))

theorem retainedFraction_le_one (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    retainedFraction width cutoff ≤ 1 := by
  apply (div_le_one (zero_lt_one.trans_le (realNormalizer_ge_one width hw))).mpr
  exact windowNormalizer_le_real width cutoff hw

theorem restrictWindow_sum (width : ℝ) (cutoff : ℕ) :
    (∑' z : ℤ, restrictWindow (integerMass width) cutoff z) = retainedFraction width cutoff := by
  rw [tsum_eq_sum (s := Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
    (fun z hz => by simp [restrictWindow, hz]), ← Finset.sum_coe_sort]
  have heq (z : Window cutoff) : restrictWindow (integerMass width) cutoff z = integerMass width z := by
    unfold restrictWindow
    split_ifs with hz
    · rfl
    · exact False.elim (hz z.property)
  simp_rw [heq]
  unfold integerMass retainedFraction windowNormalizer
  rw [Finset.sum_div]

theorem restrictWindow_nonneg (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z) (cutoff : ℕ) (z : ℤ) :
    0 ≤ restrictWindow mass cutoff z := by unfold restrictWindow; split_ifs; exact hm z; rfl

theorem restrictWindow_le (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z) (cutoff : ℕ) (z : ℤ) :
    restrictWindow mass cutoff z ≤ mass z := by unfold restrictWindow; split_ifs; rfl; exact hm z

theorem removedWindow_mass (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    (∑' z : ℤ, (integerMass width z - restrictWindow (integerMass width) cutoff z)) =
      1 - retainedFraction width cutoff := by
  have hs := summable_integerMass width hw
  have hr := Summable.of_nonneg_of_le (restrictWindow_nonneg _ (integerMass_nonneg width hw) cutoff)
    (restrictWindow_le _ (integerMass_nonneg width hw) cutoff) hs
  rw [Summable.tsum_sub hs hr, integerMass_sum width hw, restrictWindow_sum]

/-- The normalizing correction between the actual clipped root event and
the unnormalized retained infinite source is exact. -/
theorem window_root_retained_eq (width : ℝ) (cutoff count : ℕ) (target : ℤ) :
    RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
      (fun z => (z : ℤ)) target * retainedFraction width cutoff ^ count =
      convolutionPower (restrictWindow (integerMass width) cutoff) count target := by
  rw [window_root_probability_eq, convolutionPower_restrictWindow]
  have heq : integerMass width = fun z => (realNormalizer width)⁻¹ * weight width z := by
    funext z
    unfold integerMass
    ring
  rw [heq, windowSum_scale]
  unfold retainedFraction
  rw [div_pow]
  have hwindow := (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff)).ne'
  simp only [inv_pow]
  field_simp

theorem finite_eventMass_le_one {α : Type*} [Fintype α] (p : FiniteDist α) (event : α → Prop) :
    p.eventMass event ≤ 1 := by
  unfold FiniteDist.eventMass
  calc
    (∑ x, if event x then p.weight x else 0) ≤ ∑ x, p.weight x := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs
      · rfl
      · exact p.nonneg x
    _ = 1 := p.sum_one

theorem window_root_probability_le_one (width : ℝ) (cutoff count : ℕ) (target : ℤ) :
    RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
      (fun z => (z : ℤ)) target ≤ 1 := by
  classical
  unfold RootSlice.probability
  exact @finite_eventMass_le_one _
    (@Pi.instFintype (Fin count) (fun _ => Window cutoff)
      (fun a b => Classical.propDecidable (a = b)) (Fin.fintype count) (fun _ => inferInstance)) _ _

/-- Bernoulli's inequality in the form needed for normalization loss. -/
theorem one_sub_power_le (retention : ℝ) (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1) (count : ℕ) :
    1 - retention ^ count ≤ count * (1 - retention) := by
  induction count with
  | zero => simp
  | succ count ih =>
    have hp := pow_le_one₀ (n := count) hr0 hr1
    have hh := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hr1)
    rw [pow_succ]
    push_cast
    nlinarith

/-- Clipping and renormalizing each coordinate changes every finite sum
probability by at most `count` times the actual removed one-coordinate mass. -/
theorem window_root_clipping_error (width : ℝ) (cutoff count : ℕ) (hw : 0 < width) (target : ℤ) :
    |RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
        (fun z => (z : ℤ)) target - convolutionPower (integerMass width) count target| ≤
      count * (1 - retainedFraction width cutoff) := by
  have hm := integerMass_nonneg width hw
  have hdel := convolutionPower_deletion (integerMass width) (restrictWindow (integerMass width) cutoff)
    hm (restrictWindow_nonneg _ hm cutoff) (restrictWindow_le _ hm cutoff)
    (summable_integerMass width hw) (le_of_eq (integerMass_sum width hw)) count target
  rw [removedWindow_mass width cutoff hw, ← window_root_retained_eq width cutoff count target] at hdel
  have hr0 := (retainedFraction_pos width cutoff hw).le
  have hr1 := retainedFraction_le_one width cutoff hw
  have hp0 : 0 ≤ RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
      (fun z => (z : ℤ)) target := by
    classical
    unfold RootSlice.probability
    exact @FiniteDist.eventMass_nonneg _
      (@Pi.instFintype (Fin count) (fun _ => Window cutoff)
        (fun a b => Classical.propDecidable (a = b)) (Fin.fintype count) (fun _ => inferInstance)) _ _
  have hp1 := window_root_probability_le_one width cutoff count target
  have hpow := pow_le_one₀ (n := count) hr0 hr1
  have hloss := one_sub_power_le (retainedFraction width cutoff) hr0 hr1 count
  have hmul := mul_le_mul_of_nonneg_left hloss hp0
  have hlast := mul_le_mul_of_nonneg_right hp1
    (mul_nonneg (Nat.cast_nonneg count) (sub_nonneg.mpr hr1))
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The removed window mass is bounded by the genuine Gaussian tail. -/
theorem removedWindow_le_clippingProbability (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    1 - retainedFraction width cutoff ≤ clippingProbability width cutoff hw := by
  rw [← removedWindow_mass width cutoff hw, clippingProbability_eq]
  have hs := summable_integerMass width hw
  have hr := Summable.of_nonneg_of_le (restrictWindow_nonneg _ (integerMass_nonneg width hw) cutoff)
    (restrictWindow_le _ (integerMass_nonneg width hw) cutoff) hs
  have htail := (summable_clippingMass width cutoff hw).div_const (realNormalizer width)
  unfold clippingMass
  rw [← tsum_div_const]
  apply (hs.sub hr).tsum_le_tsum _ htail
  intro z
  unfold restrictWindow
  by_cases hz : z ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · simp only [if_pos hz, sub_self]
    apply div_nonneg
    · split_ifs
      · exact (weight_pos width z).le
      · rfl
    · exact zero_le_one.trans (realNormalizer_ge_one width hw)
  · have hcut : (cutoff : ℝ) ≤ |(z : ℝ)| := by
      by_contra hh
      have habs : |(z : ℝ)| < (cutoff : ℝ) := lt_of_not_ge hh
      have hz' := abs_lt.mp habs
      have hzl : -(cutoff : ℤ) ≤ z := by exact_mod_cast hz'.1.le
      have hzu : z ≤ (cutoff : ℤ) := by exact_mod_cast hz'.2.le
      exact hz (Finset.mem_Icc.mpr ⟨hzl, hzu⟩)
    simp only [if_neg hz, if_pos hcut, sub_zero, integerMass, le_refl]

/-- A fully explicit finite clipped-root error bound. -/
theorem window_root_clipping_error_exp (width : ℝ) (cutoff count : ℕ) (hw : 0 < width)
    (target : ℤ) :
    |RootSlice.probability (fun _ : Fin count => windowGaussian width cutoff)
        (fun z => (z : ℤ)) target - convolutionPower (integerMass width) count target| ≤
      count * (Real.exp (-Real.pi * (cutoff : ℝ) ^ 2 / (2 * width ^ 2)) *
        (1 + 4 * width ^ 2 / Real.pi)) := by
  apply (window_root_clipping_error width cutoff count hw target).trans
  exact mul_le_mul_of_nonneg_left ((removedWindow_le_clippingProbability width cutoff hw).trans
    (clippingProbability_le width cutoff hw (Nat.cast_nonneg cutoff))) (Nat.cast_nonneg count)

/-- The exact continuum comparison, retaining the lattice normalizer.
Keeping this scalar is useful because it cancels from marginal-density ratios. -/
noncomputable def gaussianSumApprox (width : ℝ) (merges : ℕ) (target : ℤ) : ℝ :=
  (width / realNormalizer width) ^ (merges + 1) * gaussianKernel (powerWidth width merges) target

noncomputable def clippingError (width : ℝ) (cutoff count : ℕ) : ℝ :=
  count * (Real.exp (-Real.pi * (cutoff : ℝ) ^ 2 / (2 * width ^ 2)) *
    (1 + 4 * width ^ 2 / Real.pi))

theorem gaussianSumApprox_pos (width : ℝ) (hw : 0 < width) (merges : ℕ) (target : ℤ) :
    0 < gaussianSumApprox width merges target :=
  mul_pos (pow_pos (div_pos hw (zero_lt_one.trans_le (realNormalizer_ge_one width hw))) _)
    (gaussianKernel_pos _ (powerWidth_pos width hw merges) target)

theorem clippingError_nonneg (width : ℝ) (cutoff count : ℕ) : 0 ≤ clippingError width cutoff count := by
  unfold clippingError
  positivity

/-- A finite-parameter, two-sided Gaussian approximation for the actual
clipped integer root event. Every error term has been proved from the source. -/
theorem window_root_gaussian_bounds (width error : ℝ) (cutoff merges : ℕ)
    (hw : 0 < width) (he0 : 0 ≤ error) (he1 : error ≤ 1)
    (he : thetaError (width / Real.sqrt 2) ≤ error) (target : ℤ) :
    (1 - error) ^ merges * gaussianSumApprox width merges target -
      clippingError width cutoff (merges + 1) ≤
      RootSlice.probability (fun _ : Fin (merges + 1) => windowGaussian width cutoff)
        (fun z => (z : ℤ)) target ∧
    RootSlice.probability (fun _ : Fin (merges + 1) => windowGaussian width cutoff)
        (fun z => (z : ℤ)) target ≤
      (1 + error) ^ merges * gaussianSumApprox width merges target +
        clippingError width cutoff (merges + 1) := by
  have hk := kernelPower_bounds width error hw he0 he1 he merges target
  have hclip := abs_le.mp (window_root_clipping_error_exp width cutoff (merges + 1) hw target)
  have hscale : 0 ≤ (width / realNormalizer width) ^ (merges + 1) :=
    (pow_pos (div_pos hw (zero_lt_one.trans_le (realNormalizer_ge_one width hw))) _).le
  have hL := mul_le_mul_of_nonneg_left hk.1 hscale
  have hU := mul_le_mul_of_nonneg_left hk.2 hscale
  rw [convolutionPower_integerMass width hw] at hclip
  unfold gaussianSumApprox clippingError
  constructor <;> nlinarith [hclip.1, hclip.2]

/-- Explicit relative error for the finite clipped sum. -/
noncomputable def rootSumError (width error : ℝ) (cutoff merges : ℕ) (target : ℤ) : ℝ :=
  ((1 + error) ^ merges - 1) + (1 - (1 - error) ^ merges) +
    clippingError width cutoff (merges + 1) / gaussianSumApprox width merges target

theorem window_root_gaussian_relative_error (width error : ℝ) (cutoff merges : ℕ)
    (hw : 0 < width) (he0 : 0 ≤ error) (he1 : error ≤ 1)
    (he : thetaError (width / Real.sqrt 2) ≤ error) (target : ℤ) :
    |RootSlice.probability (fun _ : Fin (merges + 1) => windowGaussian width cutoff)
        (fun z => (z : ℤ)) target / gaussianSumApprox width merges target - 1| ≤
      rootSumError width error cutoff merges target := by
  have hb := window_root_gaussian_bounds width error cutoff merges hw he0 he1 he target
  have ha := gaussianSumApprox_pos width hw merges target
  have hlow : (1 - error) ^ merges ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hupp : 1 ≤ (1 + error) ^ merges := one_le_pow₀ (by linarith)
  unfold rootSumError
  apply abs_le.mpr
  constructor
  · have hquot : ((1 - error) ^ merges * gaussianSumApprox width merges target -
        clippingError width cutoff (merges + 1)) / gaussianSumApprox width merges target =
        (1 - error) ^ merges - clippingError width cutoff (merges + 1) /
          gaussianSumApprox width merges target := by field_simp
    have hdiv := div_le_div_of_nonneg_right hb.1 ha.le
    rw [hquot] at hdiv
    linarith
  · have hquot : ((1 + error) ^ merges * gaussianSumApprox width merges target +
        clippingError width cutoff (merges + 1)) / gaussianSumApprox width merges target =
        (1 + error) ^ merges + clippingError width cutoff (merges + 1) /
          gaussianSumApprox width merges target := by field_simp
    have hdiv := div_le_div_of_nonneg_right hb.2 ha.le
    rw [hquot] at hdiv
    linarith

/-- The comparison mass decreases with the absolute value of its center. -/
theorem gaussianSumApprox_antitone_abs (width : ℝ) (hw : 0 < width) (merges : ℕ)
    (first second : ℤ) (h : |(first : ℝ)| ≤ |(second : ℝ)|) :
    gaussianSumApprox width merges second ≤ gaussianSumApprox width merges first := by
  unfold gaussianSumApprox gaussianKernel weight
  apply mul_le_mul_of_nonneg_left _
    (pow_nonneg (div_nonneg hw.le (zero_le_one.trans (realNormalizer_ge_one width hw))) _)
  apply div_le_div_of_nonneg_right _ (powerWidth_pos width hw merges).le
  apply Real.exp_le_exp.mpr
  have hsq : (first : ℝ) ^ 2 ≤ (second : ℝ) ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (first : ℝ)) (abs_nonneg (second : ℝ))).mpr h
    simpa only [sq_abs] using hsq
  have hc : 0 ≤ Real.pi / powerWidth width merges ^ 2 := by positivity
  nlinarith

/-- One explicit error at the extreme center bounds all smaller centers. -/
theorem rootSumError_mono_abs (width error : ℝ) (hw : 0 < width) (cutoff merges : ℕ)
    (first second : ℤ) (h : |(first : ℝ)| ≤ |(second : ℝ)|) :
    rootSumError width error cutoff merges first ≤ rootSumError width error cutoff merges second := by
  unfold rootSumError
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (clippingError_nonneg width cutoff (merges + 1))
    (gaussianSumApprox_pos width hw merges second)
    (gaussianSumApprox_antitone_abs width hw merges first second h)

end AFT.GaussianSource

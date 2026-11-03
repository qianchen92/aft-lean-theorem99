import AFT.BodyTypeParameters

/-! # Actual shared-source body differences, uniformly in the queue shift -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem interval_palette_translation_pair_l1_le (parameter : ℕ) (start firstShift secondShift : ℤ) (width : ℕ) :
    (∑ color : Fin (Parameters.modulus parameter),
      |intervalAnchorLaw start width ((color.val : ℤ) - firstShift) -
        intervalAnchorLaw start width ((color.val : ℤ) - secondShift)|) ≤
      2 * ((firstShift - secondShift).natAbs : ℝ) / width := by
  have hh := interval_palette_translation_l1_le parameter (start + secondShift) (firstShift - secondShift) width
  simp only [intervalAnchorLaw_translate] at hh
  have heq (color : Fin (Parameters.modulus parameter)) :
      (color.val : ℤ) - (firstShift - secondShift) - secondShift = (color.val : ℤ) - firstShift := by ring
  simpa only [heq] using hh

theorem publicAnchorKernel_translation_pair_l1 (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) (firstShift secondShift : ℤ) :
    (∑ output : Fin (Parameters.modulus parameter),
      |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - firstShift) -
        publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - secondShift)|) ≤
      2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.anchorWidth parameter := by
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - firstShift) -
        publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - secondShift)| ≤
      (|intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - firstShift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - secondShift)| +
      |intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - firstShift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - secondShift)|) / 2 := by
    unfold publicAnchorKernel
    have hh := abs_add_le
      (intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - firstShift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - secondShift))
      (intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - firstShift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - secondShift))
    have heq (a b c d : ℝ) : (a + b) / 2 - (c + d) / 2 = ((a - c) + (b - d)) / 2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hh (by norm_num)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun output _ => hpoint output)
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hh
  have h1 := interval_palette_translation_pair_l1_le parameter
    (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true) firstShift secondShift (Parameters.anchorWidth parameter)
  have h2 := interval_palette_translation_pair_l1_le parameter
    (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false) firstShift secondShift (Parameters.anchorWidth parameter)
  linarith

theorem anchorMean_translation_pair_l1 (parameter : ℕ) (primary : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ primary color) (hm : ∑ color, primary color = 1) (firstShift secondShift : ℤ) :
    (∑ output : Fin (Parameters.modulus parameter),
      |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - firstShift) -
        anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - secondShift)|) ≤
      2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.anchorWidth parameter := by
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - firstShift) -
        anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - secondShift)| ≤
      ∑ color, primary color *
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - firstShift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - secondShift)| := by
    unfold anchorMean
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_mul, abs_of_nonneg (hn _)])
  calc
    _ ≤ ∑ output : Fin (Parameters.modulus parameter), ∑ color, primary color *
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - firstShift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - secondShift)| :=
      Finset.sum_le_sum fun output _ => hpoint output
    _ = ∑ color, primary color * ∑ output : Fin (Parameters.modulus parameter),
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - firstShift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - secondShift)| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ color, primary color * (2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.anchorWidth parameter) := by
      exact Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (publicAnchorKernel_translation_pair_l1 parameter color firstShift secondShift) (hn color)
    _ = _ := by rw [← Finset.sum_mul, hm, one_mul]


theorem integerShiftProfile_abs_le (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    |integerShiftProfile parameter profile shift output| ≤ integerShiftProfile parameter (fun color => |profile color|) shift output := by
  unfold integerShiftProfile
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro color _
    split_ifs <;> simp only [abs_zero])

theorem rootProfileOperator_abs_le (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (output : Fin (Parameters.modulus parameter)) :
    |rootProfileOperator parameter profile output| ≤ rootProfileOperator parameter (fun color => |profile color|) output := by
  change |∑ root : Window (v7RootCutoff parameter), _ * _| ≤ ∑ root : Window (v7RootCutoff parameter), _ * _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro root _
  rw [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ root)]
  exact mul_le_mul_of_nonneg_left (integerShiftProfile_abs_le parameter profile root output) (FiniteDist.nonneg _ root)

theorem rootProfileOperator_l1_le (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ) :
    (∑ output, |rootProfileOperator parameter profile output|) ≤ ∑ color, |profile color| :=
  (Finset.sum_le_sum fun color _ => rootProfileOperator_abs_le parameter profile color).trans
    (rootProfileOperator_mass_le parameter (fun color => |profile color|) (fun _ => abs_nonneg _))

/-- Keeping the common queue shift cancels it exactly in the interval-edge
budget; only the difference of the two attachment sources is charged. -/
theorem actualBodyCenter_translation_pair_l1 (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hn : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualPrimary cutoffScale parameter beta color = 1)
    (hdelta : 0 ≤ bodyCompensation parameter cutoffScale) (firstShift secondShift : ℤ) :
    (∑ output, |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) firstShift output -
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) secondShift output|) ≤
      (1 + bodyCompensation parameter cutoffScale) * (2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.safeSize parameter) +
        bodyCompensation parameter cutoffScale * (2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.anchorWidth parameter) := by
  have heq : actualBodyCenter cutoffScale parameter beta =
      fun color => actualBodyIntegerProfile cutoffScale parameter beta color.val :=
    funext fun color => (actualBodyIntegerProfile_on_palette cutoffScale parameter beta color).symm
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) firstShift output -
        integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) secondShift output| ≤
      (1 + bodyCompensation parameter cutoffScale) *
        |coreIntegerProfile parameter ((output.val : ℤ) - firstShift) - coreIntegerProfile parameter ((output.val : ℤ) - secondShift)| +
      bodyCompensation parameter cutoffScale *
        |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) (actualPrimary cutoffScale parameter beta) ((output.val : ℤ) - firstShift) -
          anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) (actualPrimary cutoffScale parameter beta) ((output.val : ℤ) - secondShift)| := by
    rw [heq, integerShiftProfile_function parameter _ (actualBodyIntegerProfile_support cutoffScale parameter beta),
      integerShiftProfile_function parameter _ (actualBodyIntegerProfile_support cutoffScale parameter beta)]
    dsimp only [actualBodyIntegerProfile]
    have hid (a b c d e : ℝ) : (1 + e) * a - e * b - ((1 + e) * c - e * d) =
        (1 + e) * (a - c) - e * (b - d) := by ring
    rw [hid]
    exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hdelta, abs_of_nonneg (by linarith : 0 ≤ 1 + bodyCompensation parameter cutoffScale)])
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun output _ => hpoint output)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hc := interval_palette_translation_pair_l1_le parameter (Parameters.safeMargin parameter) firstShift secondShift (Parameters.safeSize parameter)
  have ha := anchorMean_translation_pair_l1 parameter (actualPrimary cutoffScale parameter beta) hn hm firstShift secondShift
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hc (by linarith)) (mul_le_mul_of_nonneg_left ha hdelta))

theorem actualBodyCenter_translation_pair_short_bound (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter)
    (hn : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualPrimary cutoffScale parameter beta color = 1) (firstShift secondShift : ℤ) :
    (∑ output, |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) firstShift output -
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) secondShift output|) ≤
      12 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.modulus parameter := by
  have hd := bodyCompensation_anchor_bound cutoffScale parameter hscale hp
  have hW : (0 : ℝ) < Parameters.safeSize parameter := by exact_mod_cast Parameters.safeSize_positive parameter
  have hA : (0 : ℝ) < Parameters.anchorWidth parameter := by
    simp only [Parameters.anchorWidth, Nat.cast_pow]
    have hh : (0 : ℝ) < Parameters.security parameter := by exact_mod_cast (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega)
    positivity
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hratio : bodyCompensation parameter cutoffScale / Parameters.anchorWidth parameter ≤ 1 / (Parameters.safeSize parameter : ℝ) :=
    (div_le_div_iff₀ hA hW).mpr (by simpa only [one_mul] using hd.2.2)
  have hWq : (Parameters.modulus parameter : ℝ) / 2 ≤ Parameters.safeSize parameter := by
    have hm := safeMargin_quarter parameter
    have hs := Parameters.safeSize_positive parameter
    have hnat : Parameters.modulus parameter ≤ 2 * Parameters.safeSize parameter := by unfold Parameters.safeSize at *; omega
    have hh : (Parameters.modulus parameter : ℝ) ≤ 2 * Parameters.safeSize parameter := by exact_mod_cast hnat
    linarith
  have hinv : 1 / (Parameters.safeSize parameter : ℝ) ≤ 2 / (Parameters.modulus parameter : ℝ) := by
    exact (div_le_div_iff₀ hW hq).mpr (by linarith)
  have hh := actualBodyCenter_translation_pair_l1 cutoffScale parameter beta hn hm hd.1 firstShift secondShift
  have hterm1 := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ 2 * ((firstShift - secondShift).natAbs : ℝ) / Parameters.safeSize parameter)
  have hterm2 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 * ((firstShift - secondShift).natAbs : ℝ))
  have hlast := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 6 * ((firstShift - secondShift).natAbs : ℝ))
  simp only [div_eq_mul_inv] at hh hterm1 hterm2 hlast ⊢
  nlinarith


theorem attachedBodyAtSource_nonneg (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hn : ∀ color, 0 ≤ actualBodyCenter cutoffScale parameter beta color)
    (queue source : ℤ) (output : Fin (Parameters.modulus parameter)) :
    0 ≤ attachedBodyAtSource cutoffScale parameter beta queue source output := by
  apply Finset.sum_nonneg
  intro root _
  exact mul_nonneg (FiniteDist.nonneg _ _) (integerShiftProfile_nonneg parameter _ hn _ output)

theorem attachedBodyAtSource_upper (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hbody : ∀ color, actualBodyCenter cutoffScale parameter beta color ≤ 2 * (actualCoreLaw parameter).weight color)
    (queue source : ℤ) (output : Fin (Parameters.modulus parameter)) :
    attachedBodyAtSource cutoffScale parameter beta queue source output ≤ 4 / (Parameters.modulus parameter : ℝ) := by
  unfold attachedBodyAtSource
  calc
    _ ≤ ∑ root : Window (v7RootCutoff parameter),
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)).weight root * (4 / (Parameters.modulus parameter : ℝ)) := by
      apply Finset.sum_le_sum
      intro root _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ root)
      apply integerShiftProfile_bound parameter _ _ (by positivity)
      intro color
      have hh := (actualCoreLaw_bounds parameter).1 color
      have hb := hbody color
      simp only [div_eq_mul_inv] at hh ⊢
      linarith
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem attachedBodyAtSource_mass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hm : ∑ color, actualBodyCenter cutoffScale parameter beta color = 1)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0)
    (queue source : ℤ) (hshift : |source + queue| + v7RootCutoff parameter ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ output, attachedBodyAtSource cutoffScale parameter beta queue source output) = 1 := by
  have hmass (root : Window (v7RootCutoff parameter)) :
      (∑ output, integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta)
        ((root : ℤ) + source + queue) output) = 1 := by
    rw [integerShiftProfile_mass parameter _ hs, hm]
    have hr := abs_le.mpr (Finset.mem_Icc.mp root.property)
    have hh := abs_add_le (root : ℤ) (source + queue)
    rw [← add_assoc] at hh
    omega
  unfold attachedBodyAtSource
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hmass, mul_one]
  exact FiniteDist.sum_one _

theorem attachedBodyAtSource_difference_l1 (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter)
    (hn : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualPrimary cutoffScale parameter beta color = 1)
    (queue firstSource secondSource : ℤ) :
    (∑ output, |attachedBodyAtSource cutoffScale parameter beta queue firstSource output -
      attachedBodyAtSource cutoffScale parameter beta queue secondSource output|) ≤
        12 * ((firstSource - secondSource).natAbs : ℝ) / Parameters.modulus parameter := by
  let rootLaw := rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)
  let difference (root : Window (v7RootCutoff parameter)) (output : Fin (Parameters.modulus parameter)) :=
    integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) ((root : ℤ) + firstSource + queue) output -
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) ((root : ℤ) + secondSource + queue) output
  have hpoint (output) :
      |attachedBodyAtSource cutoffScale parameter beta queue firstSource output -
        attachedBodyAtSource cutoffScale parameter beta queue secondSource output| ≤
      ∑ root, rootLaw.weight root * |difference root output| := by
    unfold attachedBodyAtSource
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
      apply Finset.sum_congr rfl
      intro root _
      rw [abs_mul, abs_of_nonneg (rootLaw.nonneg root)])
  have hrow (root : Window (v7RootCutoff parameter)) : (∑ output, |difference root output|) ≤
      12 * ((firstSource - secondSource).natAbs : ℝ) / Parameters.modulus parameter := by
    have hh := actualBodyCenter_translation_pair_short_bound cutoffScale parameter beta hscale hp hn hm
      ((root : ℤ) + firstSource + queue) ((root : ℤ) + secondSource + queue)
    have heq : (root : ℤ) + firstSource + queue - ((root : ℤ) + secondSource + queue) = firstSource - secondSource := by ring
    simpa only [heq] using hh
  calc
    _ ≤ ∑ output, ∑ root, rootLaw.weight root * |difference root output| := Finset.sum_le_sum fun output _ => hpoint output
    _ = ∑ root, rootLaw.weight root * ∑ output, |difference root output| := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ root, rootLaw.weight root * (12 * ((firstSource - secondSource).natAbs : ℝ) / Parameters.modulus parameter) :=
      Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left (hrow root) (rootLaw.nonneg root)
    _ = _ := by rw [← Finset.sum_mul, rootLaw.sum_one, one_mul]

/-- The actual root-averaged body source difference, with a complete fixed
body fiber. This is uniform in the common queue increment. -/
theorem actual_attached_body_source_difference_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue firstSource secondSource : ℤ,
      let difference := attachedBodyAtSource cutoffScale parameter (beta parameter) queue firstSource -
        attachedBodyAtSource cutoffScale parameter (beta parameter) queue secondSource
      (∀ color, |difference color| ≤ 16 * actualPrimary cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter)) difference ≤
        192 * ((firstSource - secondSource).natAbs : ℝ) / Parameters.modulus parameter := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel, eventually_ge_atTop 1]
    with parameter hb hp hlower hlarge queue firstSource secondSource
  dsimp only at hlower ⊢
  let P := actualBodyCenter cutoffScale parameter (beta parameter)
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let difference := attachedBodyAtSource cutoffScale parameter (beta parameter) queue firstSource -
    attachedBodyAtSource cutoffScale parameter (beta parameter) queue secondSource
  have hP (color) : 0 ≤ P color := (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1
  have hpoint (color) : |difference color| ≤ 16 * p color := by
    have hf0 := attachedBodyAtSource_nonneg cutoffScale parameter (beta parameter) hP queue firstSource color
    have hs0 := attachedBodyAtSource_nonneg cutoffScale parameter (beta parameter) hP queue secondSource color
    have hf := attachedBodyAtSource_upper cutoffScale parameter (beta parameter) (fun color => (hb.2.1 color).2) queue firstSource color
    have hs := attachedBodyAtSource_upper cutoffScale parameter (beta parameter) (fun color => (hb.2.1 color).2) queue secondSource color
    have hh := mul_le_mul_of_nonneg_left (hlower.1 color) (by norm_num : (0 : ℝ) ≤ 16)
    have hh' : 4 / (Parameters.modulus parameter : ℝ) ≤ 16 * p color := by convert hh using 1; ring
    exact abs_le.mpr ⟨by dsimp only [difference, Pi.sub_apply]; linarith, by dsimp only [difference, Pi.sub_apply]; linarith⟩
  refine ⟨hpoint, ?_⟩
  have hh := profileSquareNorm_le_relative_mul_l1 p difference 16 hp.1 hpoint
  have hL1 := attachedBodyAtSource_difference_l1 cutoffScale parameter (beta parameter) hscale hlarge
    (fun color => (hp.1 color).le) hp.2 queue firstSource secondSource
  exact hh.trans ((mul_le_mul_of_nonneg_left hL1 (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end
end AFT.V7Calibration

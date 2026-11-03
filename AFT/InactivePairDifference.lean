import AFT.ActualPairSourceDifference
import AFT.ActualPairEnergy
import AFT.InactiveBodyDifference

/-! # Endpoint differences centered against the actual inactive source -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def inactiveEndpointDifference (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  inactivePairAtSource cutoffScale parameter source first second -
    averagedInactivePair cutoffScale parameter first second

def inactiveEndpointDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  inactiveEndpointDifference cutoffScale parameter source first second /
    (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second)

theorem inactiveEndpointDifference_average (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    inactiveEndpointDifference cutoffScale parameter source first second =
      ∑ other, (inactiveLegSource cutoffScale parameter).weight other *
        (inactivePairAtSource cutoffScale parameter source first second -
          inactivePairAtSource cutoffScale parameter other first second) := by
  simp only [inactiveEndpointDifference, averagedInactivePair, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem inactivePairAtSource_symmetric (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    inactivePairAtSource cutoffScale parameter source first second =
      inactivePairAtSource cutoffScale parameter source second first := by
  simp only [inactivePairAtSource_mixture, TrimmedSlice.mixedPair_symmetric
    (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (inactiveStart cutoffScale parameter) (fun _ => source)
    (errorLaw (bodyBlur cutoffScale parameter)).weight (Parameters.anchorWidth parameter) first second]

theorem inactiveEndpointDifference_symmetric (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    inactiveEndpointDifference cutoffScale parameter source first second =
      inactiveEndpointDifference cutoffScale parameter source second first := by
  unfold inactiveEndpointDifference averagedInactivePair
  simp only [inactivePairAtSource_symmetric cutoffScale parameter _ first second]

/-- Centering keeps the true source distribution, the interval row L1
bound, and the pointwise integer-window height simultaneously. -/
theorem actual_inactive_endpoint_counting_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∑ first, ∑ second, inactiveEndpointDifference cutoffScale parameter source first second) = 0 ∧
      (∀ first second, |inactiveEndpointDifference cutoffScale parameter source first second| ≤
        2 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) ∧
      (∀ first, (∑ second, |inactiveEndpointDifference cutoffScale parameter source first second|) ≤
        8 * (legCutoff cutoffScale parameter : ℝ) /
          ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) ∧
      (∀ first, (∑ second, inactiveEndpointDifference cutoffScale parameter source first second ^ 2) ≤
        16 * (legCutoff cutoffScale parameter : ℝ) /
          ((Parameters.modulus parameter : ℝ) ^ 2 * (Parameters.anchorWidth parameter : ℝ) ^ 2)) := by
  filter_upwards [actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_inactive_pair_source_bounds_eventually cutoffScale hscale] with parameter hb hd source
  let difference := inactiveEndpointDifference cutoffScale parameter source
  let nu := inactiveLegSource cutoffScale parameter
  have hmean := averagedInactivePair_bounds cutoffScale parameter hb
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hw : (0 : ℝ) < Parameters.anchorWidth parameter := by
    unfold Parameters.anchorWidth
    exact_mod_cast pow_pos (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega) 32
  have hsource (other : Window (legCutoff cutoffScale parameter - 1)) :
      |(other : ℤ)| ≤ legCutoff cutoffScale parameter := by
    have hh := abs_le.mpr (Finset.mem_Icc.mp other.property)
    omega
  have hpoint (first second) : |difference first second| ≤
      2 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) := by
    have hs0 := (hb source).1 first second
    have hs1 := (hb source).2.2 first second
    have hm0 := hmean.1 first second
    have hm1 := hmean.2.2 first second
    rw [mul_comm (Parameters.anchorWidth parameter : ℝ)] at hs1 hm1
    exact abs_le.mpr ⟨by dsimp only [difference, inactiveEndpointDifference]; linarith,
      by dsimp only [difference, inactiveEndpointDifference]; linarith⟩
  have hL1 (first) : (∑ second, |difference first second|) ≤
      8 * (legCutoff cutoffScale parameter : ℝ) /
        ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) := by
    calc
      _ ≤ ∑ second, ∑ other, nu.weight other *
          |inactivePairAtSource cutoffScale parameter source first second -
            inactivePairAtSource cutoffScale parameter other first second| := by
        apply Finset.sum_le_sum
        intro second _
        dsimp only [difference]
        rw [inactiveEndpointDifference_average]
        exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
          apply Finset.sum_congr rfl
          intro other _
          rw [abs_mul, abs_of_nonneg (nu.nonneg other)])
      _ = ∑ other, nu.weight other * ∑ second,
          |inactivePairAtSource cutoffScale parameter source first second -
            inactivePairAtSource cutoffScale parameter other first second| := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ other, nu.weight other * (8 * (legCutoff cutoffScale parameter : ℝ) /
          ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) := by
        apply Finset.sum_le_sum
        intro other _
        apply mul_le_mul_of_nonneg_left _ (nu.nonneg other)
        have hh := (hd source other (hsource source) (hsource other) first).2
        have hdiff := inactive_source_difference_bound cutoffScale parameter other source
        exact hh.trans ((div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 4)) (by positivity)).trans_eq (by ring))
      _ = _ := by rw [← Finset.sum_mul, nu.sum_one, one_mul]
  refine ⟨?_, hpoint, hL1, ?_⟩
  · simp only [inactiveEndpointDifference, Finset.sum_sub_distrib, (hb source).2.1, hmean.2.1, sub_self]
  · intro first
    calc
      _ ≤ ∑ second, (2 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) *
          |difference first second| := by
        apply Finset.sum_le_sum
        intro second _
        have hh := mul_le_mul_of_nonneg_right (hpoint first second) (abs_nonneg (difference first second))
        simpa only [← sq, sq_abs] using hh
      _ = (2 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) *
          ∑ second, |difference first second| := by rw [Finset.mul_sum]
      _ ≤ (2 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) *
          (8 * (legCutoff cutoffScale parameter : ℝ) /
            ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) :=
        mul_le_mul_of_nonneg_left (hL1 first) (by positivity)
      _ = _ := by ring

/-- The four density fibers and the marginal fibers are all controlled
against the actual primary calibration law. -/
theorem actual_inactive_endpoint_density_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      let p := actualPrimary cutoffScale parameter (beta parameter)
      let density := inactiveEndpointDensity cutoffScale parameter (beta parameter) source
      (∀ first second, |density first second| ≤
        32 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) ∧
      (∑ first, ∑ second, p first * p second * density first second ^ 2) ≤
        256 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
          (Parameters.anchorWidth parameter : ℝ) ^ 2 ∧
      (∀ first, (∑ second, p second * density first second ^ 2) ≤
        1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
          (Parameters.anchorWidth parameter : ℝ) ^ 2) ∧
      (∀ second, (∑ first, p first * density first second ^ 2) ≤
        1024 * (Parameters.modulus parameter : ℝ) * legCutoff cutoffScale parameter /
          (Parameters.anchorWidth parameter : ℝ) ^ 2) ∧
      (∀ first, |(∑ second, inactiveEndpointDifference cutoffScale parameter source first second) / p first| ≤
        32 * (legCutoff cutoffScale parameter : ℝ) / Parameters.anchorWidth parameter) ∧
      (∑ first, (∑ second, inactiveEndpointDifference cutoffScale parameter source first second) ^ 2 / p first) ≤
        256 * (legCutoff cutoffScale parameter : ℝ) ^ 2 / (Parameters.anchorWidth parameter : ℝ) ^ 2 := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [actual_inactive_endpoint_counting_eventually cutoffScale hscale,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel] with parameter hc hp source
  dsimp only at hp ⊢
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let difference := inactiveEndpointDifference cutoffScale parameter source
  let density := inactiveEndpointDensity cutoffScale parameter (beta parameter) source
  let q : ℝ := Parameters.modulus parameter
  let width : ℝ := Parameters.anchorWidth parameter
  let length : ℝ := legCutoff cutoffScale parameter
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hw : 0 < width := by
    dsimp only [width, Parameters.anchorWidth]
    exact_mod_cast pow_pos (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega) 32
  have hl : 0 < 1 / (4 * q) := by positivity
  have hp0 (color) : 0 < p color := hl.trans_le (hp.1 color)
  have hbounds := TrimmedSlice.pairDifference_density_bounds difference p (1 / (4 * q))
    (16 * length / (q ^ 2 * width ^ 2)) hl hp.1 (hc source).2.2.2
  have hmarg := TrimmedSlice.pairDifference_marginal_bounds difference p (1 / (4 * q))
    (8 * length / (q * width)) hl (by positivity) hp.1 (hc source).2.2.1
  have hfixed (first) : (∑ second, p second * density first second ^ 2) ≤
      1024 * q * length / width ^ 2 := by
    exact (hbounds.2 first).trans_eq (by field_simp [ne_of_gt hq, ne_of_gt hw]; ring)
  refine ⟨?_, ?_, hfixed, ?_, ?_, ?_⟩
  · intro first second
    change |density first second| ≤ 32 * q / width
    have hh := TrimmedSlice.pairDifference_density_sup difference p (1 / (4 * q)) (2 / (q * width))
      hl (by positivity) hp.1 (hc source).2.1 first second
    exact hh.trans_eq (by field_simp [ne_of_gt hq, ne_of_gt hw]; ring)
  · have heq : (∑ first, ∑ second, p first * p second * density first second ^ 2) =
        ∑ first, ∑ second, difference first second ^ 2 / (p first * p second) := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      dsimp only [density, inactiveEndpointDensity]
      change p first * p second * (difference first second / (p first * p second)) ^ 2 = _
      field_simp
    change (∑ first, ∑ second, p first * p second * density first second ^ 2) ≤ _
    rw [heq]
    exact hbounds.1.trans_eq (by
      simp only [Fintype.card_fin]
      change q * (16 * length / (q^2 * width^2)) / (1 / (4*q))^2 = 256*q*length/width^2
      field_simp [ne_of_gt hq, ne_of_gt hw]
      ring)
  · intro second
    change (∑ first, p first * density first second ^ 2) ≤ 1024*q*length/width^2
    calc
      _ = ∑ first, p first * density second first ^ 2 := by
        apply Finset.sum_congr rfl
        intro first _
        simp only [density, inactiveEndpointDensity, inactiveEndpointDifference_symmetric cutoffScale parameter _ first second,
          mul_comm (actualPrimary cutoffScale parameter (beta parameter) first)]
      _ ≤ _ := hfixed second
  · intro first
    change |(∑ second, difference first second) / p first| ≤ 32 * length / width
    exact (hmarg.1 first).trans_eq (by field_simp [ne_of_gt hq, ne_of_gt hw]; ring)
  · exact hmarg.2.trans_eq (by
      simp only [Fintype.card_fin]
      change q * (8*length/(q*width))^2 / (1/(4*q)) = 256*length^2/width^2
      field_simp [ne_of_gt hq, ne_of_gt hw]
      ring)

end
end AFT.V7Calibration

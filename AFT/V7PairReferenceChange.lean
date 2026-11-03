import AFT.PairReferenceChange
import AFT.V7SafeInactivePair

/-! # The actual reference correction for the inactive pair target -/

namespace AFT.V7Calibration

open GaussianSource SafeConvolution Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 800000
attribute [local instance] actualModulusNeZero

def actualPairReferenceChange (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
  fun point => SafePair.canonicalPair (actualReferenceLaw cutoffScale parameter beta).weight
      (averagedInactivePair cutoffScale parameter) point.1 point.2 -
    SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus parameter : ℝ))
      (averagedInactivePair cutoffScale parameter) point.1 point.2

/-- The literal rank-two correction is controlled by the true reference
boundary perturbation and actual inactive pair marginals. -/
theorem actual_pair_reference_change_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ((Parameters.modulus parameter : ℝ) * countingL2 (actualPairReferenceChange cutoffScale parameter (beta parameter))) ^ 2 ≤
        2560 / (parameter : ℝ) ^ 38 ∧
      RowBound (8 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16))
        (actualPairReferenceChange cutoffScale parameter (beta parameter)) ∧
      RowBound (8 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16))
        (fun point => actualPairReferenceChange cutoffScale parameter (beta parameter) point.swap) ∧
      SupBound (8 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32))
        (actualPairReferenceChange cutoffScale parameter (beta parameter)) := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta,
    actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_inactive_pair_marginal_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hl hr hL1 hm hmarg hp
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  letI : Nonempty (Fin (Parameters.modulus parameter)) := Fin.pos_iff_nonempty.mp (Parameters.modulus_prime parameter).pos
  let uniform : FiniteDist (Fin (Parameters.modulus parameter)) := FiniteDist.uniform _
  have huniform (x) : uniform.weight x = 1 / (Parameters.modulus parameter : ℝ) := by
    simp only [uniform, FiniteDist.uniform_weight, Fintype.card_fin, one_div]
  have huniformFun : uniform.weight = (fun _ => 1 / (Parameters.modulus parameter : ℝ)) := funext huniform
  have href (x) : (actualReferenceLaw cutoffScale parameter (beta parameter)).weight x ≤
      2 / (Parameters.modulus parameter : ℝ) := by rw [hl.2.2]; exact (hr.1 x).2
  have hu (x) : uniform.weight x ≤ 2 / (Parameters.modulus parameter : ℝ) := by rw [huniform]; gcongr; norm_num
  have hmass := averagedInactivePair_bounds cutoffScale parameter hm
  have hrow (x) := (averagedInactivePair_marginal_le cutoffScale parameter hmarg x).1
  have hcol (y) := (averagedInactivePair_marginal_le cutoffScale parameter hmarg y).2
  have hpoint (x y) : |actualPairReferenceChange cutoffScale parameter (beta parameter) (x,y)| ≤
      8 / (Parameters.modulus parameter : ℝ)^2 := by
    have hh := SafePair.canonicalPair_reference_point_le (actualReferenceLaw cutoffScale parameter (beta parameter)) uniform
      (averagedInactivePair cutoffScale parameter) hmass.1 hmass.2.1
      (2/(Parameters.modulus parameter : ℝ)) href hu hrow hcol x y
    rw [huniformFun] at hh
    change |actualPairReferenceChange cutoffScale parameter (beta parameter) (x,y)| ≤
      2 * (2/(Parameters.modulus parameter : ℝ))^2 at hh
    exact hh.trans_eq (by ring)
  have hq32 : (parameter : ℝ)^32 ≤ Parameters.modulus parameter := by
    have hh : (parameter : ℝ)^40 ≤ Parameters.modulus parameter := by
      exact_mod_cast (by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
    exact (pow_le_pow_right₀ hp1 (by decide)).trans hh
  have hrowGeneric (f : Fin (Parameters.modulus parameter) → ℝ)
      (hf : ∀ y, |f y| ≤ 8 / (Parameters.modulus parameter : ℝ)^2) :
      countingL2 f ≤ 8 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    calc
      _ ≤ ∑ _y : Fin (Parameters.modulus parameter), (8 / (Parameters.modulus parameter : ℝ)^2)^2 := by
        apply Finset.sum_le_sum
        intro y _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hf y) 2
      _ = 64 / (Parameters.modulus parameter : ℝ)^3 := by simp; field_simp; ring
      _ ≤ 64 / ((Parameters.modulus parameter : ℝ)^2 * (parameter : ℝ)^32) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hq32 (sq_nonneg (Parameters.modulus parameter : ℝ))]
      _ = _ := by field_simp; ring
  refine ⟨?_, (fun x => hrowGeneric _ (fun y => hpoint x y)),
    (fun y => hrowGeneric _ (fun x => hpoint x y)), ?_⟩
  · have he := SafePair.canonicalPair_reference_square_le (actualReferenceLaw cutoffScale parameter (beta parameter)) uniform
      (averagedInactivePair cutoffScale parameter) hmass.1 hmass.2.1 (2/(Parameters.modulus parameter : ℝ))
      (by positivity) href hu hrow hcol
    rw [huniformFun] at he
    have hL1actual : (∑ x, |(actualReferenceLaw cutoffScale parameter (beta parameter)).weight x -
        1 / (Parameters.modulus parameter : ℝ)|) ≤ 80 / (parameter : ℝ)^38 := by
      rw [hl.2.2]
      exact hL1.2
    have hh := mul_le_mul_of_nonneg_left
      (he.trans (mul_le_mul_of_nonneg_left hL1actual (by positivity))) (sq_nonneg (Parameters.modulus parameter : ℝ))
    change (Parameters.modulus parameter : ℝ)^2 *
      (∑ x, ∑ y, actualPairReferenceChange cutoffScale parameter (beta parameter) (x,y)^2) ≤ _ at hh
    rw [mul_pow, countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
    exact hh.trans_eq (by field_simp; ring)
  · intro point
    apply (hpoint point.1 point.2).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hq32 hq.le]

end
end AFT.V7Calibration

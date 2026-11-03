import CurrentAFT.LocalReferenceEnergy

/-! # Actual fixed-scalar pair marginals and the sharp first-degree scale -/

namespace CurrentAFT.ReferenceMarginals

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff primaryLaw

private theorem averagedLaw_height (modulus width cutoff : ℕ) (start source : ℤ)
    (hwidth : 0 < width) (hdelete : 2 * (2 + 2 * width + 2 * cutoff) ≤ modulus)
    (hstart : ∀ offset ∈ anchorInterval start width,
      |offset| ≤ 2 * (width : ℤ) + ((cutoff : ℤ) - 1))
    (hsource : |source| ≤ (cutoff : ℤ) - 1) (color : ℤ) :
    TrimmedSlice.averagedLaw modulus 1 start source width color ≤ 2 / (modulus : ℝ) := by
  have hclear : 2 * (1 : ℤ) + (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) +
      ((cutoff : ℤ) - 1) < modulus := by omega
  have h := TrimmedSlice.mixedLaw_le modulus 1
    (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) ((cutoff : ℤ) - 1)
    (fun _ : Unit => start) (fun _ : Unit => source) (FiniteDist.uniform Unit).weight width hwidth.ne'
    (FiniteDist.uniform Unit).nonneg (FiniteDist.uniform Unit).sum_one
    (fun _ => hstart) (fun _ => hsource) hclear color
  simp only [TrimmedSlice.mixedLaw, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, one_mul] at h
  apply h.trans
  have hq : (0 : ℝ) < modulus := by exact_mod_cast (by omega : 0 < modulus)
  have hd := Nat.cast_le (α := ℝ).mpr hdelete
  push_cast at hd
  have hden : 0 < (modulus : ℝ) - 2 - (2 * width + ((cutoff : ℝ) - 1)) - ((cutoff : ℝ) - 1) := by linarith
  push_cast
  norm_num only [mul_one]
  apply (div_le_div_iff₀ hden hq).mpr
  linarith

theorem diffuseSeedPair_first_marginal (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (∑ second, (diffuseSeedPair security positive seed).weight (output, second)) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  simp_rw [diffuseSeedPair_weight]
  have h := TrimmedSlice.mixedPair_first_marginal (Parameters.modulus security) 1
    (fun _ : Unit => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun _ : Unit => actualSecond security seed) (FiniteDist.uniform Unit).weight
    (Parameters.anchorWidth security) (by norm_num) output
  simpa only [TrimmedSlice.mixedPair, TrimmedSlice.mixedLaw, Fintype.sum_unique,
    FiniteDist.uniform_weight, Fintype.card_unique, Nat.cast_one, inv_one, one_mul] using h

theorem diffuseSeedPair_marginal_height (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (∑ second, (diffuseSeedPair security positive seed).weight (output, second)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  rw [diffuseSeedPair_first_marginal]
  apply averagedLaw_height _ _ _ _ _ (InwardAnchor.anchorWidth_pos security)
  · exact FirstResponse.two_deletion_le_modulus security
  · exact fun offset hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin
  · exact actualSecond_bound security seed

theorem diffusePairAt_first_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (diffusePairAt security primary scalar).weight (output, second)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  unfold diffusePairAt
  simp only [FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * (2 / (Parameters.modulus security : ℝ)) := by
      apply Finset.sum_le_sum
      intro coin _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      calc
        _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (2 / (Parameters.modulus security : ℝ)) :=
          Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
            (diffuseSeedPair_marginal_height security _ _ output) ((publicBlurLaw security).nonneg edge))
        _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffusePairAt_symmetric (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (diffusePairAt security primary scalar).weight (first, second) =
      (diffusePairAt security primary scalar).weight (second, first) := by
  simp only [diffusePairAt, FiniteDist.mix_weight]
  apply Finset.sum_congr rfl
  intro coin _
  congr 1
  apply Finset.sum_congr rfl
  intro edge _
  rw [diffuseSeedPair_weight, diffuseSeedPair_weight]
  simp only [TrimmedSlice.averagedPair, TrimmedSlice.orderedPairSlice_symmetric]

theorem diffusePairAt_second_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ first, (diffusePairAt security primary scalar).weight (first, output)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  simp_rw [diffusePairAt_symmetric security primary scalar _ output]
  exact diffusePairAt_first_height security primary scalar output

theorem markedCompanionAt_row_sum (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (∑ primary, (markedCompanionAt security primary scalar).weight output) ≤ 2 := by
  simp only [markedCompanionAt, FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * 2 :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_row_sum_le_two security (-scalar.val) _ _)
        ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedCompanionAt_primary_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (∑ primary, (primaryLaw security).weight primary * (markedCompanionAt security primary scalar).weight output) ≤
      2 * primaryMaximum security := by
  have hmaximum : 0 ≤ primaryMaximum security :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ primary, primaryMaximum security * (markedCompanionAt security primary scalar).weight output :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_right
        (GaussianHeights.primaryLaw_upper security primary) ((markedCompanionAt security primary scalar).nonneg output))
    _ = primaryMaximum security * ∑ primary, (markedCompanionAt security primary scalar).weight output :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ primaryMaximum security * 2 := mul_le_mul_of_nonneg_left
      (markedCompanionAt_row_sum security scalar output) hmaximum
    _ = _ := by ring

end

end CurrentAFT.ReferenceMarginals

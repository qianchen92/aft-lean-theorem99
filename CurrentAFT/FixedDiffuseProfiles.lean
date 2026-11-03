import CurrentAFT.ReferenceMarginals

/-! # The real diffuse sign profiles before averaging the protected scalar -/

namespace CurrentAFT.FixedDiffuseProfiles

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ReferenceMarginals
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw activation

def signPairLaw (security : ℕ) (positive : Bool) (scalar : Scalar security) :
    FiniteDist (Palette security × Palette security) :=
  (publicBlurLaw security).mix (fun edge => diffuseSeedPair security positive (edge, scalar))

def fixedProfile (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) : ℝ :=
  ∑ second, (signPairLaw security positive scalar).weight (output, second)

theorem fixedProfile_nonneg (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) :
    0 ≤ fixedProfile security positive scalar output :=
  Finset.sum_nonneg (fun _ _ => (signPairLaw security positive scalar).nonneg _)

theorem fixedProfile_mass (security : ℕ) (positive : Bool) (scalar : Scalar security) :
    (∑ output, fixedProfile security positive scalar output) = 1 := by
  have h := (signPairLaw security positive scalar).sum_one
  simpa only [Fintype.sum_prod_type, fixedProfile] using h

theorem fixedProfile_height (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) :
    fixedProfile security positive scalar output ≤ 2 / (Parameters.modulus security : ℝ) := by
  unfold fixedProfile signPairLaw
  simp only [FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (diffuseSeedPair_marginal_height security positive (edge, scalar) output) ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def directionProfile (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) : ℝ :=
  (FiniteDist.uniform Bool).expectation (fun coin =>
    fixedProfile security (InwardAnchor.positiveDirection security primary coin) scalar output)

theorem diffusePairAt_first (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (diffusePairAt security primary scalar).weight (output, second)) =
      directionProfile security primary scalar output := by
  unfold diffusePairAt directionProfile fixedProfile signPairLaw
  simp only [FiniteDist.mix_weight, FiniteDist.expectation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coin _
  rw [← Finset.mul_sum]

theorem diffusePairAt_second (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ first, (diffusePairAt security primary scalar).weight (first, output)) =
      directionProfile security primary scalar output := by
  simp_rw [diffusePairAt_symmetric security primary scalar _ output]
  exact diffusePairAt_first security primary scalar output

def fixedMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (fixedProfile security true scalar output + fixedProfile security false scalar output) / 2

def fixedSignProfile (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (1 - activation security) * (fixedProfile security true scalar output - fixedProfile security false scalar output)

theorem direction_decomposition (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    2 * (1 - activation security) * directionProfile security primary scalar output =
      2 * (1 - activation security) * fixedMean security scalar output +
        fixedSignProfile security scalar output * FirstResponse.anchorSign security primary := by
  unfold directionProfile
  simp only [FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  by_cases hl : 2 * primary.val < Parameters.modulus security - 1
  · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, if_true]
    unfold fixedMean fixedSignProfile
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * primary.val
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false, if_true]
      unfold fixedMean fixedSignProfile
      ring
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false]
      unfold fixedMean fixedSignProfile
      ring

theorem fixedSignProfile_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    |fixedSignProfile security scalar output| ≤ 2 / (Parameters.modulus security : ℝ) := by
  have hfirst := fixedProfile_height security true scalar output
  have hsecond := fixedProfile_height security false scalar output
  have hfirst0 := fixedProfile_nonneg security true scalar output
  have hsecond0 := fixedProfile_nonneg security false scalar output
  have hdiff : |fixedProfile security true scalar output - fixedProfile security false scalar output| ≤
      2 / (Parameters.modulus security : ℝ) := abs_le.mpr (by constructor <;> linarith)
  have ha := activation_pos security
  have ha1 := activation_le_half security
  rw [fixedSignProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
  have hq := FirstResponse.modulus_pos security
  nlinarith only [hdiff, ha, ha1, div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq.le]

theorem fixedSignProfile_l1 (security : ℕ) (scalar : Scalar security) :
    (∑ output, |fixedSignProfile security scalar output|) ≤ 2 := by
  have ha := activation_pos security
  have ha1 := activation_le_half security
  have hpoint (output : Palette security) :
      |fixedSignProfile security scalar output| ≤ fixedProfile security true scalar output +
        fixedProfile security false scalar output := by
    rw [fixedSignProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
    have hdiff := abs_sub (fixedProfile security true scalar output) (fixedProfile security false scalar output)
    rw [abs_of_nonneg (fixedProfile_nonneg security true scalar output),
      abs_of_nonneg (fixedProfile_nonneg security false scalar output)] at hdiff
    nlinarith only [hdiff, ha, ha1, abs_nonneg
      (fixedProfile security true scalar output - fixedProfile security false scalar output)]
  calc
    _ ≤ ∑ output, (fixedProfile security true scalar output + fixedProfile security false scalar output) :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = 2 := by rw [Finset.sum_add_distrib, fixedProfile_mass, fixedProfile_mass]; norm_num

theorem pairAt_histogram (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (pairAt security primary scalar).weight (output, second)) +
        (∑ first, (pairAt security primary scalar).weight (first, output)) =
      activation security * atom primary output + activation security * (markedCompanionAt security primary scalar).weight output +
        2 * (1 - activation security) * fixedMean security scalar output +
          fixedSignProfile security scalar output * FirstResponse.anchorSign security primary := by
  classical
  have hfirst : (∑ second, (markedPairAt security primary scalar).weight (output, second)) = atom primary output := by
    simp only [markedPairAt_weight, Finset.sum_ite_irrel, Finset.sum_const_zero, FiniteDist.sum_one, atom]
  have hsecond : (∑ first, (markedPairAt security primary scalar).weight (first, output)) =
      (markedCompanionAt security primary scalar).weight output := by
    simp only [markedPairAt_weight, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hdiff := direction_decomposition security primary scalar output
  simp only [pairAt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [diffusePairAt_first, diffusePairAt_second, hfirst, hsecond]
  nlinarith only [hdiff]

end

end CurrentAFT.FixedDiffuseProfiles

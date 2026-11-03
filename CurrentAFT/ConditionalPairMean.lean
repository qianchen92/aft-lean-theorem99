import CurrentAFT.ReferenceMarginals
import CurrentAFT.BackgroundCertificates
import CurrentAFT.ActualControls

/-!
# The actual fixed-scalar off-body pair mean

The same protected second scalar is fixed in both marginals. Bounds use
the full primary reference, so the marked primary atom contributes energy
one even when its uniform-reference height is large.
-/

namespace CurrentAFT.ConditionalPairMean

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := LocalReferenceEnergy.Scalar security

def firstMarginal {Color : Type*} [Fintype Color] (law : FiniteDist (Color × Color)) :
    FiniteDist Color where
  weight color := ∑ other, law.weight (color, other)
  nonneg color := Finset.sum_nonneg fun other _ => law.nonneg (color, other)
  sum_one := by simpa only [Fintype.sum_prod_type] using law.sum_one

def secondMarginal {Color : Type*} [Fintype Color] (law : FiniteDist (Color × Color)) :
    FiniteDist Color where
  weight color := ∑ other, law.weight (other, color)
  nonneg color := Finset.sum_nonneg fun other _ => law.nonneg (other, color)
  sum_one := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using law.sum_one

def diffuseFirst (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => firstMarginal (diffusePairAt security primary scalar)

def diffuseSecond (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => secondMarginal (diffusePairAt security primary scalar)

def markedSecond (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => markedCompanionAt security primary scalar

def pairMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (1 - activation security) * ((diffuseFirst security scalar).weight output +
      (diffuseSecond security scalar).weight output) +
    activation security * ((primaryLaw security).weight output + (markedSecond security scalar).weight output)

def centeredMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  pairMean security scalar output - 2 * uniformProfile security output

theorem pairMean_mass (security : ℕ) (scalar : Scalar security) :
    (∑ output, pairMean security scalar output) = 2 := by
  simp only [pairMean, Finset.sum_add_distrib, ← Finset.mul_sum, FiniteDist.sum_one]
  ring

theorem centeredMean_mass (security : ℕ) (scalar : Scalar security) :
    (∑ output, centeredMean security scalar output) = 0 := by
  have huniform : (∑ output, uniformProfile security output) = 1 := by
    simp only [uniformProfile, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(modulus_pos security).ne']
  simp only [centeredMean, Finset.sum_sub_distrib, ← Finset.mul_sum, pairMean_mass, huniform]
  norm_num

theorem diffuseFirst_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (diffuseFirst security scalar).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  simp only [diffuseFirst, FiniteDist.mix_weight, firstMarginal]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (ReferenceMarginals.diffusePairAt_first_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffuseSecond_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (diffuseSecond security scalar).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  simp only [diffuseSecond, FiniteDist.mix_weight, secondMarginal]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (ReferenceMarginals.diffusePairAt_second_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedSecond_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (markedSecond security scalar).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  simp only [markedSecond, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (markedCompanionAt_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem height_profile_energy (security : ℕ) (law : FiniteDist (Palette security))
    (height : ℝ) (hheight : 0 ≤ height) (hbound : ∀ color, law.weight color ≤ height) :
    profileSquareNorm (primaryLaw security).weight law.weight ≤
      2 * (Parameters.modulus security : ℝ) * height := by
  have hdom (color : Palette security) : law.weight color ≤
      (2 * (Parameters.modulus security : ℝ) * height) * (primaryLaw security).weight color := by
    have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security color
    have hscale := mul_le_mul_of_nonneg_left hlower
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (modulus_pos security).le) hheight)
    have hequal : (2 * (Parameters.modulus security : ℝ) * height) *
        (1 / (2 * (Parameters.modulus security : ℝ))) = height := by
      field_simp [(modulus_pos security).ne']
    rw [hequal] at hscale
    exact (hbound color).trans hscale
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (primaryLaw security).weight law.weight (2 * (Parameters.modulus security : ℝ) * height)
    (by positivity) (primaryLaw security).nonneg law.nonneg hdom

theorem primary_profile_energy (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight = 1 := by
  unfold profileSquareNorm
  simp only [sq, mul_div_cancel_right₀ _ (primaryReference_positive security _).ne']
  exact (primaryLaw security).sum_one

private theorem five_profile_square (activation first second primary companion uniform : ℝ)
    (hactivation : 0 ≤ activation) (hactivation' : activation ≤ 1) :
    ((1 - activation) * (first + second) + activation * (primary + companion) - 2 * uniform) ^ 2 ≤
      8 * (first ^ 2 + second ^ 2 + primary ^ 2 + companion ^ 2 + uniform ^ 2) := by
  have hfirst : ((1 - activation) * first) ^ 2 ≤ first ^ 2 := by
    nlinarith [sq_nonneg first, mul_nonneg (sq_nonneg first) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hsecond : ((1 - activation) * second) ^ 2 ≤ second ^ 2 := by
    nlinarith [sq_nonneg second, mul_nonneg (sq_nonneg second) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hprimary : (activation * primary) ^ 2 ≤ primary ^ 2 := by
    nlinarith [sq_nonneg primary, mul_nonneg (sq_nonneg primary) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hcompanion : (activation * companion) ^ 2 ≤ companion ^ 2 := by
    nlinarith [sq_nonneg companion, mul_nonneg (sq_nonneg companion) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  nlinarith [sq_nonneg ((1 - activation) * (first - second)),
    sq_nonneg (activation * (primary - companion)),
    sq_nonneg ((1 - activation) * (first + second) - activation * (primary + companion)),
    sq_nonneg ((1 - activation) * (first + second) + activation * (primary + companion) + 2 * uniform)]

theorem centeredMean_energy (security : ℕ) (scalar : Scalar security) :
    profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) ≤
      88 + 16 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hfirst := height_profile_energy security (diffuseFirst security scalar)
    (2 / (Parameters.modulus security : ℝ)) (by positivity) (diffuseFirst_height security scalar)
  have hsecond := height_profile_energy security (diffuseSecond security scalar)
    (2 / (Parameters.modulus security : ℝ)) (by positivity) (diffuseSecond_height security scalar)
  have hmarked := height_profile_energy security (markedSecond security scalar)
    (1 / (Parameters.anchorWidth security : ℝ)) (by positivity) (markedSecond_height security scalar)
  have huniform := FringeCertificate.uniformProfile_square_le_two security
  have hpoint (color : Palette security) := div_le_div_of_nonneg_right
    (five_profile_square (activation security) ((diffuseFirst security scalar).weight color)
      ((diffuseSecond security scalar).weight color) ((primaryLaw security).weight color)
      ((markedSecond security scalar).weight color) (uniformProfile security color)
      (activation_pos security).le (by linarith [activation_le_half security]))
    ((primaryLaw security).nonneg color)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun color _ => hpoint color)
  have hexpand : ∀ a b c d e denominator : ℝ,
      8 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) / denominator =
      8 * (a ^ 2 / denominator + b ^ 2 / denominator + c ^ 2 / denominator +
        d ^ 2 / denominator + e ^ 2 / denominator) := by intros; ring
  simp only [hexpand, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  change profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) ≤
    8 * (profileSquareNorm (primaryLaw security).weight (diffuseFirst security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (diffuseSecond security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight +
      profileSquareNorm (primaryLaw security).weight (markedSecond security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (uniformProfile security)) at hsum
  rw [primary_profile_energy] at hsum
  have hq := (modulus_pos security).ne'
  have hcancel : 2 * (Parameters.modulus security : ℝ) * (2 / Parameters.modulus security) = 4 := by
    field_simp
    ring
  rw [hcancel] at hfirst hsecond
  simp only [div_eq_mul_inv] at hmarked ⊢
  nlinarith

theorem markedPairAt_first (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ other, (markedPairAt security primary scalar).weight (output, other)) =
      if primary = output then 1 else 0 := by
  simp only [markedPairAt, FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  by_cases hprimary : primary = output
  · simp only [hprimary, true_and]
    simp [FiniteDist.sum_one]
  · simp [hprimary]

theorem markedPairAt_second (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ other, (markedPairAt security primary scalar).weight (other, output)) =
      (markedCompanionAt security primary scalar).weight output := by
  simp only [markedPairAt, FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single output]
  · simp
  · intro other _ hother
    apply Finset.sum_eq_zero
    intro index _
    simp [hother]
  · simp

/-- Both actual pair coordinates are averaged at one and the same fixed
protected scalar; no marginal-independence replacement is made. -/
theorem pairMean_actual (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    pairMean security scalar output =
      ∑ primary, (primaryLaw security).weight primary *
        ((∑ other, (pairAt security primary scalar).weight (output, other)) +
          ∑ other, (pairAt security primary scalar).weight (other, output)) := by
  simp only [pairAt, Finset.sum_add_distrib, ← Finset.mul_sum,
    markedPairAt_first, markedPairAt_second]
  unfold pairMean diffuseFirst diffuseSecond markedSecond
  simp only [FiniteDist.mix_weight, firstMarginal, secondMarginal]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf

end

end CurrentAFT.ConditionalPairMean

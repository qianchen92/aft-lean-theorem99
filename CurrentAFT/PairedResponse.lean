import CurrentAFT.ProposalCenter
import CurrentAFT.ProposalDeviation

/-!
# The actual paired primary and compensator score

The two control laws, the smoothed inward anchor, and the activation are
the concrete current proposal. The zero center weights outside the safe
interval are retained: the actual anchor kernel vanishes there as well.
No positive lower bound is required at those forbidden atoms.

Finite Cauchy--Schwarz and the proved activated anchor height give the
compensator variance bound. Independence of the two public controls then
gives the complete paired variance. The joint-input extensions average
these actual estimates and never divide by root probabilities.
-/

namespace CurrentAFT.PairedResponse

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.safeMargin DiffuseProfiles.activation primaryLaw centerLaw
  InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def anchorWeightedScore (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  ∑ primary, (InwardAnchor.smoothedAnchorLaw security primary).weight center *
    (primaryLaw security).weight primary * score primary

def anchorScoreEnergy (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  ∑ primary, (InwardAnchor.smoothedAnchorLaw security primary).weight center *
    (primaryLaw security).weight primary * score primary ^ 2

def compensatorScore (security : ℕ) (score : Palette security → ℝ) (center : Palette security) : ℝ :=
  activation security * anchorWeightedScore security score center / (centerLaw security).weight center

/-- The actual public score reads one primary and its independent
compensator, with the same coefficient function in both summands. -/
def pairedScore (security : ℕ) (score : Palette security → ℝ)
    (primary center : Palette security) : ℝ :=
  score primary - compensatorScore security score center

theorem anchorWeightedScore_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, anchorWeightedScore security score center) =
      ∑ primary, (primaryLaw security).weight primary * score primary := by
  unfold anchorWeightedScore
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, InwardAnchor.smoothedAnchorLaw_mass, one_mul]

theorem anchorScoreEnergy_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, anchorScoreEnergy security score center) =
      ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 := by
  unfold anchorScoreEnergy
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, InwardAnchor.smoothedAnchorLaw_mass, one_mul]

theorem anchorWeightedScore_zero_outside (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) (hunsafe : ¬InwardAnchor.SafeColor security center) :
    anchorWeightedScore security score center = 0 := by
  simp only [anchorWeightedScore, InwardAnchor.smoothedAnchorLaw_zero_outside security _ center hunsafe,
    zero_mul, Finset.sum_const_zero]

theorem centerLaw_safe_atom_lower (security : ℕ) (center : Palette security)
    (hsafe : InwardAnchor.SafeColor security center) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (centerLaw security).weight center := by
  have hq := FirstResponse.modulus_pos security
  have hden : (0 : ℝ) < Parameters.modulus security - 2 * Parameters.safeMargin security := by
    have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
    push_cast at h
    linarith
  have hheight : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le hden
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  have hlower := (centerProfile_bounds security center).1
  rw [safeLaw_weight, if_pos hsafe] at hlower
  simp only [centerLaw]
  calc
    _ = (1 / (Parameters.modulus security : ℝ)) / 2 := by ring
    _ ≤ safeHeight security / 2 := div_le_div_of_nonneg_right hheight (by norm_num)
    _ ≤ _ := hlower

theorem centerLaw_zero_implies_anchorScore_zero (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) (hzero : (centerLaw security).weight center = 0) :
    anchorWeightedScore security score center = 0 := by
  by_cases hsafe : InwardAnchor.SafeColor security center
  · have hlower := centerLaw_safe_atom_lower security center hsafe
    have hq := FirstResponse.modulus_pos security
    rw [hzero] at hlower
    have hpositive : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ)) := by positivity
    linarith
  · exact anchorWeightedScore_zero_outside security score center hsafe

theorem compensatorScore_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center) =
      activation security * ∑ primary, (primaryLaw security).weight primary * score primary := by
  calc
    _ = ∑ center, activation security * anchorWeightedScore security score center := by
      apply Finset.sum_congr rfl
      intro center _
      unfold compensatorScore
      by_cases hz : (centerLaw security).weight center = 0
      · rw [hz, centerLaw_zero_implies_anchorScore_zero security score center hz]
        ring
      · field_simp
    _ = _ := by rw [← Finset.mul_sum, anchorWeightedScore_mass]

theorem pairedScore_mean_zero (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      pairedScore security score primary center) = 0 := by
  have hcompensator : (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0 := by
    rw [compensatorScore_mass, hcentered, mul_zero]
  have hrow (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center) = (primaryLaw security).weight primary * score primary := by
    unfold pairedScore
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [show (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center * score primary) =
      (primaryLaw security).weight primary * score primary * ∑ center, (centerLaw security).weight center by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
    rw [FiniteDist.sum_one, mul_one]
    have hzero : (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        compensatorScore security score center) = 0 := by
      rw [show (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
          compensatorScore security score center) = (primaryLaw security).weight primary *
            ∑ center, (centerLaw security).weight center * compensatorScore security score center by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
      rw [hcompensator, mul_zero]
    rw [hzero, sub_zero]
  simp_rw [hrow]
  exact hcentered

/-- The actual kernel comparison, including its zero rows outside safe
support, is derived from the actual activated anchor height. -/
theorem activated_anchor_center_comparison (security : ℕ) (center : Palette security) :
    activation security * anchorPrimaryMean security center ≤ 256 * (centerLaw security).weight center := by
  by_cases hsafe : InwardAnchor.SafeColor security center
  · have h := activated_anchorPrimaryMean_height security center
    have hcenter := mul_le_mul_of_nonneg_left (centerLaw_safe_atom_lower security center hsafe)
      (show (0 : ℝ) ≤ 256 by norm_num)
    have hq := FirstResponse.modulus_pos security
    have hsame : 256 * (1 / (2 * (Parameters.modulus security : ℝ))) =
        128 / (Parameters.modulus security : ℝ) := by ring
    rw [hsame] at hcenter
    exact h.trans hcenter
  · have hzero : anchorPrimaryMean security center = 0 := by
      simp only [anchorPrimaryMean, InwardAnchor.smoothedAnchorLaw_zero_outside security _ center hsafe,
        zero_mul, Finset.sum_const_zero]
    rw [hzero, mul_zero]
    exact mul_nonneg (by norm_num) ((centerLaw security).nonneg center)

theorem anchorWeightedScore_square_le (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    anchorWeightedScore security score center ^ 2 ≤
      anchorPrimaryMean security center * anchorScoreEnergy security score center := by
  unfold anchorWeightedScore anchorPrimaryMean anchorScoreEnergy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro primary _
    exact mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
      ((primaryLaw security).nonneg primary)
  · intro primary _
    exact mul_nonneg (mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
      ((primaryLaw security).nonneg primary)) (sq_nonneg _)
  · intro primary _
    ring

theorem compensator_point_energy_le (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    activation security ^ 2 * (anchorWeightedScore security score center ^ 2 /
      (centerLaw security).weight center) ≤
        256 * activation security * anchorScoreEnergy security score center := by
  have henergy : 0 ≤ anchorScoreEnergy security score center :=
    Finset.sum_nonneg (fun primary _ =>
      mul_nonneg (mul_nonneg ((InwardAnchor.smoothedAnchorLaw security primary).nonneg center)
        ((primaryLaw security).nonneg primary)) (sq_nonneg _))
  by_cases hz : (centerLaw security).weight center = 0
  · rw [hz, div_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (activation_pos security).le) henergy
  · have hb : 0 < (centerLaw security).weight center :=
      lt_of_le_of_ne ((centerLaw security).nonneg center) (Ne.symm hz)
    have hCS := mul_le_mul_of_nonneg_left (anchorWeightedScore_square_le security score center)
      (sq_nonneg (activation security))
    have hrow := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (activated_anchor_center_comparison security center) (activation_pos security).le) henergy
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hb).mpr
    nlinarith only [hCS, hrow]

theorem compensator_energy_le (security : ℕ) (score : Palette security → ℝ) :
    activation security ^ 2 * profileSquareNorm (centerLaw security).weight
      (anchorWeightedScore security score) ≤
        256 * activation security * ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ center, 256 * activation security * anchorScoreEnergy security score center :=
      Finset.sum_le_sum (fun center _ => compensator_point_energy_le security score center)
    _ = _ := by rw [← Finset.mul_sum, anchorScoreEnergy_mass]

/-- Independence and canonical centering remove the complete cross term;
the formula is valid even at the center law's zero atoms. -/
theorem pairedScore_variance_identity (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      pairedScore security score primary center ^ 2) =
      (∑ primary, (primaryLaw security).weight primary * score primary ^ 2) +
        activation security ^ 2 * profileSquareNorm (centerLaw security).weight
          (anchorWeightedScore security score) := by
  have h := independentScore_square (primaryLaw security).weight (centerLaw security).weight
    score (fun center => anchorWeightedScore security score center / (centerLaw security).weight center)
      (activation security)
  simp only [FiniteDist.sum_one, hcentered, mul_one, mul_zero, zero_mul, sub_zero,
    densityScore_square] at h
  simpa only [pairedScore, compensatorScore, mul_div_assoc, densitySquareNorm] using h

/-- The complete actual paired lift has a fixed squared L2 bound, derived
from its actual local laws and their previously proved atom estimates. -/
theorem pairedScore_energy_le (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      pairedScore security score primary center ^ 2) ≤
        129 * ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 := by
  rw [pairedScore_variance_identity security score hcentered]
  have hinput : 0 ≤ ∑ primary, (primaryLaw security).weight primary * score primary ^ 2 :=
    Finset.sum_nonneg (fun primary _ => mul_nonneg ((primaryLaw security).nonneg primary) (sq_nonneg _))
  have hbound := compensator_energy_le security score
  have ha := mul_le_mul_of_nonneg_right (activation_le_half security) hinput
  nlinarith only [hbound, ha]

/-- Exact finite Hilbert tensor extension: the retained coordinates are
summed inside their squared norm, with no coordinate-count factor. -/
theorem pairedScore_finite_hilbert_energy_le {Coordinate : Type*} [Fintype Coordinate]
    (security : ℕ) (score : Palette security → Coordinate → ℝ)
    (hcentered : ∀ coordinate,
      (∑ primary, (primaryLaw security).weight primary * score primary coordinate) = 0) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
      ∑ coordinate, pairedScore security (fun color => score color coordinate) primary center ^ 2) ≤
        129 * ∑ primary, (primaryLaw security).weight primary *
          ∑ coordinate, score primary coordinate ^ 2 := by
  calc
    _ = ∑ primary, ∑ coordinate, ∑ center,
        (primaryLaw security).weight primary * (centerLaw security).weight center *
          pairedScore security (fun color => score color coordinate) primary center ^ 2 := by
      apply Finset.sum_congr rfl
      intro primary _
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ coordinate, ∑ primary, ∑ center,
        (primaryLaw security).weight primary * (centerLaw security).weight center *
          pairedScore security (fun color => score color coordinate) primary center ^ 2 := Finset.sum_comm
    _ ≤ ∑ coordinate, 129 * ∑ primary, (primaryLaw security).weight primary * score primary coordinate ^ 2 :=
      Finset.sum_le_sum (fun coordinate _ => pairedScore_energy_le security
        (fun color => score color coordinate) (hcentered coordinate))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- The full root draw and retained coordinates may occur jointly in
the score. Only its primary coordinate is centered. Averaging retains
that joint input norm and never introduces an inverse root-atom factor. -/
theorem pairedScore_joint_root_energy_le {Root Retained : Type*}
    [Fintype Root] [Fintype Retained]
    (security : ℕ) (rootLaw : FiniteDist Root) (retainedLaw : FiniteDist Retained)
    (score : Root → Retained → Palette security → ℝ)
    (hcentered : ∀ root retained,
      (∑ primary, (primaryLaw security).weight primary * score root retained primary) = 0) :
    (∑ root, rootLaw.weight root * ∑ retained, retainedLaw.weight retained *
      ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security (score root retained) primary center ^ 2) ≤
      129 * ∑ root, rootLaw.weight root * ∑ retained, retainedLaw.weight retained *
        ∑ primary, (primaryLaw security).weight primary * score root retained primary ^ 2 := by
  have hroot (root : Root) :
      (∑ retained, retainedLaw.weight retained *
        ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
          pairedScore security (score root retained) primary center ^ 2) ≤
      129 * ∑ retained, retainedLaw.weight retained *
        ∑ primary, (primaryLaw security).weight primary * score root retained primary ^ 2 := by
    calc
      _ ≤ ∑ retained, retainedLaw.weight retained *
          (129 * ∑ primary, (primaryLaw security).weight primary * score root retained primary ^ 2) :=
        Finset.sum_le_sum (fun retained _ => mul_le_mul_of_nonneg_left
          (pairedScore_energy_le security (score root retained) (hcentered root retained))
          (retainedLaw.nonneg retained))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro retained _
        ring
  calc
    _ ≤ ∑ root, rootLaw.weight root *
        (129 * ∑ retained, retainedLaw.weight retained *
          ∑ primary, (primaryLaw security).weight primary * score root retained primary ^ 2) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left (hroot root) (rootLaw.nonneg root))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro root _
      ring

end

end CurrentAFT.PairedResponse

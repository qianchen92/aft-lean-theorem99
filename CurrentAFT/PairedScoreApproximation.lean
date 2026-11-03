import CurrentAFT.RationalPairedLiftProgram
import CurrentAFT.TensorSupApproximation
import CurrentAFT.SafeControlGroups

/-! # The actual and computed paired operators on arbitrary real scores -/
namespace CurrentAFT.PairedScoreApproximation
open AFT ActualControls ProposalPrimary ControlCoordinates RationalProposalProgram
  RationalPairedLiftProgram DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def pairedLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (anchor : Primary → FiniteDist Body) (rate : ℝ) :
    (Primary → ℝ) →ₗ[ℝ] ((Primary × Body) → ℝ) where
  toFun := ControlCoordinates.pairedLift primary body anchor rate
  map_add' first second := by
    funext point
    simp only [ControlCoordinates.pairedLift, ControlCoordinates.anchorProfile, Pi.add_apply, mul_add,
      add_mul, Finset.sum_add_distrib, add_div]
    ring
  map_smul' scalar score := by
    funext point
    simp only [ControlCoordinates.pairedLift, ControlCoordinates.anchorProfile, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have he : (∑ color, primary.weight color * (scalar * score color) * (anchor color).weight point.2) =
        scalar * ∑ color, primary.weight color * score color * (anchor color).weight point.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    rw [he]
    ring

theorem paired_bound (primary : FiniteDist Primary) (body : FiniteDist Body)
    (anchor : Primary → FiniteDist Body) (rate lower : ℝ) (hlower : 0 < lower)
    (hrate : |rate| ≤ 1) (hbody : ∀ center, lower ≤ body.weight center)
    (score : Primary → ℝ) (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (point : Primary × Body) :
    |pairedLinear primary body anchor rate score point| ≤ (1 + 1 / lower) * bound := by
  have hweight : 0 < body.weight point.2 := hlower.trans_le (hbody point.2)
  have hp := profile_bound primary anchor score bound hscore point.2
  have hproduct := mul_le_mul hrate hp (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
  have hinverse := one_div_le_one_div_of_le hlower (hbody point.2)
  change |score point.1 - rate * ControlCoordinates.anchorProfile primary anchor score point.2 / body.weight point.2| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_div, abs_mul, abs_of_pos hweight]
  calc
    _ ≤ bound + bound / body.weight point.2 := by
      apply add_le_add (hscore _)
      exact div_le_div_of_nonneg_right (hproduct.trans_eq (one_mul bound)) hweight.le
    _ ≤ bound + bound / lower := by
      have h := mul_le_mul_of_nonneg_left hinverse hb
      exact add_le_add le_rfl (by simpa only [mul_one_div] using h)
    _ = _ := by ring

def actual (security : ℕ) := pairedLinear (primaryLaw security) (bodyReference security)
  (anchorReference security) (activation security)
def approximate (security bits : ℕ) := pairedLinear (approximatePrimaryLaw security bits)
  (approximateBodyReference security bits) (approximateAnchorReference security bits)
    (LocalPairProgram.activationApprox security bits)

theorem actual_eq_physical (security : ℕ) (score : ActualControls.Palette security → ℝ)
    (point : SafeControlGroups.SafeGroup security) :
    actual security score point =
      PhysicalSynthesis.pairedChannel security score (SafeControlGroups.unwrap security point) := by
  unfold actual pairedLinear ControlCoordinates.pairedLift ControlCoordinates.anchorProfile
    PhysicalSynthesis.pairedChannel PairedResponse.pairedScore PairedResponse.compensatorScore
    PairedResponse.anchorWeightedScore
  simp only [LinearMap.coe_mk, AddHom.coe_mk, SafeControlGroups.unwrap, bodyReference, anchorReference,
    supportedLaw]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro color _
  ring

theorem actual_bound (security : ℕ) (score : ActualControls.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (point : SafeControlGroups.SafeGroup security) :
    |actual security score point| ≤ (1 + 2 * (Parameters.modulus security : ℝ)) * bound := by
  have hq := FirstResponse.modulus_pos security
  have hrate : |activation security| ≤ 1 := by
    rw [abs_of_pos (activation_pos security)]
    exact (activation_le_half security).trans (by norm_num)
  have h := paired_bound (primaryLaw security) (bodyReference security) (anchorReference security)
    (activation security) (1 / (2 * Parameters.modulus security)) (by positivity)
    hrate (bodyReference_lower security) score bound hb hscore point
  simpa only [one_div_one_div] using h

theorem approximate_bound (security bits : ℕ) (score : ActualControls.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (point : SafeControlGroups.SafeGroup security) :
    |approximate security bits score point| ≤ (1 + 2 * (Parameters.modulus security : ℝ)) * bound := by
  have hq := FirstResponse.modulus_pos security
  have hr := LocalPairProgram.activationApprox_bounds security bits
  have hrate : |(LocalPairProgram.activationApprox security bits : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hr.1)]
    have h : (LocalPairProgram.activationApprox security bits : ℝ) ≤ 1 / 2 := by exact_mod_cast hr.2
    linarith
  have h := paired_bound (approximatePrimaryLaw security bits) (approximateBodyReference security bits)
    (approximateAnchorReference security bits) (LocalPairProgram.activationApprox security bits)
    (1 / (2 * Parameters.modulus security)) (by positivity)
    hrate (RationalProposalProgram.bodyReference_lower security bits) score bound hb hscore point
  simpa only [one_div_one_div] using h

theorem difference (security bits : ℕ) (score : ActualControls.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hscore : ∀ color, |score color| ≤ bound)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ))) (point : SafeControlGroups.SafeGroup security) :
    |approximate security bits score point - actual security score point| ≤
      (errorConstant security / (2 : ℝ)^bits) * bound := by
  have h := reference_error security bits score point.1 point.2 bound hb hscore hprecision hbudget
  exact h.trans_eq (by ring)

end
end CurrentAFT.PairedScoreApproximation

import CurrentAFT.RationalFirstResponseProgram
import CurrentAFT.ControlCoordinates

/-! # The actual paired public score evaluated with one rational reference

The primary, safe center, anchor and activation are the current computed
tables. The error theorem compares their literal score with the actual
paired lift, uniformly in the exposed primary and safe center colors.
-/
namespace CurrentAFT.RationalPairedLiftProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles RationalProposalProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def anchorProfile (security bits : ℕ) (score : ℕ → ℚ) (output : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    primary security bits color.val * score color.val * anchor security bits color.val output

def current (security bits : ℕ) (score : ℕ → ℚ) (primary centerColor : ℕ) : ℚ :=
  score primary - LocalPairProgram.activationApprox security bits * anchorProfile security bits score centerColor /
    center security bits centerColor

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

theorem anchorProfile_cast (security bits : ℕ) (score : ℕ → ℚ) (output : ActualControls.SafePalette security) :
    (anchorProfile security bits score output.val.val : ℝ) =
      ControlCoordinates.anchorProfile (approximatePrimaryLaw security bits) (approximateAnchorReference security bits)
        (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) output := by
  simp only [anchorProfile, Rat.cast_sum, Rat.cast_mul]
  rw [PublicParameterProgram.modulus_value]
  unfold ControlCoordinates.anchorProfile
  apply Finset.sum_congr rfl
  intro color _
  rw [anchor_cast]
  rfl

theorem current_cast (security bits : ℕ) (score : ℕ → ℚ) (primary : FirstHistogram.Palette security)
    (output : ActualControls.SafePalette security) :
    (current security bits score primary.val output.val.val : ℝ) =
      ControlCoordinates.pairedLift (approximatePrimaryLaw security bits) (approximateBodyReference security bits)
        (approximateAnchorReference security bits) (LocalPairProgram.activationApprox security bits)
        (fun color : FirstHistogram.Palette security => (score color.val : ℝ)) (primary, output) := by
  simp only [current, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, anchorProfile_cast, ControlCoordinates.pairedLift]
  rfl

section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem profile_bound (primary : FiniteDist Primary) (anchor : Primary → FiniteDist Body)
    (score : Primary → ℝ) (bound : ℝ) (hscore : ∀ color, |score color| ≤ bound) (output : Body) :
    |ControlCoordinates.anchorProfile primary anchor score output| ≤ bound := by
  unfold ControlCoordinates.anchorProfile
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, primary.weight color*bound := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul, abs_mul, abs_of_nonneg (primary.nonneg color), abs_of_nonneg ((anchor color).nonneg output)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hscore color) (primary.nonneg color))
        ((anchor color).atom_le_one output) ((anchor color).nonneg output)
        (mul_nonneg (primary.nonneg color) ((abs_nonneg _).trans (hscore color)))).trans_eq (mul_one _)
    _ = bound := by rw [← Finset.sum_mul, primary.sum_one, one_mul]

theorem profile_error (primary approximatePrimary : FiniteDist Primary)
    (anchor approximateAnchor : Primary → FiniteDist Body) (score : Primary → ℝ)
    (bound primaryError anchorError : ℝ) (hb : 0 ≤ bound) (hp : 0 ≤ primaryError) (_ha : 0 ≤ anchorError)
    (hscore : ∀ color, |score color| ≤ bound)
    (hprimary : ∀ color, |approximatePrimary.weight color-primary.weight color| ≤ primaryError)
    (hanchor : ∀ color output, |(approximateAnchor color).weight output-(anchor color).weight output| ≤ anchorError)
    (output : Body) :
    |ControlCoordinates.anchorProfile approximatePrimary approximateAnchor score output-
      ControlCoordinates.anchorProfile primary anchor score output| ≤
      (Fintype.card Primary:ℝ)*bound*(primaryError+anchorError) := by
  unfold ControlCoordinates.anchorProfile
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _color : Primary, bound*(primaryError+anchorError) := by
      apply Finset.sum_le_sum
      intro color _
      calc
        _ = |score color*((approximatePrimary.weight color-primary.weight color)*(approximateAnchor color).weight output +
            primary.weight color*((approximateAnchor color).weight output-(anchor color).weight output))| := by congr 1; ring
        _ ≤ |score color| * (|approximatePrimary.weight color-primary.weight color| * (approximateAnchor color).weight output +
            primary.weight color*|(approximateAnchor color).weight output-(anchor color).weight output|) := by
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa only [abs_mul, abs_of_nonneg ((approximateAnchor color).nonneg output),
            abs_of_nonneg (primary.nonneg color)] using abs_add_le
              ((approximatePrimary.weight color-primary.weight color)*(approximateAnchor color).weight output)
              (primary.weight color*((approximateAnchor color).weight output-(anchor color).weight output))
        _ ≤ bound*(primaryError*1+1*anchorError) := by
          apply mul_le_mul (hscore color) _
            (add_nonneg (mul_nonneg (abs_nonneg _) ((approximateAnchor color).nonneg output))
              (mul_nonneg (primary.nonneg color) (abs_nonneg _))) hb
          exact add_le_add (mul_le_mul (hprimary color) ((approximateAnchor color).atom_le_one output)
            ((approximateAnchor color).nonneg output) hp)
            (mul_le_mul (primary.atom_le_one color) (hanchor color output) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    _ = _ := by simp [mul_assoc]

theorem paired_error (primary approximatePrimary : FiniteDist Primary)
    (body approximateBody : FiniteDist Body) (anchor approximateAnchor : Primary → FiniteDist Body)
    (rate approximateRate : ℝ) (score : Primary → ℝ)
    (bound primaryError anchorError bodyError rateError lower : ℝ)
    (hb : 0 ≤ bound) (hp : 0 ≤ primaryError) (ha : 0 ≤ anchorError) (hc : 0 ≤ bodyError) (hr : 0 ≤ rateError)
    (hlower : 0 < lower) (hrate : |rate| ≤ 1)
    (hscore : ∀ color, |score color| ≤ bound)
    (hprimary : ∀ color, |approximatePrimary.weight color-primary.weight color| ≤ primaryError)
    (hanchor : ∀ color output, |(approximateAnchor color).weight output-(anchor color).weight output| ≤ anchorError)
    (hbody : ∀ output, |approximateBody.weight output-body.weight output| ≤ bodyError)
    (hl : ∀ output, lower ≤ body.weight output) (hal : ∀ output, lower ≤ approximateBody.weight output)
    (happroxRate : |approximateRate-rate| ≤ rateError) (input : Primary × Body) :
    |ControlCoordinates.pairedLift approximatePrimary approximateBody approximateAnchor approximateRate score input-
      ControlCoordinates.pairedLift primary body anchor rate score input| ≤
      bound*(rateError/lower + (Fintype.card Primary:ℝ)*(primaryError+anchorError)/lower + bodyError/lower^2) := by
  let first := ControlCoordinates.anchorProfile approximatePrimary approximateAnchor score input.2
  let second := ControlCoordinates.anchorProfile primary anchor score input.2
  let a := approximateBody.weight input.2
  let b := body.weight input.2
  have ha0 : 0 < a := hlower.trans_le (hal input.2)
  have hb0 : 0 < b := hlower.trans_le (hl input.2)
  have hai : a⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hlower (hal input.2)
  have hbi : b⁻¹ ≤ lower⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hlower (hl input.2)
  have hf : |first| ≤ bound := profile_bound _ _ _ _ hscore _
  have hs : |second| ≤ bound := profile_bound _ _ _ _ hscore _
  have hdiff : |first-second| ≤ (Fintype.card Primary:ℝ)*bound*(primaryError+anchorError) :=
    profile_error _ _ _ _ _ _ _ _ hb hp ha hscore hprimary hanchor _
  have hi : |a⁻¹-b⁻¹| ≤ bodyError*lower⁻¹^2 := by
    calc
      _ = |(b-a)*(a⁻¹*b⁻¹)| := by congr 1; field_simp
      _ = |a-b| * (a⁻¹*b⁻¹) := by
        rw [abs_mul, abs_sub_comm b a, abs_of_pos (mul_pos (inv_pos.mpr ha0) (inv_pos.mpr hb0))]
      _ ≤ bodyError*(lower⁻¹*lower⁻¹) :=
        mul_le_mul (hbody input.2) (mul_le_mul hai hbi (inv_nonneg.mpr hb0.le) (inv_nonneg.mpr hlower.le))
          (mul_nonneg (inv_nonneg.mpr ha0.le) (inv_nonneg.mpr hb0.le)) hc
      _ = _ := by ring
  have hd : ControlCoordinates.pairedLift approximatePrimary approximateBody approximateAnchor approximateRate score input-
      ControlCoordinates.pairedLift primary body anchor rate score input =
    -((approximateRate-rate)*first*a⁻¹ + rate*(first-second)*a⁻¹ + rate*second*(a⁻¹-b⁻¹)) := by
    unfold ControlCoordinates.pairedLift
    change score input.1-approximateRate*first/a-(score input.1-rate*second/b) = _
    ring
  rw [hd, abs_neg]
  calc
    _ ≤ |(approximateRate-rate)*first*a⁻¹|+|rate*(first-second)*a⁻¹|+|rate*second*(a⁻¹-b⁻¹)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |approximateRate-rate| * |first| * a⁻¹+|rate| * |first-second| * a⁻¹+|rate| * |second| * |a⁻¹-b⁻¹| := by
      simp only [abs_mul, abs_of_pos (inv_pos.mpr ha0)]
    _ ≤ rateError*bound*lower⁻¹ + 1*((Fintype.card Primary:ℝ)*bound*(primaryError+anchorError))*lower⁻¹ +
        1*bound*(bodyError*lower⁻¹^2) :=
      add_le_add (add_le_add
        (mul_le_mul (mul_le_mul happroxRate hf (abs_nonneg _) hr) hai (inv_nonneg.mpr ha0.le) (mul_nonneg hr hb))
        (mul_le_mul (mul_le_mul hrate hdiff (abs_nonneg _) (by norm_num)) hai (inv_nonneg.mpr ha0.le) (by positivity)))
        (mul_le_mul (mul_le_mul hrate hs (abs_nonneg _) (by norm_num)) hi (abs_nonneg _) (by simpa using hb))
    _ = _ := by ring

end Generic

def errorConstant (security : ℕ) : ℝ :=
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*(Parameters.base security:ℝ)*Parameters.dimension security
  q + 2*q^2*(coefficient+1) + 4*q^2*(coefficient*q+2)

theorem reference_error (security bits : ℕ) (score : FirstHistogram.Palette security → ℝ) (primary : FirstHistogram.Palette security)
    (output : ActualControls.SafePalette security) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color, |score color| ≤ bound)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ))) :
    |ControlCoordinates.pairedLift (approximatePrimaryLaw security bits) (approximateBodyReference security bits)
        (approximateAnchorReference security bits) (LocalPairProgram.activationApprox security bits) score (primary, output) -
      ControlCoordinates.pairedLift (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
        (ActualControls.anchorReference security) (DiffuseProfiles.activation security) score (primary, output)| ≤
      errorConstant security*bound/(2:ℝ)^bits := by
  let epsilon : ℝ := 1/(2:ℝ)^bits
  let q : ℝ := Parameters.modulus security
  let coefficient : ℝ := 64*(Parameters.base security:ℝ)*Parameters.dimension security
  have hq : 0 < q := FirstResponse.modulus_pos security
  have he : 0 ≤ epsilon := by positivity
  have hc : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have hr : |DiffuseProfiles.activation security| ≤ 1 := by
    rw [abs_of_pos (DiffuseProfiles.activation_pos security)]
    exact (DiffuseProfiles.activation_le_half security).trans (by norm_num)
  have hp (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color-(ProposalPrimary.primaryLaw security).weight color| ≤ coefficient*epsilon := by
    simpa only [approximatePrimaryLaw, ProposalPrimary.primaryLaw] using
      (RationalProposalProgram.primary_error security bits color hprecision hbudget)
  have hcenter (color : ActualControls.SafePalette security) :
      |(approximateBodyReference security bits).weight color-(ActualControls.bodyReference security).weight color| ≤
      (coefficient*q+2)*epsilon := RationalProposalProgram.bodyReference_error security bits color hprecision hbudget
  have hrate : |(LocalPairProgram.activationApprox security bits:ℝ)-DiffuseProfiles.activation security| ≤ epsilon/2 :=
    (LocalPairProgram.activationApprox_error security bits).trans_eq (by dsimp only [epsilon]; ring)
  have h := paired_error (ProposalPrimary.primaryLaw security) (approximatePrimaryLaw security bits)
    (ActualControls.bodyReference security) (approximateBodyReference security bits)
    (ActualControls.anchorReference security) (approximateAnchorReference security bits)
    (DiffuseProfiles.activation security) (LocalPairProgram.activationApprox security bits)
    score
    bound (coefficient*epsilon) epsilon ((coefficient*q+2)*epsilon) (epsilon/2) (1/(2*q))
    hb (mul_nonneg hc he) he (by positivity) (by positivity) (by positivity) hr hscore hp
    (RationalProposalProgram.anchorReference_error security bits) hcenter
    (ActualControls.bodyReference_lower security) (RationalProposalProgram.bodyReference_lower security bits) hrate
    (primary, output)
  apply h.trans_eq
  simp only [Fintype.card_fin]
  dsimp only [q, coefficient, epsilon, errorConstant]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring_nf
  simp only [inv_inv]
  ring

theorem current_error (security bits : ℕ) (score : ℕ → ℚ) (primary : FirstHistogram.Palette security)
    (output : ActualControls.SafePalette security) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : FirstHistogram.Palette security, |(score color.val:ℝ)| ≤ bound)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ))) :
    |(current security bits score primary.val output.val.val:ℝ) -
      ControlCoordinates.pairedLift (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
        (ActualControls.anchorReference security) (DiffuseProfiles.activation security)
        (fun color : FirstHistogram.Palette security => (score color.val:ℝ)) (primary, output)| ≤
      errorConstant security*bound/(2:ℝ)^bits := by
  rw [current_cast]
  exact reference_error security bits _ primary output bound hb hscore hprecision hbudget

end
end CurrentAFT.RationalPairedLiftProgram

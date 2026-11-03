import AFT.MarkedSafePair

/-! # Weighted Hilbert energy of the literal four-term primary response -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

theorem profileSquareNorm_four_le (reference first second third fourth : Color → ℝ)
    (hr : ∀ color, 0 ≤ reference color) :
    profileSquareNorm reference (first + second + third - fourth) ≤
      4 * (profileSquareNorm reference first + profileSquareNorm reference second +
        profileSquareNorm reference third + profileSquareNorm reference fourth) := by
  simp only [profileSquareNorm, Pi.add_apply, Pi.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro color _
  have hpoint : (first color + second color + third color - fourth color) ^ 2 ≤
      4 * (first color ^ 2 + second color ^ 2 + third color ^ 2 + fourth color ^ 2) := by
    nlinarith only [sq_nonneg (first color - second color), sq_nonneg (third color + fourth color),
      sq_nonneg (first color + second color - (third color - fourth color))]
  exact (div_le_div_of_nonneg_right hpoint (hr color)).trans_eq (by ring)

theorem profileSquareNorm_reference_comparison (primary reference profile : Color → ℝ)
    (comparison : ℝ) (hp : ∀ color, 0 < primary color) (hr : ∀ color, 0 < reference color)
    (hcompare : ∀ color, primary color ≤ comparison * reference color) :
    profileSquareNorm reference profile ≤ comparison * profileSquareNorm primary profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hr color)).mpr
  have hh := mul_le_mul_of_nonneg_right (hcompare color)
    (div_nonneg (sq_nonneg (profile color)) (hp color).le)
  have heq : primary color * (profile color ^ 2 / primary color) = profile color ^ 2 := by
    field_simp [ne_of_gt (hp color)]
  rw [heq] at hh
  nlinarith only [hh]

/-- The diagonal, sign response, full public anchor, and root compensator
are estimated in the actual output reference norm. -/
theorem four_channel_response_energy (primary reference sign response : Color → ℝ)
    (firstAnchor secondAnchor : Color → Color → ℝ) (activation diagonal majorant l1 anchorCost : ℝ)
    (hp : ∀ color, 0 < primary color) (hpmass : ∑ color, primary color = 1)
    (hr : ∀ color, 0 < reference color)
    (hdiag : ∀ color, primary color ≤ diagonal * reference color)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant) (hv : ∀ color, |response color| ≤ majorant * reference color)
    (hl1 : (∑ color, |response color|) ≤ l1)
    (hfirst0 : ∀ color output, 0 ≤ firstAnchor color output)
    (hsecond0 : ∀ color output, 0 ≤ secondAnchor color output)
    (hfirstMass : ∀ color, ∑ output, firstAnchor color output = 1)
    (hsecondMass : ∀ color, ∑ output, secondAnchor color output = 1)
    (hfirst : ∀ output, applyAnchor firstAnchor primary output ≤ anchorCost * reference output)
    (hsecond : ∀ output, applyAnchor secondAnchor primary output ≤ anchorCost * reference output)
    (profile : Color → ℝ) :
    profileSquareNorm reference
      (activation • profile + (signFunctional sign profile) • response +
        activation • applyAnchor firstAnchor profile - activation • applyAnchor secondAnchor profile) ≤
      4 * (activation ^ 2 * diagonal + majorant * l1 + 2 * activation ^ 2 * anchorCost) *
        profileSquareNorm primary profile := by
  have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  have hd := mul_le_mul_of_nonneg_left
    (profileSquareNorm_reference_comparison primary reference profile diagonal hp hr hdiag) (sq_nonneg activation)
  have h1 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference firstAnchor profile anchorCost hp hr
      hfirst0 hfirstMass hfirst) (sq_nonneg activation)
  have h2 := mul_le_mul_of_nonneg_left
    (applyAnchor_profileSquareNorm_le primary reference secondAnchor profile anchorCost hp hr
      hsecond0 hsecondMass hsecond) (sq_nonneg activation)
  have hvnorm := (signProfile_square_bound reference response majorant hr hv).trans
    (mul_le_mul_of_nonneg_left hl1 hmajorant)
  have hsnorm := mul_le_mul (signFunctional_sq_le primary sign profile hp hpmass hsign)
    hvnorm (profileSquareNorm_nonneg reference response (fun color => (hr color).le)) hn
  have hfour := profileSquareNorm_four_le reference (activation • profile)
    ((signFunctional sign profile) • response) (activation • applyAnchor firstAnchor profile)
    (activation • applyAnchor secondAnchor profile) (fun color => (hr color).le)
  simp only [profileSquareNorm_smul] at hfour
  nlinarith only [hd, h1, h2, hsnorm, hfour]

end
end AFT

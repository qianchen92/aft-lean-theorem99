import AFT.Calibration

/-!
# Finite anchor and paired-lift estimates

These definitions instantiate the local input lift of V7 on finite primary
and safe-center alphabets. The proofs below use the actual anchor matrix
and weighted sums, rather than assuming a bounded lift as a structure field.
-/

namespace AFT

open scoped BigOperators

section FiniteProfiles

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Apply the column-stochastic public anchor law to a signed primary profile. -/
noncomputable def applyAnchor (anchor : ι → κ → ℝ) (profile : ι → ℝ) : κ → ℝ :=
  fun center => ∑ color, anchor color center * profile color

/-- Squared profile norm with respect to a positive reference law. -/
noncomputable def profileSquareNorm (reference profile : ι → ℝ) : ℝ :=
  ∑ color, profile color ^ 2 / reference color

/-- Squared density norm, with the probability weight retained explicitly. -/
noncomputable def densitySquareNorm (reference density : ι → ℝ) : ℝ :=
  ∑ color, reference color * density color ^ 2

/-- The exact paired primary/compensator score in V7 Lemma 9.5. -/
noncomputable def pairedLift (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (activation : ℝ) (profile : ι → ℝ) : ι → κ → ℝ :=
  fun color center => profile color / primary color -
    activation * applyAnchor anchor profile center / body center

theorem applyAnchor_mass (anchor : ι → κ → ℝ) (profile : ι → ℝ)
    (hanchor : ∀ color, ∑ center, anchor color center = 1) :
    (∑ center, applyAnchor anchor profile center) = ∑ color, profile color := by
  simp only [applyAnchor]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hanchor, one_mul]

theorem profileSquareNorm_nonneg (reference profile : ι → ℝ)
    (hreference : ∀ color, 0 ≤ reference color) :
    0 ≤ profileSquareNorm reference profile := by
  exact Finset.sum_nonneg fun color _ => div_nonneg (sq_nonneg _) (hreference color)

theorem densityScore_square (reference profile : ι → ℝ) :
    densitySquareNorm reference (fun color => profile color / reference color) =
      profileSquareNorm reference profile := by
  apply Finset.sum_congr rfl
  intro color _
  dsimp
  field_simp

theorem densityScore_mass (reference profile : ι → ℝ)
    (hreference : ∀ color, reference color ≠ 0) :
    (∑ color, reference color * (profile color / reference color)) = ∑ color, profile color := by
  apply Finset.sum_congr rfl
  intro color _
  field_simp [hreference color]

/-- Independence expands the squared lift into two squared norms and one
explicit cross term. Canonicality will make the cross term vanish. -/
theorem independentScore_square (primary : ι → ℝ) (body : κ → ℝ)
    (left : ι → ℝ) (right : κ → ℝ) (activation : ℝ) :
    (∑ color, ∑ center, primary color * body center *
      (left color - activation * right center) ^ 2) =
    densitySquareNorm primary left * (∑ center, body center) +
      activation ^ 2 * densitySquareNorm body right * (∑ color, primary color) -
      2 * activation * (∑ color, primary color * left color) *
        (∑ center, body center * right center) := by
  calc
    _ = ∑ color, ∑ center,
        ((primary color * left color ^ 2) * body center +
        activation ^ 2 * (body center * right center ^ 2) * primary color -
        (2 * activation * (primary color * left color)) * (body center * right center)) := by
      apply Finset.sum_congr rfl
      intro color _
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, densitySquareNorm]

/-- The two centered directions in the paired lift are exactly orthogonal.
In particular the lift cannot contract the primary profile's L2 norm. -/
theorem pairedLift_square (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (activation : ℝ) (profile : ι → ℝ)
    (hp : ∀ color, primary color ≠ 0)
    (hpmass : ∑ color, primary color = 1) (hsmass : ∑ center, body center = 1)
    (hcanonical : ∑ color, profile color = 0) :
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center ^ 2) =
      profileSquareNorm primary profile +
        activation ^ 2 * profileSquareNorm body (applyAnchor anchor profile) := by
  have h := independentScore_square primary body (fun color => profile color / primary color)
    (fun center => applyAnchor anchor profile center / body center) activation
  simp only [densityScore_square primary profile, densityScore_square body _,
    densityScore_mass primary profile hp, hpmass, hsmass, hcanonical, mul_one,
    mul_zero, zero_mul, sub_zero] at h
  simpa only [pairedLift, mul_div_assoc] using h

omit [Fintype κ] in
/-- Finite weighted Cauchy--Schwarz for a single actual anchor output row. -/
theorem applyAnchor_square_le (primary : ι → ℝ) (anchor : ι → κ → ℝ)
    (profile : ι → ℝ) (hp : ∀ color, 0 < primary color)
    (ha : ∀ color center, 0 ≤ anchor color center) (center : κ) :
    applyAnchor anchor profile center ^ 2 ≤
      applyAnchor anchor primary center *
        ∑ color, anchor color center * (profile color ^ 2 / primary color) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro color _
    exact mul_nonneg (ha color center) (le_of_lt (hp color))
  · intro color _
    exact mul_nonneg (ha color center) (div_nonneg (sq_nonneg _) (le_of_lt (hp color)))
  · intro color _
    have hne := ne_of_gt (hp color)
    field_simp

/-- The anchor lift bound with its genuine finite row comparison.  In V7
`comparison` is `C * q / anchorWidth`, obtained from the safe body lower
bound and the public anchor interval upper bound. -/
theorem applyAnchor_profileSquareNorm_le (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (profile : ι → ℝ) (comparison : ℝ)
    (hp : ∀ color, 0 < primary color) (hs : ∀ center, 0 < body center)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, applyAnchor anchor primary center ≤ comparison * body center) :
    profileSquareNorm body (applyAnchor anchor profile) ≤
      comparison * profileSquareNorm primary profile := by
  calc
    _ ≤ ∑ center, comparison *
        ∑ color, anchor color center * (profile color ^ 2 / primary color) := by
      apply Finset.sum_le_sum
      intro center _
      apply (div_le_iff₀ (hs center)).mpr
      have hnonneg : 0 ≤ ∑ color, anchor color center * (profile color ^ 2 / primary color) :=
        Finset.sum_nonneg fun color _ =>
          mul_nonneg (ha color center) (div_nonneg (sq_nonneg _) (le_of_lt (hp color)))
      have hrow := (applyAnchor_square_le primary anchor profile hp ha center).trans
        (mul_le_mul_of_nonneg_right (hcompare center) hnonneg)
      nlinarith only [hrow]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hamass, one_mul]
      rfl

omit [Fintype κ] in
/-- Uniform interval anchors of width `width` have row bound `1 / width`;
averaging them against the actual normalized primary law preserves this
bound, regardless of how concentrated that primary law is. -/
theorem applyAnchor_primary_upper (primary : ι → ℝ) (anchor : ι → κ → ℝ)
    (upper : ℝ) (hp : ∀ color, 0 ≤ primary color)
    (hmass : ∑ color, primary color = 1)
    (hanchor : ∀ color center, anchor color center ≤ upper) (center : κ) :
    applyAnchor anchor primary center ≤ upper := by
  calc
    _ ≤ ∑ color, upper * primary color := by
      exact Finset.sum_le_sum fun color _ =>
        mul_le_mul_of_nonneg_right (hanchor color center) (hp color)
    _ = _ := by rw [← Finset.mul_sum, hmass, mul_one]

omit [Fintype κ] in
/-- Derive the profile bound's comparison constant from the actual finite
anchor height and body lower bound. This is V7's `q / (c * width)` factor. -/
theorem anchor_body_comparison (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (width modulus bodyConstant : ℝ)
    (hp : ∀ color, 0 ≤ primary color) (hmass : ∑ color, primary color = 1)
    (hwidth : 0 < width) (hmodulus : 0 < modulus) (hconstant : 0 < bodyConstant)
    (hanchor : ∀ color center, anchor color center ≤ 1 / width)
    (hbody : ∀ center, bodyConstant / modulus ≤ body center) (center : κ) :
    applyAnchor anchor primary center ≤ (modulus / (bodyConstant * width)) * body center := by
  refine (applyAnchor_primary_upper primary anchor (1 / width) hp hmass hanchor center).trans ?_
  have hc : 0 ≤ modulus / (bodyConstant * width) := by positivity
  have h := mul_le_mul_of_nonneg_left (hbody center) hc
  have hcancel : modulus / (bodyConstant * width) * (bodyConstant / modulus) = 1 / width := by
    field_simp
  simpa only [hcancel] using h

/-- The paired score's exact L2 lower and upper estimates, stated in squared
form so no square-root or nonnegativity convention is hidden. -/
theorem pairedLift_square_bounds (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (activation comparison : ℝ) (profile : ι → ℝ)
    (hp : ∀ color, 0 < primary color) (hs : ∀ center, 0 < body center)
    (hpmass : ∑ color, primary color = 1) (hsmass : ∑ center, body center = 1)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, applyAnchor anchor primary center ≤ comparison * body center)
    (hcanonical : ∑ color, profile color = 0) :
    profileSquareNorm primary profile ≤
      (∑ color, ∑ center, primary color * body center *
        pairedLift primary body anchor activation profile color center ^ 2) ∧
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center ^ 2) ≤
      (1 + activation ^ 2 * comparison) * profileSquareNorm primary profile := by
  rw [pairedLift_square primary body anchor activation profile
    (fun color => ne_of_gt (hp color))
    hpmass hsmass hcanonical]
  have hn := profileSquareNorm_nonneg body (applyAnchor anchor profile)
    (fun center => le_of_lt (hs center))
  have hu := applyAnchor_profileSquareNorm_le primary body anchor profile comparison
    hp hs ha hamass hcompare
  constructor
  · linarith [mul_nonneg (sq_nonneg activation) hn]
  · nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg activation)]

/-- The exact first moment of independent primary and compensator scores.
This records all four terms before canonicality cancels the two cross terms. -/
theorem independentScore_firstMoment (primary : ι → ℝ) (body : κ → ℝ)
    (left firstResponse : ι → ℝ) (right secondResponse : κ → ℝ) (activation : ℝ) :
    (∑ color, ∑ center, primary color * body center *
      (left color - activation * right center) * (firstResponse color + secondResponse center)) =
    (∑ color, primary color * left color * firstResponse color) * (∑ center, body center) +
      (∑ color, primary color * left color) * (∑ center, body center * secondResponse center) -
      activation * (∑ color, primary color * firstResponse color) *
        (∑ center, body center * right center) -
      activation * (∑ color, primary color) *
        (∑ center, body center * right center * secondResponse center) := by
  calc
    _ = ∑ color, ∑ center,
        ((primary color * left color * firstResponse color) * body center +
          (primary color * left color) * (body center * secondResponse center) -
          (activation * primary color * firstResponse color) * (body center * right center) -
          (activation * primary color) * (body center * right center * secondResponse center)) := by
      apply Finset.sum_congr rfl
      intro color _
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      have hfactor : (∑ color, activation * primary color * firstResponse color) =
          activation * ∑ color, primary color * firstResponse color := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      rw [hfactor]

/-- Applying the actual paired score to additive output counts retains
exactly the primary response and the negative compensating response. -/
theorem pairedLift_firstMoment (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (activation : ℝ) (profile firstResponse : ι → ℝ)
    (secondResponse : κ → ℝ)
    (hp : ∀ color, primary color ≠ 0) (hs : ∀ center, body center ≠ 0)
    (hpmass : ∑ color, primary color = 1) (hsmass : ∑ center, body center = 1)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcanonical : ∑ color, profile color = 0) :
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center *
        (firstResponse color + secondResponse center)) =
      (∑ color, profile color * firstResponse color) -
        activation * ∑ center, applyAnchor anchor profile center * secondResponse center := by
  have h := independentScore_firstMoment primary body
    (fun color => profile color / primary color) firstResponse
    (fun center => applyAnchor anchor profile center / body center) secondResponse activation
  have hprimary (color : ι) : primary color * (profile color / primary color) = profile color := by
    field_simp [hp color]
  have hbody (center : κ) : body center *
      (applyAnchor anchor profile center / body center) = applyAnchor anchor profile center := by
    field_simp [hs center]
  simp only [hprimary, hbody, hpmass, hsmass, applyAnchor_mass anchor profile hamass,
    hcanonical, mul_zero, zero_mul, mul_one, add_zero, sub_zero] at h
  simpa only [pairedLift, mul_div_assoc] using h

/-- The first-response kernel obtained by averaging the actual endpoint
law. The diffuse term is retained explicitly until the canonical input
cancels it. `companion` is the actual blurred public anchor. -/
noncomputable def endpointMeanKernel [DecidableEq ι] (activation : ℝ)
    (companion : ι → ι → ℝ) (diffuse signProfile sign : ι → ℝ) : ι → ι → ℝ :=
  fun primaryColor outputColor =>
    activation * (if outputColor = primaryColor then 1 else 0) +
      activation * companion primaryColor outputColor + diffuse outputColor +
      sign primaryColor * signProfile outputColor

/-- V7's endpoint mean is evaluated against the signed primary input. -/
theorem endpointMeanKernel_response [DecidableEq ι] (activation : ℝ)
    (companion : ι → ι → ℝ) (diffuse signProfile sign profile : ι → ℝ)
    (hcanonical : ∑ color, profile color = 0) (outputColor : ι) :
    (∑ color, profile color *
      endpointMeanKernel activation companion diffuse signProfile sign color outputColor) =
      activation * profile outputColor +
        activation * applyAnchor companion profile outputColor +
        signProfile outputColor * ∑ color, sign color * profile color := by
  simp only [endpointMeanKernel, mul_add, Finset.sum_add_distrib]
  have hdelta : (∑ color, profile color *
      (activation * if outputColor = color then 1 else 0)) = activation * profile outputColor := by
    rw [Finset.sum_eq_single outputColor]
    · simp [mul_comm]
    · intro color _ hc
      simp [Ne.symm hc]
    · simp
  rw [hdelta]
  simp only [← Finset.sum_mul, hcanonical, zero_mul, add_zero]
  have hcomp : (∑ color, profile color * (activation * companion color outputColor)) =
      activation * applyAnchor companion profile outputColor := by
    rw [applyAnchor, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro color _
    ring
  have hsign : (∑ color, profile color * (sign color * signProfile outputColor)) =
      signProfile outputColor * ∑ color, sign color * profile color := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [hcomp, hsign]

/-- Concrete matrix composition of the public anchor with a body blur. -/
noncomputable def blurredAnchor (anchor : ι → κ → ℝ) (blur : κ → ι → ℝ) : ι → ι → ℝ :=
  fun color outputColor => ∑ center, anchor color center * blur center outputColor

theorem blurredAnchor_response (anchor : ι → κ → ℝ) (blur : κ → ι → ℝ)
    (profile : ι → ℝ) (outputColor : ι) :
    applyAnchor (blurredAnchor anchor blur) profile outputColor =
      applyAnchor blur (applyAnchor anchor profile) outputColor := by
  simp only [applyAnchor, blurredAnchor, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro center _
  apply Finset.sum_congr rfl
  intro color _
  ring

/-- The actual paired first response, with the public body blur and the
actual fixed-root compensating shift kept distinct.  This is exactly
`ρ f + v⟨χ,f⟩ + ρ (B - T_source) A f`. -/
theorem paired_first_response [DecidableEq ι] (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (publicBlur actualShift : κ → ι → ℝ)
    (activation : ℝ) (diffuse signProfile sign profile : ι → ℝ)
    (hp : ∀ color, primary color ≠ 0) (hs : ∀ center, body center ≠ 0)
    (hpmass : ∑ color, primary color = 1) (hsmass : ∑ center, body center = 1)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcanonical : ∑ color, profile color = 0) (outputColor : ι) :
    (∑ color, ∑ center, primary color * body center *
      pairedLift primary body anchor activation profile color center *
      (endpointMeanKernel activation (blurredAnchor anchor publicBlur)
        diffuse signProfile sign color outputColor + actualShift center outputColor)) =
      activation * profile outputColor +
        signProfile outputColor * (∑ color, sign color * profile color) +
        activation * (applyAnchor publicBlur (applyAnchor anchor profile) outputColor -
          applyAnchor actualShift (applyAnchor anchor profile) outputColor) := by
  rw [pairedLift_firstMoment primary body anchor activation profile _ _ hp hs hpmass hsmass
    hamass hcanonical]
  rw [endpointMeanKernel_response activation (blurredAnchor anchor publicBlur)
    diffuse signProfile sign profile hcanonical, blurredAnchor_response]
  have hshift : (∑ center, applyAnchor anchor profile center * actualShift center outputColor) =
      applyAnchor actualShift (applyAnchor anchor profile) outputColor := by
    apply Finset.sum_congr rfl
    intro center _
    ring
  rw [hshift]
  ring

end FiniteProfiles

section SignProfile

variable {ι : Type*} [Fintype ι]

/-- The sign functional on an actual finite signed profile. -/
noncomputable def signFunctional (sign profile : ι → ℝ) : ℝ :=
  ∑ color, sign color * profile color

/-- Linear-map form of the finite sign functional, used in the explicit
primary inverse rather than an uninterpreted functional parameter. -/
noncomputable def profileSignMap (sign : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := signFunctional sign
  map_add' first second := by
    simp [signFunctional, mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by
    simp [signFunctional, ← Finset.mul_sum, mul_left_comm]

/-- V7's sign functional is controlled by the actual L1 mass of its input. -/
theorem signFunctional_abs_le_l1 (sign profile : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1) :
    |signFunctional sign profile| ≤ ∑ color, |profile color| := by
  calc
    _ ≤ ∑ color, |sign color * profile color| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hsign color) (abs_nonneg (profile color))

/-- Construct the finite primary rank inverse from the actual sign-profile
L1 smallness used by V7. No inverse or nonzero denominator is assumed. -/
noncomputable def finitePrimaryRankEquiv (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  primaryRankEquiv activation signProfile (profileSignMap sign)
    (ne_of_gt ((Finset.sum_nonneg fun color _ => abs_nonneg (signProfile color)).trans_lt hsmall))
    (ne_of_gt (primaryRank_denominator_pos activation (signFunctional sign signProfile)
      ((signFunctional_abs_le_l1 sign signProfile hsign).trans_lt hsmall)))

/-- The constructed finite inverse has exactly the formula printed in the
local response proof. -/
theorem finitePrimaryRankEquiv_inverse_apply (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) (profile : ι → ℝ) :
    (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm profile =
      profile - ((activation + signFunctional sign signProfile)⁻¹ *
        signFunctional sign profile) • signProfile := by
  exact primaryRankInverse_apply activation signProfile (profileSignMap sign) profile

/-- The bounded sign function has profile-dual norm at most one. -/
theorem signFunctional_sq_le (primary sign profile : ι → ℝ)
    (hp : ∀ color, 0 < primary color) (hpmass : ∑ color, primary color = 1)
    (hsign : ∀ color, |sign color| ≤ 1) :
    signFunctional sign profile ^ 2 ≤ profileSquareNorm primary profile := by
  have hc : signFunctional sign profile ^ 2 ≤
      (∑ color, primary color * sign color ^ 2) * profileSquareNorm primary profile := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _
      exact mul_nonneg (le_of_lt (hp color)) (sq_nonneg _)
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      have hn := ne_of_gt (hp color)
      field_simp
  have hsignsq (color : ι) : sign color ^ 2 ≤ 1 := by
    have h := (abs_le.mp (hsign color))
    nlinarith [sq_nonneg (sign color - 1), sq_nonneg (sign color + 1)]
  have hsum : (∑ color, primary color * sign color ^ 2) ≤ 1 := by
    rw [← hpmass]
    exact Finset.sum_le_sum fun color _ => by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hsignsq color) (le_of_lt (hp color))
  have hfinal := mul_le_mul_of_nonneg_right hsum
    (profileSquareNorm_nonneg primary profile (fun color => le_of_lt (hp color)))
  exact hc.trans (by simpa only [one_mul] using hfinal)

/-- The pointwise calibrated domination and L1 mass bound imply the
weighted L2 sign-profile bound used in the explicit inverse estimate. -/
theorem signProfile_square_bound (primary signProfile : ι → ℝ) (majorant : ℝ)
    (hp : ∀ color, 0 < primary color)
    (hmajorant : ∀ color, |signProfile color| ≤ majorant * primary color) :
    profileSquareNorm primary signProfile ≤ majorant * ∑ color, |signProfile color| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hp color)).mpr
  have h := mul_le_mul_of_nonneg_right (hmajorant color) (abs_nonneg (signProfile color))
  nlinarith [sq_abs (signProfile color)]

/-- Scalar multiplication is evaluated in the actual weighted profile norm. -/
theorem profileSquareNorm_smul (primary profile : ι → ℝ) (scalar : ℝ) :
    profileSquareNorm primary (scalar • profile) = scalar ^ 2 * profileSquareNorm primary profile := by
  simp only [profileSquareNorm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro color _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The nonidentity part of V7's inverse has the advertised small L2 norm
whenever its displayed L1 and pointwise calibrated bounds hold. The exact
constant squared is `majorant * l1 / denominator^2`. -/
theorem rankCorrection_profileSquareNorm_le (primary signProfile sign profile : ι → ℝ)
    (denominator majorant : ℝ) (hp : ∀ color, 0 < primary color)
    (hpmass : ∑ color, primary color = 1) (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color) :
    profileSquareNorm primary ((signFunctional sign profile / denominator) • signProfile) ≤
      (majorant * (∑ color, |signProfile color|) / denominator ^ 2) *
        profileSquareNorm primary profile := by
  rw [profileSquareNorm_smul]
  have hc := signFunctional_sq_le primary sign profile hp hpmass hsign
  have hv := signProfile_square_bound primary signProfile majorant hp hprofile
  have hl1 : 0 ≤ ∑ color, |signProfile color| := Finset.sum_nonneg fun color _ => abs_nonneg _
  calc
    _ ≤ (signFunctional sign profile / denominator) ^ 2 *
        (majorant * ∑ color, |signProfile color|) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = (signFunctional sign profile ^ 2 / denominator ^ 2) *
        (majorant * ∑ color, |signProfile color|) := by rw [div_pow]
    _ ≤ (profileSquareNorm primary profile / denominator ^ 2) *
        (majorant * ∑ color, |signProfile color|) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (sq_nonneg denominator)) (mul_nonneg hmajorant hl1)
    _ = _ := by ring

/-- The inverse's nonidentity part also has the dimension-free density
L2-to-supremum estimate asserted in the local-response proof. -/
theorem rankCorrection_densityNorm_le (primary signProfile sign profile : ι → ℝ)
    (denominator majorant : ℝ) (hp : ∀ color, 0 < primary color)
    (hpmass : ∑ color, primary color = 1) (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color) :
    ‖fun color => (signFunctional sign profile / denominator) * signProfile color /
      primary color‖ ≤ (majorant / |denominator|) * Real.sqrt (profileSquareNorm primary profile) := by
  have hchi : |signFunctional sign profile| ≤ Real.sqrt (profileSquareNorm primary profile) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using signFunctional_sq_le primary sign profile hp hpmass hsign
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (div_nonneg hmajorant (abs_nonneg _)) (Real.sqrt_nonneg _))).mpr
  intro color
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_div, abs_of_pos (hp color)]
  have hrow : |signProfile color| / primary color ≤ majorant :=
    (div_le_iff₀ (hp color)).mpr (hprofile color)
  calc
    _ = (|signFunctional sign profile| / |denominator|) *
        (|signProfile color| / primary color) := by ring
    _ ≤ (|signFunctional sign profile| / |denominator|) * majorant :=
      mul_le_mul_of_nonneg_left hrow (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ (Real.sqrt (profileSquareNorm primary profile) / |denominator|) * majorant :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hchi (abs_nonneg _)) hmajorant
    _ = _ := by ring

end SignProfile

end AFT

import AFT.Inverse

/-!
# Exact finite calibration identities from reference V7

This module defines V7's base primary profile, beta repair, compensated body
profile, and reference mean. The calibration and normalization identities
are checked without assuming the desired identity. The analytic estimates
for the particular Gaussian, anchor, and trimmed-slice profiles remain
separate obligations; arbitrary profiles are not asserted to be positive.
-/

namespace AFT

open scoped BigOperators

section Calibration

variable {ι : Type*}

/-- Total mass of a finite signed color profile. -/
def signedProfileMass [Fintype ι] : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun profile := ∑ color, profile color
  map_add' x y := Finset.sum_add_distrib
  map_smul' scalar x := by simp [← Finset.mul_sum]

@[simp] theorem signedProfileMass_apply [Fintype ι] (profile : ι → ℝ) :
    signedProfileMass profile = ∑ color, profile color := rfl

/-- The exact numerator in equation (9.5), divided by the total mark mass. -/
noncomputable def basePrimaryProfile (dimension bodies legs activation : ℝ)
    (uniform bodyMean shiftedSlice unshiftedSlice : ι → ℝ) : ι → ℝ :=
  fun color => (dimension * uniform color - (bodies + legs * activation) * bodyMean color
    - 2 * legs * shiftedSlice color + 2 * legs * activation * unshiftedSlice color) /
      (legs * activation)

/-- The beta-dependent boundary mass repair. -/
def calibratedPrimaryProfile (base boundaryUniform interiorUniform : ι → ℝ)
    (boundaryMassChange : ℝ) : ι → ℝ :=
  base + boundaryMassChange • (boundaryUniform - interiorUniform)

/-- The compensated body profile. Positivity requires the explicit estimate
proved separately below. -/
def calibratedBodyProfile (core anchorPrimary : ι → ℝ) (compensation : ℝ) : ι → ℝ :=
  (1 + compensation) • core - compensation • anchorPrimary

/-- The diffuse two-endpoint mean in the calibrated model. -/
def diffuseEndpointMean (activation : ℝ) (shiftedSlice unshiftedSlice : ι → ℝ) : ι → ℝ :=
  (2 : ℝ) • shiftedSlice - (2 * activation) • unshiftedSlice

/-- The reference mean specified by the calibrated beta parameter. -/
noncomputable def calibratedReferenceMean (dimension legs activation boundaryMassChange : ℝ)
    (uniform boundaryUniform interiorUniform : ι → ℝ) : ι → ℝ :=
  uniform + (legs * activation * boundaryMassChange / dimension) •
    (boundaryUniform - interiorUniform)

/-- The base calibration exactly solves the mean equation. -/
theorem basePrimaryProfile_mean_identity (dimension bodies legs activation : ℝ)
    (uniform bodyMean shiftedSlice unshiftedSlice : ι → ℝ)
    (hmark : legs * activation ≠ 0) :
    (bodies + legs * activation) • bodyMean +
      legs • diffuseEndpointMean activation shiftedSlice unshiftedSlice +
      (legs * activation) •
        basePrimaryProfile dimension bodies legs activation uniform bodyMean
          shiftedSlice unshiftedSlice = dimension • uniform := by
  have hlegs : legs ≠ 0 := (mul_ne_zero_iff.mp hmark).1
  have hactivation : activation ≠ 0 := (mul_ne_zero_iff.mp hmark).2
  funext color
  simp only [basePrimaryProfile, diffuseEndpointMean, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Including the beta repair gives exactly the reference mean of V7. -/
theorem calibratedPrimaryProfile_mean_identity
    (dimension bodies legs activation boundaryMassChange : ℝ)
    (uniform bodyMean shiftedSlice unshiftedSlice boundaryUniform interiorUniform : ι → ℝ)
    (hmark : legs * activation ≠ 0) (hdimension : dimension ≠ 0) :
    (bodies + legs * activation) • bodyMean +
      legs • diffuseEndpointMean activation shiftedSlice unshiftedSlice +
      (legs * activation) • calibratedPrimaryProfile
        (basePrimaryProfile dimension bodies legs activation uniform bodyMean
          shiftedSlice unshiftedSlice) boundaryUniform interiorUniform boundaryMassChange =
      dimension • calibratedReferenceMean dimension legs activation boundaryMassChange
        uniform boundaryUniform interiorUniform := by
  have hlegs : legs ≠ 0 := (mul_ne_zero_iff.mp hmark).1
  have hactivation : activation ≠ 0 := (mul_ne_zero_iff.mp hmark).2
  funext color
  simp only [basePrimaryProfile, calibratedPrimaryProfile, diffuseEndpointMean,
    calibratedReferenceMean, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Compensation cancels the marked companion's mean before any norm is
estimated; the blur can be any actual linear convolution operator. -/
theorem body_companion_cancellation (bodies legs activation : ℝ)
    (core anchorPrimary : ι → ℝ) (blur : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hbodies : bodies ≠ 0) :
    bodies • blur (calibratedBodyProfile core anchorPrimary (legs * activation / bodies)) +
      (legs * activation) • blur anchorPrimary =
      (bodies + legs * activation) • blur core := by
  simp only [calibratedBodyProfile, map_sub, map_smul, smul_sub, smul_smul]
  have hc : bodies * (legs * activation / bodies) = legs * activation := by
    field_simp
  have hd : bodies * (1 + legs * activation / bodies) = bodies + legs * activation := by
    field_simp
  rw [hc, hd]
  abel

theorem basePrimaryProfile_mass [Fintype ι] (dimension bodies legs activation : ℝ)
    (uniform bodyMean shiftedSlice unshiftedSlice : ι → ℝ)
    (hmark : legs * activation ≠ 0) (hdim : dimension = bodies + 2 * legs)
    (hu : signedProfileMass uniform = 1) (hb : signedProfileMass bodyMean = 1)
    (ht : signedProfileMass shiftedSlice = 1) (ht₀ : signedProfileMass unshiftedSlice = 1) :
    signedProfileMass (basePrimaryProfile dimension bodies legs activation uniform bodyMean
      shiftedSlice unshiftedSlice) = 1 := by
  have h := congrArg signedProfileMass
    (basePrimaryProfile_mean_identity dimension bodies legs activation uniform bodyMean
      shiftedSlice unshiftedSlice hmark)
  simp only [map_add, map_smul, smul_eq_mul, diffuseEndpointMean, map_sub, hu, hb,
    ht, ht₀, mul_one] at h
  apply (mul_left_cancel₀ hmark)
  rw [mul_one]
  nlinarith [h]

theorem calibratedPrimaryProfile_mass [Fintype ι] (base boundaryUniform interiorUniform : ι → ℝ)
    (boundaryMassChange : ℝ) (hbase : signedProfileMass base = 1)
    (hboundary : signedProfileMass boundaryUniform = 1)
    (hinterior : signedProfileMass interiorUniform = 1) :
    signedProfileMass
      (calibratedPrimaryProfile base boundaryUniform interiorUniform boundaryMassChange) = 1 := by
  simp [calibratedPrimaryProfile, map_add, map_sub, map_smul, hbase, hboundary, hinterior]

theorem calibratedBodyProfile_mass [Fintype ι] (core anchorPrimary : ι → ℝ) (compensation : ℝ)
    (hcore : signedProfileMass core = 1) (hanchor : signedProfileMass anchorPrimary = 1) :
    signedProfileMass (calibratedBodyProfile core anchorPrimary compensation) = 1 := by
  simp [calibratedBodyProfile, map_sub, map_smul, hcore, hanchor]

/-- A pointwise positive lower bound for the actual compensated body
formula follows from the anchor upper bound. -/
theorem calibratedBodyProfile_lower_bound (core anchorPrimary : ι → ℝ)
    (compensation upperBound : ℝ) (hcompensation : 0 ≤ compensation)
    (hcore : ∀ color, 0 ≤ core color) (hanchor : ∀ color, anchorPrimary color ≤ upperBound)
    (color : ι) :
    core color - compensation * upperBound ≤
      calibratedBodyProfile core anchorPrimary compensation color := by
  simp only [calibratedBodyProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [hcore color, hanchor color]

/-- The explicit finite numerical condition ensuring nonnegativity. -/
theorem calibratedBodyProfile_nonneg (core anchorPrimary : ι → ℝ)
    (compensation upperBound : ℝ) (hcompensation : 0 ≤ compensation)
    (hcore : ∀ color, 0 ≤ core color) (hanchor : ∀ color, anchorPrimary color ≤ upperBound)
    (hsmall : ∀ color, compensation * upperBound ≤ core color) (color : ι) :
    0 ≤ calibratedBodyProfile core anchorPrimary compensation color := by
  exact (sub_nonneg.mpr (hsmall color)).trans
    (calibratedBodyProfile_lower_bound core anchorPrimary compensation upperBound
      hcompensation hcore hanchor color)

/-- The positivity criterion on the physical safe-center support. Outside
that support both the uniform core and all anchor laws vanish. -/
theorem calibratedBodyProfile_nonneg_supported (safe : Set ι)
    (core anchorPrimary : ι → ℝ) (compensation upperBound : ℝ)
    (hcompensation : 0 ≤ compensation) (hcore : ∀ color, 0 ≤ core color)
    (hanchor : ∀ color, anchorPrimary color ≤ upperBound)
    (hsmall : ∀ color ∈ safe, compensation * upperBound ≤ core color)
    (houtside : ∀ color ∉ safe, core color = 0 ∧ anchorPrimary color = 0)
    (color : ι) : 0 ≤ calibratedBodyProfile core anchorPrimary compensation color := by
  by_cases hc : color ∈ safe
  · exact (sub_nonneg.mpr (hsmall color hc)).trans
      (calibratedBodyProfile_lower_bound core anchorPrimary compensation upperBound
        hcompensation hcore hanchor color)
  · obtain ⟨hcorezero, hanchorzero⟩ := houtside color hc
    simp [calibratedBodyProfile, hcorezero, hanchorzero]

end Calibration

end AFT

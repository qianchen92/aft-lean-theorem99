import AFT.TrimmedPalette
import AFT.ClippedSource
import CurrentAFT.Parameters

/-!
# The actual sign-dependent diffuse endpoint marginals

The interval is the manuscript's inward-anchor interval, and the endpoint
is drawn from the genuine integer trimmed slice, with its varying slice
denominator. The finite seed jointly records the independent public blur
and protected second input. No circular-window replacement is made.
-/

namespace CurrentAFT.DiffuseProfiles

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*} [Fintype Seed]

/-- Positive sign uses `[width,2*width)`. Negative sign uses
`[-2*width+1,-width+1)`, the reflection of the same uniform integer set. -/
def intervalStart (positive : Bool) (width : ℕ) (blur : ℤ) : ℤ :=
  (if positive then (width : ℤ) else -2 * (width : ℤ) + 1) + blur

/-- The full diffuse marginal includes public blur and the protected
second leg input before averaging. -/
def profile (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ) : Fin modulus → ℝ :=
  fun color => TrimmedSlice.mixedLaw modulus trim
    (fun seed => intervalStart positive width (blur seed)) second seedLaw.weight width color.val

theorem interval_bound (positive : Bool) (width : ℕ)
    (blur blurBound shift : ℤ) (hblur : |blur| ≤ blurBound)
    (hshift : shift ∈ anchorInterval (intervalStart positive width blur) width) :
    |shift| ≤ 2 * (width : ℤ) + blurBound := by
  simp only [anchorInterval, Finset.mem_Ico, intervalStart] at hshift
  have hb := abs_le.mp hblur
  cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hshift <;>
    apply abs_le.mpr <;> constructor <;> omega

theorem profile_nonneg (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ) (color : Fin modulus) :
    0 ≤ profile modulus width trim positive seedLaw blur second color :=
  TrimmedSlice.mixedLaw_nonneg _ _ _ _ _ _ _ seedLaw.nonneg

theorem profile_mass (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width) (htrim : 0 ≤ trim)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus) :
    ∑ color, profile modulus width trim positive seedLaw blur second color = 1 := by
  exact TrimmedSlice.mixedLaw_palette_mass modulus trim (2 * (width : ℤ) + blurBound)
    secondBound width hwidth.ne' _ second seedLaw.weight seedLaw.sum_one htrim
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega)

theorem profile_upper (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus)
    (color : Fin modulus) :
    profile modulus width trim positive seedLaw blur second color ≤
      1 / ((modulus : ℝ) - (2 * (trim : ℝ) + 2 * width + blurBound + secondBound)) := by
  have h := TrimmedSlice.mixedLaw_le modulus trim (2 * (width : ℤ) + blurBound)
    secondBound _ second seedLaw.weight width hwidth.ne' seedLaw.nonneg seedLaw.sum_one
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega) color.val
  convert h using 1; push_cast; ring

theorem profile_l1_uniform (modulus width : ℕ) (trim : ℤ) (positive : Bool)
    (seedLaw : FiniteDist Seed) (blur second : Seed → ℤ)
    (blurBound secondBound : ℤ) (hwidth : 0 < width) (htrim : 0 ≤ trim)
    (hblur : ∀ seed, |blur seed| ≤ blurBound)
    (hsecond : ∀ seed, |second seed| ≤ secondBound)
    (hclear : 2 * trim + 2 * (width : ℤ) + blurBound + secondBound < modulus) :
    (∑ color : Fin modulus, |profile modulus width trim positive seedLaw blur second color -
      (modulus : ℝ)⁻¹|) ≤
      2 * (2 * (trim : ℝ) + 2 * width + blurBound + secondBound) / modulus := by
  have h := TrimmedSlice.mixedLaw_palette_l1_le modulus trim (2 * (width : ℤ) + blurBound)
    secondBound width hwidth.ne' _ second seedLaw.weight seedLaw.nonneg seedLaw.sum_one htrim
    (fun seed shift hs => interval_bound positive width _ _ _ (hblur seed) hs)
    hsecond (by omega)
  convert h using 1; push_cast; ring

/-- The protected scalar law is the actual clipped Gaussian at the current
public width and strict cutoff, not the older V7 activation model. -/
def scalarLaw (security : ℕ) :
    FiniteDist (GaussianSource.Window (Parameters.sourceCutoff security - 1)) :=
  GaussianSource.windowGaussian (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1)

/-- The public blur is the difference of two independently drawn protected
edge scalars, exactly the one-coordinate body-cycle marginal. -/
def edgeCutoff (security : ℕ) : ℕ := (Parameters.sourceCutoff security - 1) / 2

def edgeLaw (security : ℕ) : FiniteDist (GaussianSource.Window (edgeCutoff security)) :=
  GaussianSource.windowGaussian (Parameters.sourceWidth security) (edgeCutoff security)

abbrev ActualSeed (security : ℕ) :=
  (GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security)) ×
    GaussianSource.Window (Parameters.sourceCutoff security - 1)

def actualSeedLaw (security : ℕ) : FiniteDist (ActualSeed security) :=
  ((edgeLaw security).prod (edgeLaw security)).prod (scalarLaw security)

def actualBlur (security : ℕ) (seed : ActualSeed security) : ℤ := seed.1.1 - seed.1.2

def actualSecond (security : ℕ) (seed : ActualSeed security) : ℤ := seed.2

def actualProfile (security : ℕ) (positive : Bool) : Fin (Parameters.modulus security) → ℝ :=
  profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)

theorem actualBlur_bound (security : ℕ) (seed : ActualSeed security) :
    |actualBlur security seed| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h1 := Finset.mem_Icc.mp seed.1.1.property
  have h2 := Finset.mem_Icc.mp seed.1.2.property
  have hcut : 0 < Parameters.sourceCutoff security := by
    unfold Parameters.sourceCutoff
    exact pow_pos (Parameters.base_pos security) _
  unfold actualBlur edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem actualSecond_bound (security : ℕ) (seed : ActualSeed security) :
    |actualSecond security seed| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h := Finset.mem_Icc.mp seed.2.property
  have hcut : 0 < Parameters.sourceCutoff security := by
    unfold Parameters.sourceCutoff
    exact pow_pos (Parameters.base_pos security) _
  unfold actualSecond
  apply abs_le.mpr
  constructor <;> omega

/-- The manuscript's conservative deletion length. -/
def deletion (security : ℕ) : ℕ :=
  2 + 2 * Parameters.anchorWidth security + 2 * Parameters.sourceCutoff security

theorem anchorWidth_eq (security : ℕ) : Parameters.anchorWidth security =
    Parameters.base security ^ 48 := by
  simp [Parameters.anchorWidth, Parameters.scale, ← pow_mul]

theorem deletion_clearance (security : ℕ) : deletion security < Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security := (by have := Parameters.base_ge_two security; omega)
  have ha : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    rw [anchorWidth_eq]
    exact Nat.pow_le_pow_right hb (by omega)
  have hc : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (by omega)
  have hp : 1 ≤ Parameters.base security ^ 64 := one_le_pow₀ hb
  have hq := (Parameters.modulus_bounds security).1
  unfold deletion
  omega

private theorem actual_clearance (security : ℕ) :
    2 * (1 : ℤ) + 2 * Parameters.anchorWidth security +
      ((Parameters.sourceCutoff security : ℤ) - 1) +
        ((Parameters.sourceCutoff security : ℤ) - 1) < Parameters.modulus security := by
  have h := deletion_clearance security
  unfold deletion at h
  omega

theorem actualProfile_mass (security : ℕ) (positive : Bool) :
    ∑ color, actualProfile security positive color = 1 := by
  apply profile_mass _ _ _ _ _ _ _
    ((Parameters.sourceCutoff security : ℤ) - 1)
      ((Parameters.sourceCutoff security : ℤ) - 1)
  · rw [anchorWidth_eq]
    exact pow_pos (Parameters.base_pos security) _
  · norm_num
  · exact actualBlur_bound security
  · exact actualSecond_bound security
  · exact actual_clearance security

theorem actualProfile_upper (security : ℕ) (positive : Bool)
    (color : Fin (Parameters.modulus security)) :
    actualProfile security positive color ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  have h := profile_upper (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)
    ((Parameters.sourceCutoff security : ℤ) - 1) ((Parameters.sourceCutoff security : ℤ) - 1)
    (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _)
    (actualBlur_bound security) (actualSecond_bound security) (actual_clearance security) color
  apply h.trans
  apply one_div_le_one_div_of_le
  · exact sub_pos.mpr (Nat.cast_lt.mpr (deletion_clearance security))
  · simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_natCast,
      Int.cast_one]
    linarith

theorem actualProfile_l1_uniform (security : ℕ) (positive : Bool) :
    (∑ color : Fin (Parameters.modulus security), |actualProfile security positive color -
      (Parameters.modulus security : ℝ)⁻¹|) ≤
      2 * (deletion security : ℝ) / Parameters.modulus security := by
  have h := profile_l1_uniform (Parameters.modulus security) (Parameters.anchorWidth security) 1 positive
    (actualSeedLaw security) (actualBlur security) (actualSecond security)
    ((Parameters.sourceCutoff security : ℤ) - 1) ((Parameters.sourceCutoff security : ℤ) - 1)
    (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _) (by norm_num)
    (actualBlur_bound security) (actualSecond_bound security) (actual_clearance security)
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_sub, Int.cast_natCast,
    Int.cast_one]
  linarith

/-- The marked activation is one half of the actual clipped scalar's zero atom. -/
def activation (security : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (scalarLaw security).weight
    (GaussianSource.windowZero (Parameters.sourceCutoff security - 1))

theorem activation_pos (security : ℕ) : 0 < activation security :=
  mul_pos (by norm_num) (GaussianSource.windowGaussian_positive _ _ _)

theorem activation_le_half (security : ℕ) : activation security ≤ 1 / 2 := by
  have h := Finset.single_le_sum (f := (scalarLaw security).weight)
    (fun point _ => (scalarLaw security).nonneg point)
    (Finset.mem_univ (GaussianSource.windowZero (Parameters.sourceCutoff security - 1)))
  rw [FiniteDist.sum_one] at h
  unfold activation
  linarith

theorem activation_lower (security : ℕ) :
    1 / (2 * (1 + 2 / Real.pi) * Parameters.base security) ≤ activation security := by
  have h := GaussianSource.windowGaussian_zero_lower (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1)
    (by exact_mod_cast (show 1 ≤ Parameters.base security by
      have := Parameters.base_ge_two security; omega))
  change 1 / (2 * (1 + 2 / Real.pi) * Parameters.base security) ≤
    (1 / 2 : ℝ) * (GaussianSource.windowGaussian (Parameters.sourceWidth security)
      (Parameters.sourceCutoff security - 1)).weight _
  calc
    _ = (1 / 2 : ℝ) * (1 / ((1 + 2 / Real.pi) * Parameters.sourceWidth security)) := by
      simp only [Parameters.sourceWidth, one_div, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The concrete rank-one numerator of the first histogram response. -/
def signProfile (security : ℕ) : Fin (Parameters.modulus security) → ℝ :=
  fun color => (1 - activation security) *
    (actualProfile security true color - actualProfile security false color)

theorem signProfile_mass (security : ℕ) : ∑ color, signProfile security color = 0 := by
  simp only [signProfile, ← Finset.mul_sum, Finset.sum_sub_distrib, actualProfile_mass,
    sub_self, mul_zero]

theorem signProfile_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    |signProfile security color| ≤ 1 / ((Parameters.modulus security : ℝ) - deletion security) := by
  have h1 := actualProfile_upper security true color
  have h2 := actualProfile_upper security false color
  have hn1 := profile_nonneg (Parameters.modulus security) (Parameters.anchorWidth security) 1 true
    (actualSeedLaw security) (actualBlur security) (actualSecond security) color
  have hn2 := profile_nonneg (Parameters.modulus security) (Parameters.anchorWidth security) 1 false
    (actualSeedLaw security) (actualBlur security) (actualSecond security) color
  change 0 ≤ actualProfile security true color at hn1
  change 0 ≤ actualProfile security false color at hn2
  have ha0 := (activation_pos security).le
  have ha1 := activation_le_half security
  rw [signProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
  have hdiff : |actualProfile security true color - actualProfile security false color| ≤
      1 / ((Parameters.modulus security : ℝ) - deletion security) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - activation security ≤ 1)
    (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff)

theorem signProfile_l1 (security : ℕ) :
    (∑ color, |signProfile security color|) ≤
      4 * (deletion security : ℝ) / Parameters.modulus security := by
  have hdiff := Finset.sum_le_sum (s := Finset.univ) (fun color _ =>
    abs_sub_le (actualProfile security true color) ((Parameters.modulus security : ℝ)⁻¹)
      (actualProfile security false color))
  simp_rw [abs_sub_comm ((Parameters.modulus security : ℝ)⁻¹)] at hdiff
  rw [Finset.sum_add_distrib] at hdiff
  have h1 := actualProfile_l1_uniform security true
  have h2 := actualProfile_l1_uniform security false
  have ha0 := (activation_pos security).le
  have ha1 := activation_le_half security
  calc
    _ = (1 - activation security) *
        ∑ color, |actualProfile security true color - actualProfile security false color| := by
      simp only [signProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security),
        Finset.mul_sum]
    _ ≤ ∑ color, |actualProfile security true color - actualProfile security false color| := by
      nlinarith [Finset.sum_nonneg (fun color (_ : color ∈ Finset.univ) =>
        abs_nonneg (actualProfile security true color - actualProfile security false color))]
    _ ≤ _ := (hdiff.trans (add_le_add h1 h2)).trans_eq (by ring)

end

end CurrentAFT.DiffuseProfiles

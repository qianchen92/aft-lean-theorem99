import AFT.CoreCenteringDifference
import AFT.SmoothingDifference

/-! # Uniform canonical projection commutes with actual finite smoothing -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable def uniformCanonical : Module.End ℝ (G × G → ℝ) where
  toFun profile color := SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
    (fun x y => profile (x, y)) color.1 color.2
  map_add' first second := by
    funext color
    simp only [SafePair.canonicalPair, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar profile := by
    funext color
    simp only [SafePair.canonicalPair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

omit [AddCommGroup G] [DecidableEq G] in
@[simp] theorem uniformCanonical_apply (profile : G × G → ℝ) (color : G × G) :
    uniformCanonical profile color = SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
      (fun x y => profile (x, y)) color.1 color.2 := rfl

omit [DecidableEq G] in
theorem uniformCanonical_translation (profile : G × G → ℝ) (shift : G × G) :
    uniformCanonical (fun color => profile (color - shift)) = fun color => uniformCanonical profile (color - shift) := by
  funext color
  simp only [uniformCanonical_apply, SafePair.canonicalPair]
  have hfirst (second : G) : (∑ first, profile (first - shift.1, second - shift.2)) =
      ∑ first, profile (first, second - shift.2) := translated_sum (fun first => profile (first, second - shift.2)) shift.1
  have hsecond (first : G) : (∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ second, profile (first - shift.1, second) := translated_sum (fun second => profile (first - shift.1, second)) shift.2
  have htotal : (∑ first, ∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ first, ∑ second, profile (first, second) := by
    simp_rw [hsecond]
    exact translated_sum (fun first => ∑ second, profile (first, second)) shift.1
  change profile (color.1 - shift.1, color.2 - shift.2) - 1 / (Fintype.card G : ℝ) *
    (∑ x, profile (x - shift.1, color.2 - shift.2)) -
    (∑ x, profile (color.1 - shift.1, x - shift.2)) * (1 / (Fintype.card G : ℝ)) +
    (∑ x, ∑ y, profile (x - shift.1, y - shift.2)) * (1 / (Fintype.card G : ℝ)) * (1 / (Fintype.card G : ℝ)) = _
  rw [hfirst, hsecond, htotal]
  rfl

omit [DecidableEq G] in
theorem uniformCanonical_commute (kernel : G × G → ℝ) : Commute uniformCanonical (convolution kernel) := by
  apply LinearMap.ext
  intro profile
  funext color
  have hrepr : convolution kernel profile = ∑ shift, kernel shift • (fun point => profile (point - shift)) := by
    funext point
    simp only [convolution_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change uniformCanonical (convolution kernel profile) color = convolution kernel (uniformCanonical profile) color
  rw [hrepr, map_sum]
  simp only [map_smul, uniformCanonical_translation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, convolution_apply]

/-- Uniform canonicalization is the exact counting-Hilbert orthogonal
projection, including for a signed non-product joint profile. -/
theorem uniformCanonical_L2_le (profile : G × G → ℝ) :
    countingL2 (uniformCanonical profile) ≤ countingL2 profile := by
  have hh := SafePair.coreSeed_square_le (Finset.univ : Finset G) (fun x y => profile (x, y)) Finset.univ_nonempty
  simp only [SafePair.coreSeed, SafePair.canonicalPair, SafePair.restrictPair, uniformFiniteProfile, Finset.mem_univ, and_self,
    if_true, Finset.card_univ] at hh
  apply Real.sqrt_le_sqrt
  simpa only [Fintype.sum_prod_type, uniformCanonical_apply, SafePair.canonicalPair, one_div] using hh

/-- The actual smoothed core seed differs from the desired canonical pair
by exactly the core-centering error, the retained smoothing error, and the
deleted edge error. Each is measured before any parameter simplification. -/
theorem smoothed_core_error_L2_le (source : FiniteDist (G × G)) (core : Finset G)
    (mass : G → G → ℝ) (order : ℕ) :
    let original := fun color : G × G => mass color.1 color.2
    let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
    let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
    countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤
      countingL2 (seed - uniformCanonical restricted) +
      order * countingL2 (convolution source.weight restricted - restricted) +
      countingL2 (restricted - original) := by
  dsimp only
  let original := fun color : G × G => mass color.1 color.2
  let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
  let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
  have hc := (uniformCanonical_commute source.weight).pow_right order
  have hcomm : (convolution source.weight ^ order) (uniformCanonical restricted) =
      uniformCanonical ((convolution source.weight ^ order) restricted) := by
    have hh := congrArg (fun operator : Module.End ℝ (G × G → ℝ) => operator restricted) hc.eq
    simpa only [Module.End.mul_apply] using hh.symm
  have heq : (convolution source.weight ^ order) seed - uniformCanonical original =
      (convolution source.weight ^ order) (seed - uniformCanonical restricted) +
      uniformCanonical ((convolution source.weight ^ order) restricted - restricted) +
      uniformCanonical (restricted - original) := by
    simp only [map_sub]
    rw [hcomm]
    abel
  change countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤ _
  rw [heq]
  exact (countingL2_add _ _).trans ((add_le_add
    ((countingL2_add _ _).trans (add_le_add (probability_power_L2_le source order _)
      ((uniformCanonical_L2_le _).trans (probability_power_error_L2_le source restricted order))))
    (uniformCanonical_L2_le _)))

end AFT.SafeConvolution

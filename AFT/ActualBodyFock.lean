import AFT.SingletonFock
import AFT.ActualRootBudget

/-! # The actual shifted safe-body input has its required Fock scale -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts LocalTensors
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualBodyFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem integerShiftProfile_square (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    integerShiftProfile parameter profile shift output ^ 2 =
      integerShiftProfile parameter (fun center => profile center ^ 2) shift output := by
  by_cases ht : ∃ center : Fin (Parameters.modulus parameter), (output.val : ℤ) = (center.val : ℤ) + shift
  · obtain ⟨center, hc⟩ := ht
    have heq (other : Fin (Parameters.modulus parameter)) :
        (output.val : ℤ) = (other.val : ℤ) + shift ↔ other = center := by
      constructor
      · intro hh
        apply paletteInteger_injective parameter
        change (other.val : ℤ) = center.val
        omega
      · rintro rfl
        exact hc
    simp only [integerShiftProfile, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hn (center : Fin (Parameters.modulus parameter)) :
        ¬ (output.val : ℤ) = (center.val : ℤ) + shift := fun hh => ht ⟨center, hh⟩
    simp only [integerShiftProfile, if_neg (hn _), Finset.sum_const_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

/-- Integer translation contracts counting energy, even when values leave
its finite alphabet. Physical safe inputs separately preserve their mass. -/
theorem integerShiftProfile_counting_energy_le (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) :
    (∑ output, integerShiftProfile parameter profile shift output ^ 2) ≤ ∑ center, profile center ^ 2 := by
  simp only [integerShiftProfile_square]
  exact integerShiftProfile_mass_le parameter _ (fun _ => sq_nonneg _) shift

/-- The actual scalar signed body response at a realized integer shift. -/
def actualBodySignedProfile (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (input : Fin (Parameters.modulus parameter) → ℝ) (shift : ℤ) : Fin (Parameters.modulus parameter) → ℝ :=
  integerShiftProfile parameter (fun center => (actualBodyLaw cutoffScale parameter beta).weight center * input center) shift

/-- The true body response has an absolute weighted Hilbert bound; the
reference lower bound and actual body height cancel the palette cardinality. -/
theorem actual_body_signed_profile_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ input : Fin (Parameters.modulus parameter) → ℝ, ∀ shift : ℤ,
      profileSquareNorm (actualReferenceLaw cutoffScale parameter (beta parameter)).weight
        (actualBodySignedProfile cutoffScale parameter (beta parameter) input shift) ≤
      8 * (actualBodyLaw cutoffScale parameter (beta parameter)).l2Sq input := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hl hr hb input shift
  let q : ℝ := Parameters.modulus parameter
  let law := actualBodyLaw cutoffScale parameter (beta parameter)
  let response := actualBodySignedProfile cutoffScale parameter (beta parameter) input shift
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hp (color) : law.weight color ≤ 4 / q := by
    change (actualBodyLaw cutoffScale parameter (beta parameter)).weight color ≤ _
    rw [hl.2.1]
    exact (hb.2.1 color).2.trans ((mul_le_mul_of_nonneg_left ((actualCoreLaw_bounds parameter).1 color)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by dsimp only [q]; ring))
  have hcount : (∑ color, response color ^ 2) ≤ (4 / q) * law.l2Sq input := by
    apply (integerShiftProfile_counting_energy_le parameter (fun color => law.weight color * input color) shift).trans
    unfold FiniteDist.l2Sq FiniteDist.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro color _
    have hh := mul_le_mul_of_nonneg_right (hp color) (mul_nonneg (law.nonneg color) (sq_nonneg (input color)))
    nlinarith only [hh]
  have href (color) : 1 / (2 * q) ≤ (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    exact hr color
  have hinv (color) : 1 / (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color ≤ 2 * q := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1 / (2 * q)) (href color)
    exact hh.trans_eq (by field_simp)
  calc
    _ ≤ (2 * q) * ∑ color, response color ^ 2 := by
      unfold profileSquareNorm
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro color _
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_left (hinv color) (sq_nonneg (response color))
    _ ≤ (2 * q) * ((4 / q) * law.l2Sq input) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by field_simp; ring

/-- The complete actual canonical body Fock response has squared scale
`lambda^-56`, hence norm scale `lambda^-28` exactly as in Section 9. -/
theorem actual_body_fock_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ input : Fin (Parameters.modulus parameter) → ℝ,
      (actualBodyLaw cutoffScale parameter (beta parameter)).expectation input = 0 → ∀ shift : ℤ,
      |shift| ≤ (maxBodyShift cutoffScale parameter : ℤ) →
      taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter (beta parameter))
        (fun word : Fin 1 → Fin (Parameters.modulus parameter) =>
          actualBodySignedProfile cutoffScale parameter (beta parameter) input shift (word 0))
        (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤
          (256 / (parameter : ℝ) ^ 56) * (actualBodyLaw cutoffScale parameter (beta parameter)).l2Sq input := by
  filter_upwards [actual_body_signed_profile_energy_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    body_support_scales_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter he hl hr hb hs hp input hi shift hshift
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  have hz : (∑ color, actualBodySignedProfile cutoffScale parameter (beta parameter) input shift color) = 0 := by
    unfold actualBodySignedProfile
    rw [integerShiftProfile_mass parameter _ (by
      intro color hc
      rw [hl.2.1, hb.2.2 color hc, zero_mul]) shift (hshift.trans (by exact_mod_cast hs.1))]
    exact hi
  have hh := singleton_tagged_energy_le (actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (actualBodySignedProfile cutoffScale parameter (beta parameter) input shift) hz
    (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)
  let scale := (parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter)
  have hscale0 : 0 ≤ scale := by dsimp only [scale]; positivity
  have hscaleB : scale ≤ 2 / (parameter : ℝ) ^ 28 := by
    apply le_trans _ (actualFockScale_le parameter hp)
    change scale ≤ Real.sqrt 2 * scale
    have hsqrt : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt hscale0]
  have hsquared := (sq_le_sq₀ hscale0 (by positivity)).mpr hscaleB
  calc
    _ ≤ 8 * scale ^ 2 * (8 * (actualBodyLaw cutoffScale parameter (beta parameter)).l2Sq input) :=
      hh.trans (mul_le_mul_of_nonneg_left (he input shift) (by positivity))
    _ ≤ 8 * (2 / (parameter : ℝ) ^ 28) ^ 2 * (8 * (actualBodyLaw cutoffScale parameter (beta parameter)).l2Sq input) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquared (by norm_num))
        (mul_nonneg (by norm_num) (FiniteDist.l2Sq_nonneg _ _))
    _ = _ := by ring

end
end AFT.V7Calibration

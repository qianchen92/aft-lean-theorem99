import AFT.ActualBodyCenterProgram
import AFT.NumericalPairedScore

/-! # Rational entries of the actual public paired-score matrix -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- Projection onto the probability interval prevents numerical overshoot. -/
def probabilityClamp (value : ℚ) : ℚ := min 1 (max 0 value)

/-- The cutoff is polynomial and below every positive actual body atom.
Unsafe atoms retain the exact zero-denominator convention. -/
def actualBodyReciprocalProgram (constant n : ℕ) (beta : ℚ) (center : ℕ) : ℚ :=
  if actualSafeMarginProgram n ≤ center ∧
      center < (ParameterProgram.modulus n).value-actualSafeMarginProgram n then
    (max (actualBodyCenterProgram constant n beta center)
      (1/(4*(ParameterProgram.modulus n).value : ℚ)))⁻¹
  else 0

def actualPairedMatrixProgram (constant n : ℕ) (beta : ℚ) (point mark center : ℕ) : ℚ :=
  (if point=mark then 1 else 0)-
    probabilityClamp (actualActivationApprox constant n n)*
    publicAnchorKernelProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) point center*
    probabilityClamp (actualPrimaryProgram constant n beta point)*
    actualBodyReciprocalProgram constant n beta center

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance pairedMatrixProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem probabilityClamp_bounds (value : ℚ) :
    0 ≤ (probabilityClamp value : ℝ) ∧ (probabilityClamp value : ℝ) ≤ 1 := by
  simp only [probabilityClamp,Rat.cast_min,Rat.cast_max,Rat.cast_one,Rat.cast_zero]
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem probabilityClamp_error (value : ℚ) (target : ℝ) (h0 : 0 ≤ target) (h1 : target ≤ 1) :
    |(probabilityClamp value : ℝ)-target| ≤ |(value : ℝ)-target| := by
  simp only [probabilityClamp,Rat.cast_min,Rat.cast_max,Rat.cast_one,Rat.cast_zero]
  have hu := le_abs_self ((value : ℝ)-target)
  have hd := neg_le_abs ((value : ℝ)-target)
  by_cases hv0 : (value : ℝ) ≤ 0
  · rw [max_eq_left hv0,min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    rw [abs_of_nonpos (by linarith : (0 : ℝ)-target ≤ 0)]
    linarith
  · have hv0' : 0 ≤ (value : ℝ) := (lt_of_not_ge hv0).le
    rw [max_eq_right hv0']
    by_cases hv1 : 1 ≤ (value : ℝ)
    · rw [min_eq_left hv1,abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1-target)]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hv1))]

theorem clippedInverse_error (value target lower : ℝ) (hl : 0 < lower)
    (ht : lower ≤ target) :
    |(max value lower)⁻¹-target⁻¹| ≤ |value-target|/lower^2 := by
  have hm : 0 < max value lower := hl.trans_le (le_max_right _ _)
  have hp : 0 < target := hl.trans_le ht
  have he : |max value lower-target| ≤ |value-target| := by
    have hh := abs_max_sub_max_le_abs value target lower
    simpa only [max_eq_left ht] using hh
  rw [show (max value lower)⁻¹-target⁻¹=(target-max value lower)/(max value lower*target) by field_simp,
    abs_div,abs_of_pos (mul_pos hm hp),abs_sub_comm]
  calc
    _ ≤ |value-target|/(max value lower*target) := div_le_div_of_nonneg_right he (mul_pos hm hp).le
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hl)
      (by simpa only [pow_two] using mul_le_mul (le_max_right value lower) ht hl.le hm.le)

private theorem actualSafeProgram_iff (n : ℕ) (center : Fin (Parameters.modulus n)) :
    (actualSafeMarginProgram n ≤ center.val ∧
      center.val < (ParameterProgram.modulus n).value-actualSafeMarginProgram n) ↔ center∈safePalette n := by
  simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
    TrimmedSlice.mem_slice,actualSafeMarginProgram_eq,ParameterProgram.modulus_value]
  have hs := Parameters.safeSize_positive n
  unfold Parameters.safeSize at hs
  omega

theorem actual_body_reciprocal_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ center : Fin (Parameters.modulus n),
      0 ≤ (actualBodyReciprocalProgram constant n (beta n) center.val : ℝ) ∧
      (actualBodyReciprocalProgram constant n (beta n) center.val : ℝ) ≤ 4*Parameters.modulus n ∧
      |(actualBodyReciprocalProgram constant n (beta n) center.val : ℝ)-
        ((actualBodyLaw constant n (beta n)).weight center)⁻¹| ≤
        16*(Parameters.modulus n : ℝ)^2*actualBodyCenterProgramError n := by
  filter_upwards [actual_body_center_program_eventually constant hc beta hbeta,
    actual_body_center_probability_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta]
    with n happ hbody hl center
  have hq : (0 : ℝ) < Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  rw [hl.2.1]
  by_cases hs : center∈safePalette n
  · have hp : 1/(2*(Parameters.modulus n : ℝ)) ≤ actualBodyCenter constant n (beta n) center := by
      have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds n).2 center hs) (by norm_num : (0 : ℝ) ≤ 2)).trans
        (hbody.2.1 center).1
      convert hh using 1; ring
    have hlo : 0 < 1/(4*(Parameters.modulus n : ℝ)) := by positivity
    have hlow : 1/(4*(Parameters.modulus n : ℝ)) ≤ actualBodyCenter constant n (beta n) center := by
      apply le_trans _ hp
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    rw [actualBodyReciprocalProgram,if_pos ((actualSafeProgram_iff n center).mpr hs)]
    simp only [Rat.cast_inv,Rat.cast_max,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_natCast,ParameterProgram.modulus_value]
    have hm : 0 < max (actualBodyCenterProgram constant n (beta n) center.val : ℝ) (1/(4*Parameters.modulus n)) :=
      hlo.trans_le (le_max_right _ _)
    refine ⟨inv_nonneg.mpr hm.le,?_,?_⟩
    · have hh := one_div_le_one_div_of_le hlo (le_max_right (actualBodyCenterProgram constant n (beta n) center.val : ℝ) _)
      simpa only [one_div,inv_inv] using hh
    · apply (clippedInverse_error _ _ _ hlo hlow).trans
      calc
        _ ≤ actualBodyCenterProgramError n/(1/(4*(Parameters.modulus n : ℝ)))^2 :=
          div_le_div_of_nonneg_right (happ center) (sq_nonneg _)
        _ = _ := by field_simp; ring
  · rw [actualBodyReciprocalProgram,if_neg (fun hh => hs ((actualSafeProgram_iff n center).mp hh))]
    simp only [Rat.cast_zero,hbody.2.2 center hs,inv_zero,sub_self,abs_zero]
    have he := (abs_nonneg _).trans (happ center)
    exact ⟨le_refl _,by positivity,by positivity⟩

def actualPairedMatrixProgramError (n : ℕ) : ℝ :=
  8*(n : ℝ)^40*(1/(2 : ℝ)^n+actualPrimaryProgramError n)+
    64*(n : ℝ)^80*actualBodyCenterProgramError n


theorem actualPairedMatrixProgramError_negligible : Negligible actualPairedMatrixProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert ((hm.add actualPrimaryProgramError_negligible).mul_polynomial 40).const_mul 8 |>.add
    ((actualBodyCenterProgramError_negligible.mul_polynomial 80).const_mul 64) using 1
  funext n
  unfold actualPairedMatrixProgramError
  ring

private theorem product_probability_error (a ap p pp k ea ep : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hpp : 0 ≤ pp) (hpp1 : pp ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1) (hda : |ap-a| ≤ ea) (hdp : |pp-p| ≤ ep) :
    |ap*k*pp-a*k*p| ≤ ea+ep := by
  rw [show ap*k*pp-a*k*p=(ap-a)*(k*pp)+(a*k)*(pp-p) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_of_nonneg hk,abs_of_nonneg hpp,abs_of_nonneg ha]
  have hkp : k*pp ≤ 1 := by nlinarith
  have hak : a*k ≤ 1 := by nlinarith
  exact add_le_add ((mul_le_mul_of_nonneg_left hkp (abs_nonneg _)).trans (by simpa using hda))
    ((mul_le_mul_of_nonneg_right hak (abs_nonneg _)).trans (by simpa using hdp))

/-- Every matrix entry used by the actual paired score is computed without
real-number oracles, including centers where the true body probability is zero. -/
theorem actual_paired_matrix_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ point mark center : Fin (Parameters.modulus n),
      |(actualPairedMatrixProgram constant n (beta n) point.val mark.val center.val : ℝ)-
        pairedPublicMatrix (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
          (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
          (v7Activation constant n) point (mark,center)| ≤ actualPairedMatrixProgramError n := by
  filter_upwards [actual_body_reciprocal_program_eventually constant hc beta hbeta,
    actual_primary_program_eventually constant hc,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    hbeta,eventually_ge_atTop 2] with n hr hp hl hb hn point mark center
  let a : ℝ := v7Activation constant n
  let ap : ℝ := probabilityClamp (actualActivationApprox constant n n)
  let p : ℝ := (actualPrimaryLaw constant n (beta n)).weight point
  let pp : ℝ := probabilityClamp (actualPrimaryProgram constant n (beta n) point.val)
  let k : ℝ := publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) point center.val
  let r : ℝ := ((actualBodyLaw constant n (beta n)).weight center)⁻¹
  let rp : ℝ := actualBodyReciprocalProgram constant n (beta n) center.val
  have ha : 0 ≤ a := (activation_positive _ _ _ _
    (legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) (by omega))).le
  have ha1 : a ≤ 1 := activation_le_one _ _ _ _
  have hp0 : 0 ≤ p := (actualPrimaryLaw constant n (beta n)).nonneg point
  have hp1 : p ≤ 1 := by
    simpa only [(actualPrimaryLaw constant n (beta n)).sum_one] using Finset.single_le_sum
      (fun x (_ : x∈Finset.univ) => (actualPrimaryLaw constant n (beta n)).nonneg x) (Finset.mem_univ point)
  have hpp := probabilityClamp_bounds (actualPrimaryProgram constant n (beta n) point.val)
  have hk : 0 ≤ k := publicAnchorKernel_nonneg _ _ _ _
  have hk1 : k ≤ 1 := by
    have hh := publicAnchorKernelProgram_abs_le_one (Parameters.modulus n) (Parameters.anchorWidth n) point.val center.val
    rw [publicAnchorKernelProgram_cast] at hh
    exact (le_abs_self _).trans hh
  have hda : |ap-a| ≤ 1/(2 : ℝ)^n :=
    (probabilityClamp_error _ _ ha ha1).trans (actualActivationApprox_error constant n n hc (by omega))
  have hdp : |pp-p| ≤ actualPrimaryProgramError n := by
    apply (probabilityClamp_error _ _ hp0 hp1).trans
    simpa only [p,hl.1] using hp (beta n) hb.1 point
  have hnume := product_probability_error a ap p pp k _ _ ha ha1 hpp.1 hpp.2 hk hk1 hda hdp
  have hnum0 : 0 ≤ a*k*p := by positivity
  have hnum1 : a*k*p ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hk,mul_nonneg (sub_nonneg.mpr hp1) (mul_nonneg ha hk)]
  have hre := (hr center).2.2
  have hr0 := (hr center).1
  have hr1 := (hr center).2.1
  have he : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans hdp
  have hbe : 0 ≤ actualBodyCenterProgramError n := by
    unfold actualBodyCenterProgramError
    positivity
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    simpa only [Parameters.security_eq n hn,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
      (show (Parameters.modulus n : ℝ) ≤ 2*(Parameters.security n : ℝ)^40 by exact_mod_cast (Parameters.modulus_bounds n).2)
  have hsame : (point.val=mark.val) ↔ point=mark := Fin.val_inj
  simp only [actualPairedMatrixProgram,Rat.cast_sub,Rat.cast_mul,apply_ite,Rat.cast_one,Rat.cast_zero,
    ParameterProgram.modulus_value,actualAnchorWidthProgram_eq,publicAnchorKernelProgram_cast,hsame,pairedPublicMatrix]
  simp only [div_eq_mul_inv]
  change |((if point=mark then 1 else 0)-ap*k*pp*rp)-((if point=mark then 1 else 0)-a*k*p*r)| ≤ _
  rw [show (if point=mark then 1 else 0)-ap*k*pp*rp-((if point=mark then 1 else 0)-a*k*p*r)=
    -((ap*k*pp-a*k*p)*rp+(a*k*p)*(rp-r)) by ring,abs_neg]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hr0,abs_of_nonneg hnum0]
  have hstep := add_le_add (mul_le_mul hnume hr1 hr0 (by positivity))
    (mul_le_mul hnum1 hre (abs_nonneg _) (by norm_num))
  apply hstep.trans
  simp only [one_mul]
  unfold actualPairedMatrixProgramError
  have hq2 : (Parameters.modulus n : ℝ)^2 ≤ 4*(n : ℝ)^80 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Parameters.modulus n) hq 2
    convert hh using 1; ring
  calc
    _ ≤ (1/(2 : ℝ)^n+actualPrimaryProgramError n)*(4*(2*(n : ℝ)^40))+
        16*(4*(n : ℝ)^80)*actualBodyCenterProgramError n := by gcongr
    _ = _ := by ring


/-- Both the exact and computed entries have a uniform constant bound.
This uses the actual anchor/body comparison, rather than a small-atom inverse bound. -/
theorem actual_paired_matrix_program_bounds_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ point mark center : Fin (Parameters.modulus n),
      |pairedPublicMatrix (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (v7Activation constant n) point (mark,center)| ≤ 773 ∧
      |(actualPairedMatrixProgram constant n (beta n) point.val mark.val center.val : ℝ)| ≤ 774 := by
  filter_upwards [actual_paired_matrix_program_eventually constant hc beta hbeta,
    actual_public_anchor_comparison_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,
    actualPairedMatrixProgramError_negligible 0,eventually_ge_atTop 2]
    with n he hc' herr hn point mark center
  have ha : 0 ≤ v7Activation constant n := (activation_positive _ _ _ _
    (legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) (by omega))).le
  have hr := pairedPublicMatrix_row_le (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
    (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
    (v7Activation constant n) 772 ha (by norm_num) (fun _ _ => publicAnchorKernel_nonneg _ _ _ _) hc' (mark,center)
  have hs := Finset.single_le_sum (f:=fun color => |pairedPublicMatrix
    (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
    (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
    (v7Activation constant n) color (mark,center)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ point)
  have ht : |pairedPublicMatrix (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
      (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
      (v7Activation constant n) point (mark,center)| ≤ 773 := by linarith
  refine ⟨ht,?_⟩
  have hab := abs_add_le
    ((actualPairedMatrixProgram constant n (beta n) point.val mark.val center.val : ℝ)-
      pairedPublicMatrix (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (v7Activation constant n) point (mark,center))
    (pairedPublicMatrix (actualPrimaryLaw constant n (beta n)) (actualBodyLaw constant n (beta n))
      (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
      (v7Activation constant n) point (mark,center))
  simp only [sub_add_cancel] at hab
  have hh := he point mark center
  have hsmall : actualPairedMatrixProgramError n ≤ 1 := by simpa only [pow_zero,div_one] using (le_abs_self _).trans herr
  linarith

end
end AFT.V7Calibration

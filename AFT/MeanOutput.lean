import AFT.PrimarySingletonOutput
import AFT.PairMeanInputs

/-! # Exact evaluation of the actual body and endpoint mean input tables -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def profileForm : (Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun profile := ∑ color, MvPolynomial.C (profile color)*MvPolynomial.X color
  map_add' first second := by simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar profile := by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,RingHom.id_apply,MvPolynomial.smul_eq_C_mul,mul_assoc]

omit [Fintype Color] in
theorem profile_weight_recover (reference profile : Color → ℝ) (bound : ℝ)
    (hbound : ∀ color, |profile color| ≤ bound*reference color) (color : Color) :
    reference color*(profile color/reference color) = profile color := by
  by_cases hz : reference color = 0
  · have hp := hbound color
    rw [hz,mul_zero] at hp
    have hh : profile color = 0 := abs_nonpos_iff.mp hp
    simp [hh]
  · field_simp

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

/-- Every physical body mean table maps exactly to its original centered
integer-shift law under the real leading output channel. -/
theorem actual_body_mean_table_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ shift : ℤ, |shift| ≤ maxBodyShift C n →
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (bodyMeanTable C n (beta n) shift)) =
      profileForm (rootProfileOperator n (integerShiftProfile n (actualBodyCenter C n (beta n)) shift)-
        actualReferenceMean C n (beta n)) := by
  filter_upwards [actual_body_type_power_bounds C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n ht hl hp hn operator hop shift hs
  have htype := ht shift hs
  have hpositive (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by
    rw [hl.1]
    exact (hp.1 color).ne'
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  have hmargin : v7RootCutoff n ≤ Parameters.safeMargin n := by
    simp only [v7RootCutoff,Parameters.safeMargin,Parameters.security_eq n hn]
    omega
  let T := inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
  let L := actualLeadingOutput C n (beta n)
  have hconst (scalar : ℝ) : L (T (MvPolynomial.C scalar)) = MvPolynomial.C scalar := by
    change L (T (algebraMap ℝ _ scalar)) = algebraMap ℝ _ scalar
    rw [T.commutes,L.commutes]
  have hsafe : L (T (MvPolynomial.X (bodyMeanSafeInput C n (beta n) shift))) =
      profileForm (rootProfileOperator n (bodyCanonicalInput C n (beta n) shift)) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,bodyMeanSafeInput,inversePrimarySeed_bodySingleton]
    rw [← hl.2.1]
    apply actualLeadingOutput_safe_body
    · exact profile_weight_recover _ _ 5 (by rw [hl.2.1]; exact htype.2.2.1)
    · exact htype.2.1
    · exact hmargin
  have hout : L (T (MvPolynomial.X (bodyMeanOutsideInput C n (beta n) shift))) =
      profileForm (bodyCenteredOutside C n (beta n) shift) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,bodyMeanOutsideInput]
    rw [← hl.1]
    exact actualLeadingOutput_inverse_primary C n (beta n) operator hop hrho hpositive _
  have hroot : L (T (MvPolynomial.X (rootMeanInput C n (beta n)))) =
      profileForm (actualRootBodyMean n-actualReferenceMean C n (beta n)) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,rootMeanInput]
    unfold rootMeanDifferenceDensity
    rw [← hl.1]
    exact actualLeadingOutput_inverse_primary C n (beta n) operator hop hrho hpositive _
  change L (T (bodyMeanTable C n (beta n) shift)) = _
  simp only [bodyMeanTable,map_add,map_mul,hconst,hsafe,hout,hroot]
  have hid := congrArg (profileForm (Color := Fin (Parameters.modulus n)))
    (body_type_centered_decomposition C n (beta n) shift)
  simp only [map_add,map_smul,MvPolynomial.smul_eq_C_mul] at hid
  exact hid.symm


/-- The two real endpoint marginals are the exact leading image of the
three actual calibrated input seeds. -/
theorem actual_pair_mean_table_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (pairMeanTable C n (beta n))) =
      profileForm (fun color => (∑ second, localPairMixture C n (beta n) color second)+
        (∑ first, localPairMixture C n (beta n) first color)-2*actualReferenceMean C n (beta n) color) := by
  filter_upwards [actual_pair_mean_decomposition_eventually C hC,
    actual_extra_anchor_seed_bounds C hC beta hbeta,
    actual_extra_anchor_seed_power_bounds C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hd he hep hl hp hn operator hop
  have hpositive (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by
    rw [hl.1]
    exact (hp.1 color).ne'
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  have hmargin : v7RootCutoff n ≤ Parameters.safeMargin n := by
    simp only [v7RootCutoff,Parameters.safeMargin,Parameters.security_eq n hn]
    omega
  let T := inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
  let L := actualLeadingOutput C n (beta n)
  have hconst (scalar : ℝ) : L (T (MvPolynomial.C scalar)) = MvPolynomial.C scalar := by
    change L (T (algebraMap ℝ _ scalar)) = algebraMap ℝ _ scalar
    rw [T.commutes,L.commutes]
  have hsafe : L (T (MvPolynomial.X (extraAnchorMeanInput C n (beta n)))) =
      profileForm (rootProfileOperator n (extraAnchorSeed C n (beta n))) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,extraAnchorMeanInput,inversePrimarySeed_bodySingleton]
    rw [← hl.2.1]
    apply actualLeadingOutput_safe_body
    · exact profile_weight_recover _ _ (8*(n : ℝ)^8) (by rw [hl.2.1]; exact hep.2)
    · exact he.2.1
    · exact hmargin
  have hroot : L (T (MvPolynomial.X (rootMeanInput C n (beta n)))) =
      profileForm (actualRootBodyMean n-actualReferenceMean C n (beta n)) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,rootMeanInput]
    unfold rootMeanDifferenceDensity
    rw [← hl.1]
    exact actualLeadingOutput_inverse_primary C n (beta n) operator hop hrho hpositive _
  have hfull : L (T (MvPolynomial.X (fullBodyMeanInput C n (beta n)))) =
      profileForm (actualBodyMean C n-actualReferenceMean C n (beta n)) := by
    simp only [T,inversePrimaryTable,MvPolynomial.aeval_X,fullBodyMeanInput]
    rw [← hl.1]
    exact actualLeadingOutput_inverse_primary C n (beta n) operator hop hrho hpositive _
  change L (T (pairMeanTable C n (beta n))) = _
  simp only [pairMeanTable,map_add,map_mul,hconst,hsafe,hroot,hfull]
  have hid : (fun color => (∑ second,localPairMixture C n (beta n) color second)+
      (∑ first,localPairMixture C n (beta n) first color)-2*actualReferenceMean C n (beta n) color) =
      v7Activation C n • rootProfileOperator n (extraAnchorSeed C n (beta n))+
      v7Activation C n • (actualRootBodyMean n-actualReferenceMean C n (beta n))+
      (-((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)) •
        (actualBodyMean C n-actualReferenceMean C n (beta n)) := by
    funext color
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [hd (beta n) color]
    ring
  rw [hid,map_add,map_add,map_smul,map_smul,map_smul]
  simp only [MvPolynomial.smul_eq_C_mul]

end
end AFT.V7Calibration

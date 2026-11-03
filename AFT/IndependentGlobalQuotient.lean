import AFT.PendingPrimaryExpansion
import AFT.IndependentBodyUpper
import AFT.ReciprocalGrowth

/-! # Literal normalized independent response for an arbitrary joint seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentGlobalQuotientFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentGlobalQuotient (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (depth : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  independentNumeratorTable C n beta operator charts seed *
    (independentPositiveReciprocal C n beta operator charts depth)^seed.primaryOrder *
    (independentBodyReciprocal C n beta operator depth)^seed.bodyOrder

def independentGlobalGrowth (C : ℝ) (n primaryOrder bodyOrder : ℕ) : ℝ :=
  (1+independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ))^primaryOrder *
    (1+2*(independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ)))^primaryOrder *
    (1+2*(independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ)))^bodyOrder

/-- Full joint numerator and both true positive denominators are controlled
before any output evaluation; the original variable cancels literally. -/
theorem independentGlobalQuotient_bounds_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second=
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ depth : ℕ,
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    activity weight (independentGlobalQuotient C n (beta n) operator charts seed depth) ≤
      independentGlobalGrowth C n seed.primaryOrder seed.bodyOrder*weight seed ∧
    activity weight (independentGlobalQuotient C n (beta n) operator charts seed depth-MvPolynomial.X seed) ≤
      (independentGlobalGrowth C n seed.primaryOrder seed.bodyOrder-1)*weight seed := by
  have htyp := htypical.mono fun _ hn => And.intro hn.1 (And.intro hn.2.1 hn.2.2.1)
  have small (constant : ℝ) : ∀ᶠ n : ℕ in atTop,constant/(n : ℝ)^(43/4 : ℝ) ≤ 1/2 :=
    Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/2)
      (((tendsto_rpow_atTop (by norm_num : (0:ℝ)<43/4)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop constant)
  filter_upwards [independentNumeratorTable_bounds_eventually C hC beta pool htypical,
    independentPositiveInputTable_activity_eventually C hC beta pool htyp,
    independentBodyInputTable_activity_eventually C hC beta pool htyp,
    small (independentPositiveInputConstant C),small (independentBodyInputConstant C)]
    with n hnum hp hb hps hbs operator hop charts hcharts bodyPool radius hradius seed hseed depth
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  let delta := independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)
  let ep := 2*(independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ))
  let eb := 2*(independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ))
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have ha := activationConstant_pos C hC
  have hd : 0 ≤ delta := by dsimp [delta,independentJointHigherConstant,independentReferenceHilbertConstant]; positivity
  have hep : 0 ≤ ep := by dsimp [ep,independentPositiveInputConstant]; positivity
  have heb : 0 ≤ eb := by dsimp [eb,independentBodyInputConstant]; positivity
  have hp := hp operator hop charts hcharts bodyPool radius hradius
  have hb := hb operator hop bodyPool radius hradius
  have hpe : activity weight (independentPositiveReciprocal C n (beta n) operator charts depth-1) ≤ ep :=
    (activity_finiteCorrection_sub_one_le weight hw _ depth (hp.trans hps)).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2))
  have hbe : activity weight (independentBodyReciprocal C n (beta n) operator depth-1) ≤ eb :=
    (activity_finiteCorrection_sub_one_le weight hw _ depth (hb.trans hbs)).trans
      (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2))
  have hpp := activity_pow_sub_one_le weight hw _ ep hep hpe seed.primaryOrder
  have hbp := activity_pow_sub_one_le weight hw _ eb heb hbe seed.bodyOrder
  have hpfull : activity weight ((independentPositiveReciprocal C n (beta n) operator charts depth)^seed.primaryOrder) ≤
      (1+ep)^seed.primaryOrder := by
    have hh := activity_le_one_add_of_sub_one weight hw _ _ hpp
    linarith
  have hbfull : activity weight ((independentBodyReciprocal C n (beta n) operator depth)^seed.bodyOrder) ≤
      (1+eb)^seed.bodyOrder := by
    have hh := activity_le_one_add_of_sub_one weight hw _ _ hbp
    linarith
  have hn := hnum operator hop charts hcharts bodyPool radius hradius seed hseed
  have hfirst := activity_mul_perturbation_le weight hw (MvPolynomial.X seed)
    (independentNumeratorTable C n (beta n) operator charts seed)
    ((independentPositiveReciprocal C n (beta n) operator charts depth)^seed.primaryOrder)
    (weight seed) ((1+delta)^seed.primaryOrder) ((1+ep)^seed.primaryOrder)
    (hw seed) (one_le_pow₀ (by linarith)) (by rw [activity_X]) hn.1 hn.2 hpfull hpp
  have hsecond := activity_mul_perturbation_le weight hw (MvPolynomial.X seed)
    (independentNumeratorTable C n (beta n) operator charts seed *
      (independentPositiveReciprocal C n (beta n) operator charts depth)^seed.primaryOrder)
    ((independentBodyReciprocal C n (beta n) operator depth)^seed.bodyOrder)
    (weight seed) ((1+delta)^seed.primaryOrder*(1+ep)^seed.primaryOrder) ((1+eb)^seed.bodyOrder)
    (hw seed) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith)))
    (by rw [activity_X]) hfirst.1 hfirst.2 hbfull hbp
  exact hsecond

theorem independentGlobalQuotient_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)
      Finset.univ seed.kernel → ∀ depth : ℕ,
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentGlobalQuotient C n (beta n) operator charts seed depth) := by
  filter_upwards [independentNumeratorTable_canonical_eventually C hC beta hbeta,
    independentBodyInputTable_canonical_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,actual_reference_laws_eventually C hC beta hbeta,
    actualResponse_inverse_mass_eventually C hC]
    with n hn hb hp hl hm operator hop charts seed hseed depth
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hpositive := referenceCoefficientTable_inverse_canonical (actualPrimaryLaw C n (beta n))
    (actualBodyLaw C n (beta n)) (actualReferenceLaw C n (beta n)) (v7Activation C n)
    operator hp0 (hm operator hop) (independentPairedPositiveMass C n (beta n) charts)
  exact ((hn operator hop charts seed hseed).mul ((hpositive.finiteCorrection depth).pow seed.primaryOrder)).mul
    (((hb operator hop).finiteCorrection depth).pow seed.bodyOrder)

end
end AFT.V7Calibration

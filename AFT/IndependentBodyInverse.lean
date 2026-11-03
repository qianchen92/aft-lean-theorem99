import AFT.IndependentBodyPositive
import AFT.IndependentPositiveInverse

/-! # Literal finite reciprocal of the real reserved-body factor -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentBodyInverseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentBodyInverseSubtypeDecEq (s : Finset (Fin 1)) : DecidableEq s := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentBodyInputConstant (C : ℝ) : ℝ := 768*activationConstant C

def independentBodyInputTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ)) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  referenceInverseTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (actualReferenceLaw C n beta) (v7Activation C n) operator (independentBodyPositiveMass C n beta)

def independentBodyReciprocal (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (depth : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  finiteCorrection (independentBodyInputTable C n beta operator) depth

theorem independentBodyInputTable_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n → ∀ bodyPool radius : ℝ,0 ≤ radius →
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pool n) bodyPool radius) (independentBodyInputTable C n (beta n) operator) ≤
      independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    independentBodyPositive_activity_eventually C hC beta hbeta,htypical,eventually_ge_atTop 2]
    with n hi hh ht hn operator hop bodyPool radius hradius
  obtain ⟨inverse,hinverse,hi⟩ := hi
  have heq : operator=inverse := LinearEquiv.toLinearMap_injective (hop.trans hinverse.symm)
  subst inverse
  let p := actualPrimaryLaw C n (beta n)
  let body := actualBodyLaw C n (beta n)
  let r := actualReferenceLaw C n (beta n)
  let rate : ℝ := 1/Real.sqrt (pool n : ℝ)
  let budget : ℝ := 48*(8*activationConstant C)/(n : ℝ)^(43/4 : ℝ)
  have ha := activationConstant_pos C hC
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hrate := independent_primary_rate_small n (pool n) hn ht.2.2
  have hbudget : 0 ≤ budget := by dsimp [budget]; positivity
  have hselected (selected : Finset (Fin 1)) (hs : selected ≠ ∅) :
      inputWeight p body (pool n) bodyPool radius
        (inversePrimarySeed p body (v7Activation C n) operator
          (referenceCoefficientSeed p r (independentBodyPositiveMass C n (beta n)) selected)) ≤ budget := by
    have hcard : selected.card=1 := by
      have hle := Finset.card_le_univ selected
      have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      simp only [Fintype.card_fin] at hle
      omega
    have hinv := hi body bodyPool radius hradius
      (referenceCoefficientSeed p r (independentBodyPositiveMass C n (beta n)) selected)
    unfold responseInputWeight at hinv
    rw [referenceCoefficientSeed_weight] at hinv
    have horder : (referenceCoefficientSeed p r (independentBodyPositiveMass C n (beta n)) selected).primaryOrder=1 := by
      simp only [referenceCoefficientSeed,primaryFiniteSeed,Fintype.card_coe,hcard]
    rw [horder,pow_one] at hinv
    simp only [← one_div] at hinv
    have hraw := hh selected hs rate hrate.1.le hrate.2.1
    have hbound := hinv.trans (mul_le_mul_of_nonneg_left hraw (div_nonneg (by norm_num) hrho.le))
    have he : (4/v7Activation C n)*(48*rate)=48*independentCoordinateCost C n (pool n) := by
      dsimp [independentCoordinateCost,rate]
      ring
    change _ ≤ (4/v7Activation C n)*(48*rate) at hbound
    rw [he] at hbound
    exact hbound.trans ((mul_le_mul_of_nonneg_left
      (independentCoordinateCost_le C hC n (pool n) hn ht.2.2) (by norm_num : (0:ℝ)≤48)).trans_eq (by
        dsimp [budget]; ring))
  have htable := referenceCoefficientTable_inverse_activity_le p body r (pool n) bodyPool radius
    (v7Activation C n) hradius operator (independentBodyPositiveMass C n (beta n)) (fun _ => budget) hselected
  apply htable.trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 1))).erase ∅).card : ℝ) ≤ 2 := by
    exact_mod_cast ((Finset.card_le_univ ((Finset.univ : Finset (Finset (Fin 1))).erase ∅)).trans_eq (by simp))
  rw [Finset.sum_const,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcard hbudget).trans_eq (by
    dsimp [budget,independentBodyInputConstant]; ring)

theorem independentBodyReciprocal_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n → ∀ bodyPool radius : ℝ,0 ≤ radius → ∀ depth : ℕ,
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pool n) bodyPool radius) (independentBodyReciprocal C n (beta n) operator depth) ≤ 2 := by
  have ht : Tendsto (fun n : ℕ => independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ)) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<43/4)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop _
  have hs := Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/2) ht
  filter_upwards [independentBodyInputTable_activity_eventually C hC beta pool htypical,hs]
    with n h hs operator hop bodyPool radius hradius depth
  exact activity_finiteCorrection_le_two _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _
    ((h operator hop bodyPool radius hradius).trans hs)

theorem independentBodyInputTable_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color) :
    actualLeadingOutput C n beta (independentBodyInputTable C n beta operator)=
      centeredGeneratingLinear (actualReferenceLaw C n beta).weight (independentBodyPositiveMass C n beta)-1 := by
  have hh := actual_referenceCoefficientTable_inverse_image C n beta operator hop hrho hp
    (independentBodyPositiveMass C n beta)
  simpa only [independentBodyPositiveMass_mass,map_one] using hh

theorem independentBodyReciprocal_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,0 < (actualPrimaryLaw C n beta).weight color) (depth : ℕ) :
    actualLeadingOutput C n beta (independentBodyReciprocal C n beta operator depth)=
      finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n beta).weight
        (independentBodyPositiveMass C n beta)-1) depth := by
  simp only [independentBodyReciprocal,finiteCorrection,map_sum,map_pow,map_neg,
    independentBodyInputTable_image C n beta operator hop hrho hp]

theorem independentBodyInputTable_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentBodyInputTable C n (beta n) operator) := by
  filter_upwards [actualResponse_inverse_mass_eventually C hC,
    actual_primary_probability_eventually C hC beta hbeta,actual_reference_laws_eventually C hC beta hbeta]
    with n hm hp hl operator hop
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  exact referenceCoefficientTable_inverse_canonical _ _ _ _ operator hp0 (hm operator hop) _

end
end AFT.V7Calibration

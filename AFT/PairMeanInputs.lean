import AFT.BodyMeanInputs
import AFT.ActualMeanCalibration

/-! # The actual calibrated endpoint first coefficient and its finite inputs -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def extraAnchorMeanInput (C : ℝ) (n : ℕ) (beta : ℝ) : InputSeed (Fin (Parameters.modulus n)) :=
  bodySingletonInput (fun color => extraAnchorSeed C n beta color/actualBodyCenter C n beta color)

def fullBodyMeanInput (C : ℝ) (n : ℕ) (beta : ℝ) : InputSeed (Fin (Parameters.modulus n)) :=
  primarySingletonInput (fun color => (actualBodyMean C n color-actualReferenceMean C n beta color)/actualPrimary C n beta color)

def pairMeanTable (C : ℝ) (n : ℕ) (beta : ℝ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  MvPolynomial.C (v7Activation C n)*MvPolynomial.X (extraAnchorMeanInput C n beta)+
  MvPolynomial.C (v7Activation C n)*MvPolynomial.X (rootMeanInput C n beta)+
  MvPolynomial.C (-((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n))*MvPolynomial.X (fullBodyMeanInput C n beta)

def pairMeanInputConstant (C : ℝ) : ℝ := 2*(Real.sqrt (anchorSeedSquareConstant C)+16)+
  8*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant)+
  24*(Real.sqrt bodyMeanSquareConstant+2*bodyMeanRelativeConstant)

theorem pairMeanTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (pairMeanTable C n beta) := by
  intro powers hp
  unfold pairMeanTable
  rw [MvPolynomial.coeff_add,MvPolynomial.coeff_add,
    hasOrder_C_mul_X (fun s => s.primaryOrder+s.bodyOrder) 1 (extraAnchorMeanInput C n beta) (v7Activation C n) (by rfl) powers hp,
    hasOrder_C_mul_X (fun s => s.primaryOrder+s.bodyOrder) 1 (rootMeanInput C n beta) (v7Activation C n) (by rfl) powers hp,
    hasOrder_C_mul_X (fun s => s.primaryOrder+s.bodyOrder) 1 (fullBodyMeanInput C n beta)
      (-((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)) (by rfl) powers hp]
  norm_num

/-- This is the exact endpoint mean rearrangement forced by calibration;
the anchor contribution remains an actual physical marginal. -/
theorem actual_pair_mean_decomposition_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ beta : ℝ, ∀ color : Fin (Parameters.modulus n),
      (∑ second, localPairMixture C n beta color second)+(∑ first, localPairMixture C n beta first color)-
        2*actualReferenceMean C n beta color =
      v7Activation C n * rootProfileOperator n (extraAnchorSeed C n beta) color+
      v7Activation C n * (actualRootBodyMean n color-actualReferenceMean C n beta color)-
      ((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)*
        (actualBodyMean C n color-actualReferenceMean C n beta color) := by
  filter_upwards [actual_total_mean_eventually C hC,actual_extra_seed_root_image_eventually C hC]
    with n ht he beta color
  have hm : (Parameters.legs n : ℝ) ≠ 0 := by
    have hh : 0 < Parameters.legs n := by unfold Parameters.legs; exact pow_pos (by have := Parameters.security_ge_two n; omega) _
    exact_mod_cast hh.ne'
  have hN : (Parameters.bodies n : ℝ) ≠ 0 := by exact_mod_cast (Parameters.bodies_positive n).ne'
  have hpop : (Parameters.dimension n : ℝ) = Parameters.bodies n+2*Parameters.legs n := by
    exact_mod_cast (Parameters.population_identity n).symm
  have h := ht beta color
  rw [actualFullBodyProfile_formula,hpop] at h
  have ha : (∑ first, actualMarkedPair C n beta first color) =
      blurredAnchorMean (Parameters.modulus n) (Parameters.anchorWidth n)
        (bodyShift C n) (bodyBlur C n) (actualPrimary C n beta) color.val := rfl
  have he' := congrFun (he beta) color
  simp only at he'
  rw [ha] at he'
  rw [he']
  unfold bodyCompensation at h
  field_simp [hm,hN] at h ⊢
  nlinarith

theorem actual_pair_mean_seed_bounds_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n)
        (extraAnchorMeanInput C n (beta n)) ≤ 2*(Real.sqrt (anchorSeedSquareConstant C)+16)/(n : ℝ)^24 ∧
      responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n)
        (fullBodyMeanInput C n (beta n)) ≤ 8*(Real.sqrt bodyMeanSquareConstant+2*bodyMeanRelativeConstant)/(n : ℝ)^46 := by
  filter_upwards [actual_extra_anchor_seed_power_bounds C hC beta hbeta,
    actual_body_mean_bounds C hC beta hbeta,v7Activation_lower_eventually C hC,eventually_ge_atTop 2]
    with n he hf hrho hn primary body hp hb ppool bpool hpp hbp
  let x : ℝ := n
  let a := (Real.sqrt (ppool : ℝ))⁻¹
  let b := (Real.sqrt (bpool : ℝ))⁻¹
  let K := Real.sqrt (anchorSeedSquareConstant C)
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have ha := covariance_pool_rate n ppool hn hpp
  have hbb := body_pair_pool_rate n bpool hn hbp
  have hA : 0 ≤ anchorSeedSquareConstant C := by unfold anchorSeedSquareConstant; positivity
  have hS : 0 ≤ bodyMeanSquareConstant := by unfold bodyMeanSquareConstant bodyMeanRelativeConstant; positivity
  have hR : 0 ≤ bodyMeanRelativeConstant := by unfold bodyMeanRelativeConstant; positivity
  have hsquare : profileSquareNorm body.weight (extraAnchorSeed C n (beta n)) ≤ (K*x^4)^2 := by
    rw [hb,mul_pow,show K^2=anchorSeedSquareConstant C by exact Real.sq_sqrt hA]
    apply he.1.trans
    apply mul_le_mul_of_nonneg_left _ hA
    have hh := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1/2 : ℝ) ≤ (8 : ℕ))
    convert hh using 1; norm_num [← pow_mul]
  have hsafe := MixedKernel.profile_singleton_activity_le body (extraAnchorSeed C n (beta n))
    b (K*x^4) (8*x^8) hbb.1 (by positivity) (by positivity) hsquare (by rw [hb]; exact he.2)
  have hfixed : b*(8*x^8) ≤ 16*x^4 := by
    calc
      _ ≤ (2/x^30)*(8*x^8) := mul_le_mul_of_nonneg_right hbb.2.2 (by positivity)
      _ = 16/x^22 := by field_simp; ring
      _ ≤ 16 := by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [one_le_pow₀ hx (n := 22)]
      _ ≤ _ := by nlinarith [one_le_pow₀ hx (n := 4)]
  have hsafeNum : x^2*(b*(K*x^4+b*(8*x^8))) ≤ 2*(K+16)/x^24 := by
    calc
      _ ≤ x^2*((2/x^30)*(K*x^4+16*x^4)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hbb.2.2 (add_le_add le_rfl hfixed) (by positivity) (by positivity)) (sq_nonneg _)
      _ = _ := by field_simp
  have hfullSq : profileSquareNorm primary.weight (actualBodyMean C n-actualReferenceMean C n (beta n)) ≤
      (Real.sqrt bodyMeanSquareConstant/x^36)^2 := by
    rw [hp,div_pow,Real.sq_sqrt hS]
    apply hf.2.trans
    have hpow : (n : ℝ)^72 ≤ (n : ℝ)^(289/4 : ℝ) := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (72 : ℕ) ≤ (289/4 : ℝ))
    convert div_le_div_of_nonneg_left hS (by positivity : (0 : ℝ) < (n : ℝ)^72) hpow using 1; ring
  have hfullPoint (color) : |(actualBodyMean C n-actualReferenceMean C n (beta n)) color| ≤
      (bodyMeanRelativeConstant/x^30)*primary.weight color := by
    rw [hp]
    apply (hf.1 color).trans
    apply mul_le_mul_of_nonneg_right _ (by rw [← hp]; exact primary.nonneg color)
    apply div_le_div_of_nonneg_left hR (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (30 : ℕ) ≤ (137/4 : ℝ))
  have hfull := MixedKernel.profile_singleton_activity_le primary (actualBodyMean C n-actualReferenceMean C n (beta n))
    a (Real.sqrt bodyMeanSquareConstant/x^36) (bodyMeanRelativeConstant/x^30) ha.1 (by positivity) (by positivity) hfullSq hfullPoint
  have hrho0 : 0 < v7Activation C n := lt_of_lt_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
  have hinv : (v7Activation C n)⁻¹ ≤ x^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
    simpa only [one_div,inv_inv] using hh
  constructor
  · change (4/v7Activation C n)^0*inputWeight primary body ppool bpool (x^2) (bodySingletonInput _) ≤ _
    rw [pow_zero,one_mul,bodySingletonInput_weight,← hb]
    exact (mul_le_mul_of_nonneg_left hsafe (sq_nonneg _)).trans hsafeNum
  · change (4/v7Activation C n)^1*inputWeight primary body ppool bpool (x^2) (primarySingletonInput _) ≤ _
    rw [pow_one,primarySingletonInput_weight,← hp]
    exact (mul_le_mul_of_nonneg_left hfull (by positivity)).trans
      (primary_mean_numeric x a (v7Activation C n) (Real.sqrt bodyMeanSquareConstant) bodyMeanRelativeConstant
        hx ha.1 ha.2.2 hrho0 hinv (by positivity) hR)


theorem pairMeanTable_activity_le (C : ℝ) (n : ℕ) (beta : ℝ)
    (w : InputSeed (Fin (Parameters.modulus n)) → ℝ) (hw : ∀ seed, 0 ≤ w seed)
    (hrho : 0 ≤ v7Activation C n) (hrho1 : v7Activation C n ≤ 1) :
    activity w (pairMeanTable C n beta) ≤ w (extraAnchorMeanInput C n beta)+w (rootMeanInput C n beta)+
      ((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)*w (fullBodyMeanInput C n beta) := by
  have hscalar (c : ℝ) (seed : InputSeed (Fin (Parameters.modulus n))) :
      activity w (MvPolynomial.C c*MvPolynomial.X seed) ≤ |c| * w seed := by
    simpa only [activity_C,activity_X] using activity_mul_le w hw (MvPolynomial.C c) (MvPolynomial.X seed)
  have hpos : 0 ≤ (Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n := by positivity
  have hh := add_le_add (add_le_add (hscalar (v7Activation C n) (extraAnchorMeanInput C n beta))
    (hscalar (v7Activation C n) (rootMeanInput C n beta)))
    (hscalar (-((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)) (fullBodyMeanInput C n beta))
  simp only [abs_of_nonneg hrho,abs_neg,abs_of_nonneg hpos] at hh
  unfold pairMeanTable
  apply (activity_add_le w hw _ _).trans
  apply (add_le_add (activity_add_le w hw _ _) le_rfl).trans
  apply hh.trans
  have h1 := mul_le_mul_of_nonneg_right hrho1 (hw (extraAnchorMeanInput C n beta))
  have h2 := mul_le_mul_of_nonneg_right hrho1 (hw (rootMeanInput C n beta))
  linarith

theorem actual_pair_mean_table_raw_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      activity (responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n))
        (pairMeanTable C n (beta n)) ≤ pairMeanInputConstant C/(n : ℝ)^16 := by
  filter_upwards [actual_pair_mean_seed_bounds_eventually C hC beta hbeta,
    actual_body_mean_seed_bounds_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hp hb hn primary body hprimary hbody ppool bpool hpp hbp
  let w := responseInputWeight primary body ppool bpool ((n : ℝ)^2) (4/v7Activation C n)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hx
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hrho1 : v7Activation C n ≤ 1 := activation_le_one _ _ _ _
  have hw : ∀ seed, 0 ≤ w seed := responseInputWeight_nonneg _ _ _ _ _ _ (sq_nonneg _) (by positivity)
  have htable := pairMeanTable_activity_le C n (beta n) w hw hrho.le hrho1
  obtain ⟨hanchor,hfull⟩ := hp primary body hprimary hbody ppool bpool hpp hbp
  have hzero : |(0 : ℤ)| ≤ maxBodyShift C n := by simp
  have hroot := (hb 0 hzero primary body hprimary hbody ppool bpool hpp hbp).2.2
  have hpop := Parameters.population_identity n
  have hdim : (Parameters.bodies n : ℝ) ≤ 2*(n : ℝ)^60 := by
    exact_mod_cast (show Parameters.bodies n ≤ 2*n^60 by
      have hh := (Parameters.dimension_bounds n).2
      rw [Parameters.security_eq n hn] at hh
      omega)
  have hm : (Parameters.legs n : ℝ) = (n : ℝ)^30 := by
    simp only [Parameters.legs,Parameters.security_eq n hn,Nat.cast_pow]
  have hcoeff : (Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n ≤ 3*(n : ℝ)^30 := by
    rw [hm]
    have hq : (Parameters.bodies n : ℝ)/(n : ℝ)^30 ≤ 2*(n : ℝ)^30 := by
      apply (div_le_iff₀ (by positivity)).mpr
      convert hdim using 1; ring
    nlinarith [one_le_pow₀ hx (n := 30)]
  have hA : 0 ≤ anchorSeedSquareConstant C := by unfold anchorSeedSquareConstant; positivity
  have hR : 0 ≤ bodyMeanRelativeConstant := by unfold bodyMeanRelativeConstant; positivity
  have hS : 0 ≤ bodyMeanSquareConstant := by unfold bodyMeanSquareConstant; positivity
  have hanchor' : w (extraAnchorMeanInput C n (beta n)) ≤ 2*(Real.sqrt (anchorSeedSquareConstant C)+16)/(n : ℝ)^16 := by
    apply hanchor.trans
    convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 16 ≤ 24 by decide))
      (show 0 ≤ 2*(Real.sqrt (anchorSeedSquareConstant C)+16) by positivity) using 1 <;> ring
  have hroot' : w (rootMeanInput C n (beta n)) ≤ 8*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant)/(n : ℝ)^16 := by
    apply hroot.trans
    convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 16 ≤ 46 by decide))
      (show 0 ≤ 8*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant) by positivity) using 1 <;> ring
  have hfull' : ((Parameters.bodies n : ℝ)/Parameters.legs n+v7Activation C n)*w (fullBodyMeanInput C n (beta n)) ≤
      24*(Real.sqrt bodyMeanSquareConstant+2*bodyMeanRelativeConstant)/(n : ℝ)^16 := by
    apply (mul_le_mul hcoeff hfull (hw _) (by positivity)).trans_eq
    field_simp
    ring
  exact htable.trans ((add_le_add (add_le_add hanchor' hroot') hfull').trans_eq (by unfold pairMeanInputConstant; ring))

theorem actual_pair_mean_input_table_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2))
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
          (pairMeanTable C n (beta n))) ≤ pairMeanInputConstant C/(n : ℝ)^16 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_pair_mean_table_raw_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,htypical]
    with n hi hraw hl ht
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro bpool hbp
  exact (inversePrimaryTable_activity_le _ _ _ _ _ _ (sq_nonneg _) operator
    (hi (actualBodyLaw C n (beta n)) bpool ((n : ℝ)^2) (sq_nonneg _)) _).trans
      (hraw _ _ hl.1 hl.2.1 (pool n) bpool ht.2.2 hbp)

end
end AFT.V7Calibration

import AFT.ProfileSingleton
import AFT.PrimarySeedInverse
import AFT.MarkedFringe
import AFT.BodyTypeParameters

/-! # Literal finite input tables for the mean of each physical body type -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def bodyMeanSafeInput (C : ℝ) (n : ℕ) (beta : ℝ) (shift : ℤ) : InputSeed (Fin (Parameters.modulus n)) :=
  bodySingletonInput (fun color => bodyCanonicalInput C n beta shift color/actualBodyCenter C n beta color)

def bodyMeanOutsideInput (C : ℝ) (n : ℕ) (beta : ℝ) (shift : ℤ) : InputSeed (Fin (Parameters.modulus n)) :=
  primarySingletonInput (fun color => bodyCenteredOutside C n beta shift color/actualPrimary C n beta color)

def rootMeanInput (C : ℝ) (n : ℕ) (beta : ℝ) : InputSeed (Fin (Parameters.modulus n)) :=
  primarySingletonInput (rootMeanDifferenceDensity C n beta)

def bodyMeanTable (C : ℝ) (n : ℕ) (beta : ℝ) (shift : ℤ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  MvPolynomial.X (bodyMeanSafeInput C n beta shift)+MvPolynomial.X (bodyMeanOutsideInput C n beta shift)+
    MvPolynomial.C (1-bodyOutsideMass n (actualBodyCenter C n beta) shift)*MvPolynomial.X (rootMeanInput C n beta)

def bodyMeanInputConstant : ℝ := 86+8*(Real.sqrt centeredBodyFringeSquareConstant+992)+
  8*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant)

theorem bodyMeanTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) (shift : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (bodyMeanTable C n beta shift) := by
  have hX (seed : InputSeed (Fin (Parameters.modulus n))) (hs : 1 ≤ seed.primaryOrder+seed.bodyOrder) :
      HasOrder (fun s => s.primaryOrder+s.bodyOrder) 1 (MvPolynomial.X seed) := by
    simpa only [map_one,one_mul] using hasOrder_C_mul_X (fun s => s.primaryOrder+s.bodyOrder) 1 seed 1 hs
  intro powers hp
  unfold bodyMeanTable
  rw [MvPolynomial.coeff_add,MvPolynomial.coeff_add,
    hX (bodyMeanSafeInput C n beta shift) (by rfl) powers hp,
    hX (bodyMeanOutsideInput C n beta shift) (by rfl) powers hp,
    hasOrder_C_mul_X (fun s => s.primaryOrder+s.bodyOrder) 1 (rootMeanInput C n beta)
      (1-bodyOutsideMass n (actualBodyCenter C n beta) shift) (by rfl) powers hp]
  norm_num

theorem primary_mean_numeric (x a rho K R : ℝ) (hx : 1 ≤ x) (ha : 0 ≤ a)
    (ha' : a ≤ 2/x^15) (_hrho : 0 < rho) (hinv : rho⁻¹ ≤ x^5)
    (hK : 0 ≤ K) (hR : 0 ≤ R) :
    (4/rho)*(a*(K/x^36+a*(R/x^30))) ≤ 8*(K+2*R)/x^46 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hfixed : a*(R/x^30) ≤ 2*R/x^36 := by
    calc
      _ ≤ (2/x^15)*(R/x^30) := mul_le_mul_of_nonneg_right ha' (by positivity)
      _ = 2*R/x^45 := by field_simp
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 36 ≤ 45 by decide)) (show 0 ≤ 2*R by positivity) using 1 <;> ring
  calc
    _ ≤ (4*x^5)*((2/x^15)*(K/x^36+2*R/x^36)) := by
      apply mul_le_mul
      · simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 4 by norm_num)
      · exact mul_le_mul ha' (add_le_add le_rfl hfixed) (by positivity) (by positivity)
      · positivity
      · positivity
    _ = _ := by field_simp; ring

/-- Actual profiles, including their support fringes, have uniform integer
power bounds suitable for every finite represented input table. -/
theorem actual_body_mean_seed_bounds_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ shift : ℤ, |shift| ≤ maxBodyShift C n →
      ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n)
        (bodyMeanSafeInput C n (beta n) shift) ≤ 86/(n : ℝ)^47 ∧
      responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n)
        (bodyMeanOutsideInput C n (beta n) shift) ≤ 8*(Real.sqrt centeredBodyFringeSquareConstant+992)/(n : ℝ)^46 ∧
      responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n)
        (rootMeanInput C n (beta n)) ≤ 8*(Real.sqrt (2*bodyMeanSquareConstant)+4*bodyMeanRelativeConstant)/(n : ℝ)^46 := by
  filter_upwards [actual_body_type_power_bounds C hC beta hbeta,
    actual_centered_body_fringe_eventually C hC beta hbeta,
    actual_body_fringe_bounds_eventually C hC beta hbeta,
    actual_marked_fringe_factors_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta,
    legCutoff_le_square_eventually C hC, v7Activation_lower_eventually C hC, eventually_ge_atTop 2]
    with n ht ho hf hg hb hcut hrho hn shift hs primary body hp hbody ppool bpool hpp hbp
  let x : ℝ := n
  let a := (Real.sqrt (ppool : ℝ))⁻¹
  let b := (Real.sqrt (bpool : ℝ))⁻¹
  let rho := v7Activation C n
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have ha := covariance_pool_rate n ppool hn hpp
  have hbb := body_pair_pool_rate n bpool hn hbp
  have ht := ht shift hs
  have hK0 : 0 ≤ centeredBodyFringeSquareConstant := by unfold centeredBodyFringeSquareConstant; positivity
  have hR0 : 0 ≤ bodyMeanRelativeConstant := by unfold bodyMeanRelativeConstant; positivity
  have hS0 : 0 ≤ bodyMeanSquareConstant := by unfold bodyMeanSquareConstant; positivity
  have hsafe := MixedKernel.profile_singleton_activity_le body
    (bodyCanonicalInput C n (beta n) shift) b (33/x^19) 5 hbb.1 (by positivity) (by norm_num)
    (by rw [hbody]; exact ht.2.2.2.1.trans (by dsimp only [x]; field_simp; norm_num))
    (by rw [hbody]; exact ht.2.2.1)
  have hsafeNum : x^2*(b*(33/x^19+b*5)) ≤ 86/x^47 := by
    have h5 : b*5 ≤ 10/x^19 := by
      calc
        _ ≤ (2/x^30)*5 := mul_le_mul_of_nonneg_right hbb.2.2 (by norm_num)
        _ = 10/x^30 := by ring
        _ ≤ _ := by convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 19 ≤ 30 by decide)) (show (0 : ℝ) ≤ 10 by norm_num) using 1 <;> ring
    calc
      _ ≤ x^2*((2/x^30)*(33/x^19+10/x^19)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hbb.2.2 (add_le_add le_rfl h5) (by positivity) (by positivity)) (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hmu : bodyOutsideMass n (actualBodyCenter C n (beta n)) shift ≤ 60/x^38 := by
    have hh := (hf shift).1
    have hh' := (body_shift_fraction C n hn hcut shift hs).1
    have hh'' := mul_le_mul_of_nonneg_left hh' (show (0 : ℝ) ≤ 12 by norm_num)
    dsimp only [x]
    simp only [div_eq_mul_inv] at hh hh'' ⊢
    linarith
  have hpoint : ∀ color, |bodyCenteredOutside C n (beta n) shift color| ≤
      (496/x^30)*primary.weight color := by
    intro color
    rw [hp]
    apply ((ho shift).1 color).trans
    apply mul_le_mul_of_nonneg_right _ (by rw [← hp]; exact primary.nonneg color)
    have hd := bodyCompensation_coarse C n hC hn
    have hm30 : 60/x^38 ≤ 60/x^30 := by
      convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 30 ≤ 38 by decide)) (show (0 : ℝ) ≤ 60 by norm_num) using 1 <;> ring
    dsimp only [x] at *
    simp only [div_eq_mul_inv] at hd hm30 hmu ⊢
    linarith
  have hsquare : profileSquareNorm primary.weight (bodyCenteredOutside C n (beta n) shift) ≤
      (Real.sqrt centeredBodyFringeSquareConstant/x^36)^2 := by
    rw [hp,div_pow,Real.sq_sqrt hK0]
    apply ht.2.2.2.2.2.trans
    have hpow : (n : ℝ)^72 ≤ (n : ℝ)^(289/4 : ℝ) := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (72 : ℕ) ≤ (289/4 : ℝ))
    convert div_le_div_of_nonneg_left hK0 (by positivity : (0 : ℝ) < (n : ℝ)^72) hpow using 1; ring
  have hout := MixedKernel.profile_singleton_activity_le primary (bodyCenteredOutside C n (beta n) shift)
    a (Real.sqrt centeredBodyFringeSquareConstant/x^36) (496/x^30) ha.1 (by positivity) (by positivity) hsquare hpoint
  have hrootSq : (∑ color, primary.weight color*rootMeanDifferenceDensity C n (beta n) color^2) ≤
      (Real.sqrt (2*bodyMeanSquareConstant)/x^36)^2 := by
    rw [hp,div_pow,Real.sq_sqrt (by positivity)]
    convert hg.2.2.2 using 1; ring
  have hrootPoint (color) : |rootMeanDifferenceDensity C n (beta n) color| ≤ 2*bodyMeanRelativeConstant/x^30 := by
    apply (hg.2.2.1 color).trans
    convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 30 ≤ 34 by decide)) (show 0 ≤ 2*bodyMeanRelativeConstant by positivity) using 1 <;> ring
  have hroot := MixedKernel.singleton_activity_le primary (rootMeanDifferenceDensity C n (beta n))
    a (Real.sqrt (2*bodyMeanSquareConstant)/x^36) (2*bodyMeanRelativeConstant/x^30)
    ha.1 (by positivity) (by positivity) hrootSq hrootPoint
  have hrho0 : 0 < rho := lt_of_lt_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
  have hinv : rho⁻¹ ≤ x^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ)^5)⁻¹) hrho
    simpa only [one_div,inv_inv] using hh
  constructor
  · change (4/rho)^0*inputWeight primary body ppool bpool (x^2) (bodySingletonInput _) ≤ _
    rw [pow_zero,one_mul,bodySingletonInput_weight]
    rw [← hbody]
    exact (mul_le_mul_of_nonneg_left hsafe (sq_nonneg _)).trans hsafeNum
  constructor
  · change (4/rho)^1*inputWeight primary body ppool bpool (x^2) (primarySingletonInput _) ≤ _
    rw [pow_one,primarySingletonInput_weight,← hp]
    apply (mul_le_mul_of_nonneg_left hout (by positivity)).trans
    convert (primary_mean_numeric x a rho (Real.sqrt centeredBodyFringeSquareConstant) 496 hx ha.1 ha.2.2 hrho0 hinv (by positivity) (by norm_num)) using 1; ring
  · change (4/rho)^1*inputWeight primary body ppool bpool (x^2) (primarySingletonInput _) ≤ _
    rw [pow_one,primarySingletonInput_weight]
    apply (mul_le_mul_of_nonneg_left hroot (by positivity)).trans
    convert (primary_mean_numeric x a rho (Real.sqrt (2*bodyMeanSquareConstant)) (2*bodyMeanRelativeConstant)
        hx ha.1 ha.2.2 hrho0 hinv (by positivity) (by positivity)) using 1; ring


theorem bodyMeanTable_activity_le (C : ℝ) (n : ℕ) (beta : ℝ) (shift : ℤ)
    (w : InputSeed (Fin (Parameters.modulus n)) → ℝ) (hw : ∀ seed, 0 ≤ w seed)
    (hmu : 0 ≤ bodyOutsideMass n (actualBodyCenter C n beta) shift ∧
      bodyOutsideMass n (actualBodyCenter C n beta) shift ≤ 1) :
    activity w (bodyMeanTable C n beta shift) ≤ w (bodyMeanSafeInput C n beta shift)+
      w (bodyMeanOutsideInput C n beta shift)+w (rootMeanInput C n beta) := by
  unfold bodyMeanTable
  apply (activity_add_le w hw _ _).trans
  have hleft := activity_add_le w hw (MvPolynomial.X (bodyMeanSafeInput C n beta shift))
    (MvPolynomial.X (bodyMeanOutsideInput C n beta shift))
  simp only [activity_X] at hleft
  have hright := activity_mul_le w hw
    (MvPolynomial.C (1-bodyOutsideMass n (actualBodyCenter C n beta) shift))
    (MvPolynomial.X (rootMeanInput C n beta))
  simp only [activity_C,activity_X,abs_of_nonneg (sub_nonneg.mpr hmu.2)] at hright
  have hright' : activity w (MvPolynomial.C (1-bodyOutsideMass n (actualBodyCenter C n beta) shift)*
      MvPolynomial.X (rootMeanInput C n beta)) ≤ w (rootMeanInput C n beta) :=
    hright.trans (by nlinarith [hw (rootMeanInput C n beta)])
  exact add_le_add hleft hright'

theorem actual_body_mean_table_raw_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ shift : ℤ, |shift| ≤ maxBodyShift C n →
      ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      activity (responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n))
        (bodyMeanTable C n (beta n) shift) ≤ bodyMeanInputConstant/(n : ℝ)^46 := by
  filter_upwards [actual_body_mean_seed_bounds_eventually C hC beta hbeta,
    eventually_ge_atTop 2] with n h hn shift hs primary body hp hb ppool bpool hpp hbp
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hmu := bodyOutsideMass_bounds n body.weight body.nonneg body.sum_one shift
  rw [hb] at hmu
  have htable := bodyMeanTable_activity_le C n (beta n) shift
    (responseInputWeight primary body ppool bpool ((n : ℝ)^2) (4/v7Activation C n))
    (responseInputWeight_nonneg _ _ _ _ _ _ (sq_nonneg _) (by positivity)) hmu
  obtain ⟨h1,h2,h3⟩ := h shift hs primary body hp hb ppool bpool hpp hbp
  have h1' : 86/(n : ℝ)^47 ≤ 86/(n : ℝ)^46 := by
    convert mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 46 ≤ 47 by decide)) (show (0 : ℝ) ≤ 86 by norm_num) using 1 <;> ring
  exact htable.trans ((add_le_add (add_le_add (h1.trans h1') h2) h3).trans_eq (by unfold bodyMeanInputConstant; ring))

/-- Every component has been transformed by the same actual calibration
inverse; the conclusion is an activity bound on a literal finite table. -/
theorem actual_body_mean_input_table_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ shift : ℤ, |shift| ≤ maxBodyShift C n →
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2))
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
          (bodyMeanTable C n (beta n) shift)) ≤ bodyMeanInputConstant/(n : ℝ)^46 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_body_mean_table_raw_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,htypical,eventually_ge_atTop 2]
    with n hi hraw hl ht hn
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro bpool hbp shift hs
  exact (inversePrimaryTable_activity_le _ _ _ _ _ _ (sq_nonneg _) operator
    (hi (actualBodyLaw C n (beta n)) bpool ((n : ℝ)^2) (sq_nonneg _)) _).trans
      (hraw shift hs _ _ hl.1 hl.2.1 (pool n) bpool ht.2.2 hbp)

end
end AFT.V7Calibration

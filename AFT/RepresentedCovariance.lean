import AFT.CovarianceParameters
import AFT.ActualCovarianceCanonical
import AFT.RepresentedQueue

/-! # Literal finite input table of the actual local source covariances

The five entries are the actual cubic and quadratic kernels, with the
physical activation coefficients.  Primary inverse costs are charged per
coordinate while retaining the actual primary pool size.
-/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

variable {Color Seed : Type*} [Fintype Color]

def responseInputWeight (primary body : FiniteDist Color) (primaryPool bodyPool radius inverseCost : ℝ)
    (seed : InputSeed Color) : ℝ :=
  inverseCost ^ seed.primaryOrder * inputWeight primary body primaryPool bodyPool radius seed

theorem responseInputWeight_nonneg (primary body : FiniteDist Color) (primaryPool bodyPool radius inverseCost : ℝ)
    (hradius : 0 ≤ radius) (hcost : 0 ≤ inverseCost) (seed : InputSeed Color) :
    0 ≤ responseInputWeight primary body primaryPool bodyPool radius inverseCost seed :=
  mul_nonneg (pow_nonneg hcost _) (inputWeight_nonneg primary body primaryPool bodyPool radius seed hradius)

omit [Fintype Color] in
theorem hasOrder_C_mul_X (order : Seed → ℕ) (minimum : ℕ) (seed : Seed) (coefficient : ℝ)
    (h : minimum ≤ order seed) : HasOrder order minimum (MvPolynomial.C coefficient * MvPolynomial.X seed) := by
  intro powers hp
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs with heq
  · subst powers
    have hh : weightedOrder order (Finsupp.single seed 1) = order seed := by
      simp [weightedOrder]
    rw [hh] at hp
    omega
  · simp

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open Filter GaussianSource RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def actualCovarianceSeed (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    Fin 5 → InputSeed (Fin (Parameters.modulus parameter)) :=
  ![actualInactiveTripleInput cutoffScale parameter beta queue,
    actualInactiveMarginalBodyInput cutoffScale parameter beta queue,
    actualActiveTripleInput cutoffScale parameter beta queue,
    actualActiveMarginalBodyInput cutoffScale parameter beta queue false,
    actualActiveMarginalBodyInput cutoffScale parameter beta queue true]

def covarianceCoefficient (rho : ℝ) : Fin 5 → ℝ :=
  ![1-rho, 2*(1-rho), rho*(1-rho), rho*(1-rho), rho*(1-rho)]

def actualCovarianceTable (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    Table (InputSeed (Fin (Parameters.modulus parameter))) :=
  ∑ index : Fin 5, MvPolynomial.C (covarianceCoefficient (v7Activation cutoffScale parameter) index) *
    MvPolynomial.X (actualCovarianceSeed cutoffScale parameter beta queue index)

theorem actualCovarianceTable_hasOrder (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 2
      (actualCovarianceTable cutoffScale parameter beta queue) := by
  apply hasOrder_sum
  intro index _
  apply hasOrder_C_mul_X
  fin_cases index <;> norm_num [actualCovarianceSeed, actualInactiveTripleInput,
    actualInactiveMarginalBodyInput, actualActiveTripleInput, actualActiveMarginalBodyInput,
    primaryTripleInput, primaryPairInput]

theorem actualCovarianceTable_activity_le (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (weight : InputSeed (Fin (Parameters.modulus parameter)) → ℝ)
    (hweight : ∀ seed, 0 ≤ weight seed)
    (hrho0 : 0 ≤ v7Activation cutoffScale parameter)
    (hrho1 : v7Activation cutoffScale parameter ≤ 1) :
    activity weight (actualCovarianceTable cutoffScale parameter beta queue) ≤
      (1-v7Activation cutoffScale parameter) *
        (weight (actualInactiveTripleInput cutoffScale parameter beta queue) +
          2*weight (actualInactiveMarginalBodyInput cutoffScale parameter beta queue)) +
      v7Activation cutoffScale parameter*(1-v7Activation cutoffScale parameter) *
        (weight (actualActiveTripleInput cutoffScale parameter beta queue) +
          weight (actualActiveMarginalBodyInput cutoffScale parameter beta queue false) +
          weight (actualActiveMarginalBodyInput cutoffScale parameter beta queue true)) := by
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index : Fin 5, |covarianceCoefficient (v7Activation cutoffScale parameter) index| *
        weight (actualCovarianceSeed cutoffScale parameter beta queue index) := by
      apply Finset.sum_le_sum
      intro index _
      simpa only [activity_C, activity_X] using activity_mul_le weight hweight
        (MvPolynomial.C (covarianceCoefficient (v7Activation cutoffScale parameter) index))
        (MvPolynomial.X (actualCovarianceSeed cutoffScale parameter beta queue index))
    _ = _ := by
      have hnonneg : 0 ≤ 1-v7Activation cutoffScale parameter := sub_nonneg.mpr hrho1
      simp [Fin.sum_univ_succ, covarianceCoefficient, actualCovarianceSeed,
        abs_of_nonneg hnonneg, abs_of_nonneg hrho0, abs_mul]
      ring

/-- All five actual inputs, including the per-primary inverse cost, are
bounded uniformly over the public queue and over retained pool sizes. -/
theorem actual_covariance_seed_budgets_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter : ℕ in atTop, ∀ queue : ℤ,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool : ℕ, Parameters.legs parameter ≤ 2*primaryPool →
      ∀ bodyPool radius cost : ℝ, 0 ≤ cost →
      let w := responseInputWeight primary body primaryPool bodyPool radius cost
      w (actualInactiveTripleInput cutoffScale parameter (beta parameter) queue) ≤ cost^3*(851968/(parameter : ℝ)^71) ∧
      w (actualInactiveMarginalBodyInput cutoffScale parameter (beta parameter) queue) ≤ cost^2*(9984/(parameter : ℝ)^75) ∧
      w (actualActiveTripleInput cutoffScale parameter (beta parameter) queue) ≤ cost^3*(1703936/(parameter : ℝ)^56) ∧
      ∀ side, w (actualActiveMarginalBodyInput cutoffScale parameter (beta parameter) queue side) ≤ cost^2*(17472/(parameter : ℝ)^37) := by
  filter_upwards [actual_inactive_triple_activity_eventually cutoffScale hscale beta hbeta,
    actual_inactive_marginal_body_activity_eventually cutoffScale hscale beta hbeta,
    actual_active_triple_activity_eventually cutoffScale hscale beta hbeta,
    actual_active_marginal_body_activity_eventually cutoffScale hscale beta hbeta,
    actual_covariance_activity_powers_eventually cutoffScale hscale,
    actual_quadratic_covariance_powers_eventually cutoffScale hscale,
    eventually_ge_atTop 2] with parameter hI hIQ hA hAQ hpower hquad hp
  intro queue primary body hprimary pool hpool bodyPool radius cost hcost
  let a := (Real.sqrt (pool : ℝ))⁻¹
  have ha := covariance_pool_rate parameter pool hp hpool
  have hpow := hpower a ha.1 ha.2.1 ha.2.2
  have hq := hquad a ha.1 ha.2.1 ha.2.2
  have hI' := hI queue primary body hprimary pool bodyPool radius
  have hIQ' := (hIQ queue primary body hprimary pool bodyPool radius).trans hq.1
  have hA' := hA queue primary body hprimary pool bodyPool radius
  have hAQ' (side : Bool) := (hAQ queue side primary body hprimary pool bodyPool radius).trans hq.2
  have hbody0 : 0 ≤ inactiveBodyActivityBound cutoffScale parameter a := by unfold inactiveBodyActivityBound; positivity
  have hIcap : inputWeight primary body pool bodyPool radius
      (actualInactiveTripleInput cutoffScale parameter (beta parameter) queue) ≤ 851968/(parameter : ℝ)^71 := by
    apply hI'.trans
    exact (mul_le_mul hpow.1 hpow.2.1 hbody0 (by positivity)).trans_eq (by field_simp; norm_num)
  have hAcap : inputWeight primary body pool bodyPool radius
      (actualActiveTripleInput cutoffScale parameter (beta parameter) queue) ≤ 1703936/(parameter : ℝ)^56 := by
    apply hA'.trans
    exact (mul_le_mul hpow.2.2 hpow.2.1 hbody0 (by positivity)).trans_eq (by field_simp; norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · exact mul_le_mul_of_nonneg_left hIcap (pow_nonneg hcost 3)
  · exact mul_le_mul_of_nonneg_left hIQ' (pow_nonneg hcost 2)
  · exact mul_le_mul_of_nonneg_left hAcap (pow_nonneg hcost 3)
  · intro side
    exact mul_le_mul_of_nonneg_left (hAQ' side) (pow_nonneg hcost 2)

/-- The physical activation coefficient cancels one primary inverse in
both active contributions. -/
theorem covariance_numeric_bound (x rho : ℝ) (hx : 1 ≤ x) (hrho : 0 < rho)
    (hinv : rho⁻¹ ≤ x^5) :
    x^30*((1-rho)*((2/rho)^3*(851968/x^71)+2*(2/rho)^2*(9984/x^75))+
      rho*(1-rho)*((2/rho)^3*(1703936/x^56)+2*(2/rho)^2*(17472/x^37))) ≤ 33554432/x^2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hinv0 : 0 ≤ rho⁻¹ := inv_nonneg.mpr hrho.le
  have h3 : (2/rho)^3 ≤ 8*x^15 := by
    calc
      _ = 8*(rho⁻¹)^3 := by ring
      _ ≤ 8*(x^5)^3 := by gcongr
      _ = _ := by ring
  have h2 : (2/rho)^2 ≤ 4*x^10 := by
    calc
      _ = 4*(rho⁻¹)^2 := by ring
      _ ≤ 4*(x^5)^2 := by gcongr
      _ = _ := by ring
  have hr3 : rho*(2/rho)^3 ≤ 8*x^10 := by
    calc
      _ = 8*(rho⁻¹)^2 := by field_simp; ring
      _ ≤ 8*(x^5)^2 := by gcongr
      _ = _ := by ring
  have hr2 : rho*(2/rho)^2 ≤ 4*x^5 := by
    calc
      _ = 4*rho⁻¹ := by field_simp; ring
      _ ≤ _ := by gcongr
  have hremaining : 1-rho ≤ 1 := by linarith
  calc
    _ ≤ x^30*((2/rho)^3*(851968/x^71)+2*(2/rho)^2*(9984/x^75)+
        (rho*(2/rho)^3)*(1703936/x^56)+2*(rho*(2/rho)^2)*(17472/x^37)) := by
      have hfirst := mul_le_mul_of_nonneg_right hremaining
        (show 0 ≤ (2/rho)^3*(851968/x^71)+2*(2/rho)^2*(9984/x^75) by positivity)
      have hsecond := mul_le_mul_of_nonneg_right hremaining
        (show 0 ≤ rho*((2/rho)^3*(1703936/x^56)+2*(2/rho)^2*(17472/x^37)) by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ x^30)
      nlinarith
    _ ≤ x^30*((8*x^15)*(851968/x^71)+2*(4*x^10)*(9984/x^75)+
        (8*x^10)*(1703936/x^56)+2*(4*x^5)*(17472/x^37)) := by gcongr
    _ = 6815744/x^26+79872/x^35+13631488/x^16+139776/x^2 := by field_simp; ring
    _ ≤ 33554432/x^2 := by
      have h26 := inverse_power_antitone hx (show 2 ≤ 26 by decide)
      have h35 := inverse_power_antitone hx (show 2 ≤ 35 by decide)
      have h16 := inverse_power_antitone hx (show 2 ≤ 16 by decide)
      simp only [div_eq_mul_inv, one_mul] at h26 h35 h16 ⊢
      nlinarith [inv_nonneg.mpr (show 0 ≤ x^2 by positivity)]

/-- The true covariance table, summed over the actual number of legs,
has the required lambda^-2 budget after all primary inverse costs. -/
theorem actual_covariance_table_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter : ℕ in atTop, ∀ queue : ℤ,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool : ℕ, Parameters.legs parameter ≤ 2*primaryPool →
      ∀ bodyPool radius : ℝ, 0 ≤ radius →
      (Parameters.legs parameter : ℝ) *
        activity (responseInputWeight primary body primaryPool bodyPool radius (2/v7Activation cutoffScale parameter))
          (actualCovarianceTable cutoffScale parameter (beta parameter) queue) ≤ 33554432/(parameter : ℝ)^2 := by
  filter_upwards [actual_covariance_seed_budgets_eventually cutoffScale hscale beta hbeta,
    v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hseed hlower hp queue primary body hprimary pool hpool bodyPool radius hradius
  let rho := v7Activation cutoffScale parameter
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hrho : 0 < rho := lt_of_lt_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hlower
  have hrho1 : rho ≤ 1 := activation_le_one _ _ _ _
  have hinv : rho⁻¹ ≤ (parameter : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hlower
    simpa only [one_div, inv_inv] using hh
  let w := responseInputWeight primary body pool bodyPool radius (2/rho)
  have hw : ∀ seed, 0 ≤ w seed := responseInputWeight_nonneg primary body pool bodyPool radius (2/rho) hradius (by positivity)
  have hb := hseed queue primary body hprimary pool hpool bodyPool radius (2/rho) (by positivity)
  have hI := hb.1
  have hIQ := hb.2.1
  have hA := hb.2.2.1
  have hAF := hb.2.2.2 false
  have hAT := hb.2.2.2 true
  have ht := actualCovarianceTable_activity_le cutoffScale parameter (beta parameter) queue w hw hrho.le hrho1
  have ht' : activity w (actualCovarianceTable cutoffScale parameter (beta parameter) queue) ≤
      (1-rho)*((2/rho)^3*(851968/(parameter : ℝ)^71)+2*(2/rho)^2*(9984/(parameter : ℝ)^75))+
      rho*(1-rho)*((2/rho)^3*(1703936/(parameter : ℝ)^56)+2*(2/rho)^2*(17472/(parameter : ℝ)^37)) := by
    apply ht.trans
    have hnonneg : 0 ≤ 1-rho := sub_nonneg.mpr hrho1
    change (1-rho)*(_+2*_)+rho*(1-rho)*(_+_+_) ≤ _
    calc
      _ ≤ (1-rho)*((2/rho)^3*(851968/(parameter : ℝ)^71)+2*((2/rho)^2*(9984/(parameter : ℝ)^75)))+
          rho*(1-rho)*((2/rho)^3*(1703936/(parameter : ℝ)^56)+(2/rho)^2*(17472/(parameter : ℝ)^37)+(2/rho)^2*(17472/(parameter : ℝ)^37)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hI (mul_le_mul_of_nonneg_left hIQ (by norm_num))) hnonneg)
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hAF) hAT) (mul_nonneg hrho.le hnonneg))
      _ = _ := by ring
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  change (Parameters.legs parameter : ℝ)*activity w _ ≤ _
  rw [hm]
  exact (mul_le_mul_of_nonneg_left ht' (by positivity)).trans
    (covariance_numeric_bound (parameter : ℝ) rho hx hrho hinv)

/-- The literal mixed-fiber inverse has cost four per primary coordinate.
Changing the fixed constant leaves the actual lambda^-2 decay unchanged. -/
theorem covariance_numeric_bound_four (x rho : ℝ) (hx : 1 ≤ x) (hrho : 0 < rho)
    (hrho1 : rho ≤ 1) (hinv : rho⁻¹ ≤ x^5) :
    x^30*((1-rho)*((4/rho)^3*(851968/x^71)+2*(4/rho)^2*(9984/x^75))+
      rho*(1-rho)*((4/rho)^3*(1703936/x^56)+2*(4/rho)^2*(17472/x^37))) ≤ 268435456/x^2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hc : 0 ≤ 1-rho := sub_nonneg.mpr hrho1
  have hI : 0 ≤ 8*(1-rho)*(2/rho)^2*(9984/x^75) := by positivity
  have hA : 0 ≤ 8*rho*(1-rho)*(2/rho)^2*(17472/x^37) := by positivity
  calc
    _ ≤ 8*(x^30*((1-rho)*((2/rho)^3*(851968/x^71)+2*(2/rho)^2*(9984/x^75))+
        rho*(1-rho)*((2/rho)^3*(1703936/x^56)+2*(2/rho)^2*(17472/x^37)))) := by
      have hh : (1-rho)*((4/rho)^3*(851968/x^71)+2*(4/rho)^2*(9984/x^75))+
          rho*(1-rho)*((4/rho)^3*(1703936/x^56)+2*(4/rho)^2*(17472/x^37)) ≤
          8*((1-rho)*((2/rho)^3*(851968/x^71)+2*(2/rho)^2*(9984/x^75))+
          rho*(1-rho)*((2/rho)^3*(1703936/x^56)+2*(2/rho)^2*(17472/x^37))) := by
        linear_combination hI+hA
      exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ x^30)).trans_eq (by ring)
    _ ≤ 8*(33554432/x^2) := mul_le_mul_of_nonneg_left (covariance_numeric_bound x rho hx hrho hinv) (by norm_num)
    _ = _ := by ring
/-- The true covariance table, summed over the actual number of legs,
has the required lambda^-2 budget after all primary inverse costs. -/
theorem actual_covariance_table_mixed_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter : ℕ in atTop, ∀ queue : ℤ,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool : ℕ, Parameters.legs parameter ≤ 2*primaryPool →
      ∀ bodyPool radius : ℝ, 0 ≤ radius →
      (Parameters.legs parameter : ℝ) *
        activity (responseInputWeight primary body primaryPool bodyPool radius (4/v7Activation cutoffScale parameter))
          (actualCovarianceTable cutoffScale parameter (beta parameter) queue) ≤ 268435456/(parameter : ℝ)^2 := by
  filter_upwards [actual_covariance_seed_budgets_eventually cutoffScale hscale beta hbeta,
    v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hseed hlower hp queue primary body hprimary pool hpool bodyPool radius hradius
  let rho := v7Activation cutoffScale parameter
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hrho : 0 < rho := lt_of_lt_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hlower
  have hrho1 : rho ≤ 1 := activation_le_one _ _ _ _
  have hinv : rho⁻¹ ≤ (parameter : ℝ)^5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < ((parameter : ℝ)^5)⁻¹) hlower
    simpa only [one_div, inv_inv] using hh
  let w := responseInputWeight primary body pool bodyPool radius (4/rho)
  have hw : ∀ seed, 0 ≤ w seed := responseInputWeight_nonneg primary body pool bodyPool radius (4/rho) hradius (by positivity)
  have hb := hseed queue primary body hprimary pool hpool bodyPool radius (4/rho) (by positivity)
  have hI := hb.1
  have hIQ := hb.2.1
  have hA := hb.2.2.1
  have hAF := hb.2.2.2 false
  have hAT := hb.2.2.2 true
  have ht := actualCovarianceTable_activity_le cutoffScale parameter (beta parameter) queue w hw hrho.le hrho1
  have ht' : activity w (actualCovarianceTable cutoffScale parameter (beta parameter) queue) ≤
      (1-rho)*((4/rho)^3*(851968/(parameter : ℝ)^71)+2*(4/rho)^2*(9984/(parameter : ℝ)^75))+
      rho*(1-rho)*((4/rho)^3*(1703936/(parameter : ℝ)^56)+2*(4/rho)^2*(17472/(parameter : ℝ)^37)) := by
    apply ht.trans
    have hnonneg : 0 ≤ 1-rho := sub_nonneg.mpr hrho1
    change (1-rho)*(_+2*_)+rho*(1-rho)*(_+_+_) ≤ _
    calc
      _ ≤ (1-rho)*((4/rho)^3*(851968/(parameter : ℝ)^71)+2*((4/rho)^2*(9984/(parameter : ℝ)^75)))+
          rho*(1-rho)*((4/rho)^3*(1703936/(parameter : ℝ)^56)+(4/rho)^2*(17472/(parameter : ℝ)^37)+(4/rho)^2*(17472/(parameter : ℝ)^37)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hI (mul_le_mul_of_nonneg_left hIQ (by norm_num))) hnonneg)
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hAF) hAT) (mul_nonneg hrho.le hnonneg))
      _ = _ := by ring
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  change (Parameters.legs parameter : ℝ)*activity w _ ≤ _
  rw [hm]
  exact (mul_le_mul_of_nonneg_left ht' (by positivity)).trans
    (covariance_numeric_bound_four (parameter : ℝ) rho hx hrho hrho1 hinv)

end
end AFT.V7Calibration

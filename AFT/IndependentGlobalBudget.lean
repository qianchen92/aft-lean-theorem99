import AFT.IndependentGlobalQuotient

/-! # Fixed-cutoff independent response has the original lambda^{-5/2} scale -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentGlobalBudgetFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentGlobalBudgetConstant (C : ℝ) : ℝ :=
  independentJointHigherConstant C+2*independentPositiveInputConstant C+2*independentBodyInputConstant C

def independentGlobalUpperConstant (C : ℝ) (cutoff : ℕ) : ℝ :=
  Real.exp 1*(2*cutoff)*independentGlobalBudgetConstant C

theorem independentGlobalGrowth_small_eventually (C : ℝ) (hC : 1 ≤ C) (cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ primaryOrder bodyOrder : ℕ,primaryOrder+bodyOrder ≤ cutoff →
      independentGlobalGrowth C n primaryOrder bodyOrder-1 ≤
        independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ) := by
  have ha := activationConstant_pos C hC
  have hhigh : 0 ≤ independentJointHigherConstant C := by
    unfold independentJointHigherConstant independentReferenceHilbertConstant; positivity
  have hp : 0 ≤ independentPositiveInputConstant C := by unfold independentPositiveInputConstant; positivity
  have hb : 0 ≤ independentBodyInputConstant C := by unfold independentBodyInputConstant; positivity
  have hc : 0 ≤ independentGlobalBudgetConstant C := by unfold independentGlobalBudgetConstant; positivity
  have ht : Tendsto (fun n : ℕ => (2*cutoff : ℝ)*(independentGlobalBudgetConstant C/(n : ℝ)^(5/2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using ((((tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop
        (independentGlobalBudgetConstant C)).const_mul (2*cutoff : ℝ))
  filter_upwards [Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1) ht,eventually_ge_atTop 2]
    with n hn hn2 primaryOrder bodyOrder horder
  have hx : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  let error := independentGlobalBudgetConstant C/(n : ℝ)^(5/2 : ℝ)
  have he : 0 ≤ error := div_nonneg hc (Real.rpow_nonneg (by positivity) _)
  have hden := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5/2:ℝ)≤43/4)
  have hh : independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ) ≤ error := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [independentGlobalBudgetConstant]
    linarith
  have hpp : 2*(independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ)) ≤ error := by
    have hi := div_le_div_of_nonneg_left hp (Real.rpow_pos_of_pos hx _) hden
    apply (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2)).trans
    change _ ≤ independentGlobalBudgetConstant C/(n : ℝ)^(5/2 : ℝ)
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [independentGlobalBudgetConstant]
    linarith
  have hbb : 2*(independentBodyInputConstant C/(n : ℝ)^(43/4 : ℝ)) ≤ error := by
    have hi := div_le_div_of_nonneg_left hb (Real.rpow_pos_of_pos hx _) hden
    apply (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2)).trans
    change _ ≤ independentGlobalBudgetConstant C/(n : ℝ)^(5/2 : ℝ)
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [independentGlobalBudgetConstant]
    linarith
  have hg : independentGlobalGrowth C n primaryOrder bodyOrder ≤ (1+error)^(2*cutoff) := by
    unfold independentGlobalGrowth
    calc
      _ ≤ (1+error)^primaryOrder*(1+error)^primaryOrder*(1+error)^bodyOrder := by
        gcongr
      _ = (1+error)^(primaryOrder+primaryOrder+bodyOrder) := by rw [pow_add,pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hsmall : ((2*cutoff : ℕ):ℝ)*error ≤ 1 := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hn
  exact (sub_le_sub_right hg 1).trans
    ((one_add_power_sub_one_le error (2*cutoff) he hsmall).trans_eq (by
      dsimp [error,independentGlobalUpperConstant]
      push_cast
      ring))

/-- The actual arbitrary joint independent response satisfies the required
small activity at every fixed input cutoff, with no extra lambda powers. -/
theorem independentGlobalUpper_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ) (cutoff : ℕ)
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
      Finset.univ seed.kernel → seed.primaryOrder+seed.bodyOrder ≤ cutoff → ∀ depth : ℕ,
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    activity weight (independentGlobalQuotient C n (beta n) operator charts seed depth-MvPolynomial.X seed) ≤
      independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ)*weight seed := by
  filter_upwards [independentGlobalQuotient_bounds_eventually C hC beta pool htypical,
    independentGlobalGrowth_small_eventually C hC cutoff]
    with n hq hg operator hop charts hcharts bodyPool radius hradius seed hseed horder depth
  exact (hq operator hop charts hcharts bodyPool radius hradius seed hseed depth).2.trans
    (mul_le_mul_of_nonneg_right (hg seed.primaryOrder seed.bodyOrder horder)
      (inputWeight_nonneg _ _ _ _ _ seed hradius))

end
end AFT.V7Calibration

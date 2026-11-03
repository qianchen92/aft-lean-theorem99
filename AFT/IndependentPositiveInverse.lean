import AFT.IndependentPositiveActivity
import AFT.IndependentResponseCost
import AFT.ReferenceQuotientTable

/-! # The actual positive local denominator has a small literal inverse input -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPositiveInverseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPositiveInverseSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentPositiveInputConstant (C : ℝ) : ℝ :=
  16*(4112*(8*activationConstant C)+(2*2097152*100000000)*(8*activationConstant C)^2)

def independentPositiveInputTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  referenceInverseTable (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (actualReferenceLaw C n beta) (v7Activation C n) operator (independentPairedPositiveMass C n beta charts)

/-- The positive error is represented by actual calibrated kernels. Its
small activity is derived from the physical singleton and full fibers. -/
theorem independentPositiveInputTable_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pool n) bodyPool radius) (independentPositiveInputTable C n (beta n) operator charts) ≤
      independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  have hlarge : ∀ᶠ n : ℕ in atTop,8*activationConstant C ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    independentPairedPositive_component_activity_eventually C hC beta hbeta,
    independentPairedPositive_linear_activity_eventually C hC beta hbeta,
    htypical,hlarge,eventually_ge_atTop 2]
    with n hi hh hl ht hlarge hn operator hop charts hc bodyPool radius hradius
  obtain ⟨inverse,hinverse,hi⟩ := hi
  have heq : operator=inverse := LinearEquiv.toLinearMap_injective (hop.trans hinverse.symm)
  subst inverse
  let p := actualPrimaryLaw C n (beta n)
  let body := actualBodyLaw C n (beta n)
  let r := actualReferenceLaw C n (beta n)
  let rate : ℝ := 1/Real.sqrt (pool n : ℝ)
  let cost := independentCoordinateCost C n (pool n)
  let coefficient : ℝ := 2*2097152*100000000
  let budget := (4112*(8*activationConstant C)+coefficient*(8*activationConstant C)^2)/(n : ℝ)^(43/4 : ℝ)
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha := activationConstant_pos C hC
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hrate := independent_primary_rate_small n (pool n) hn ht.2.2
  have hcost := independent_positive_cost_bound C hC n (pool n) hn ht.2.2 hlarge
  have hcost0 : 0 ≤ cost := by dsimp [cost,independentCoordinateCost]; positivity
  have hbudget : 0 ≤ budget := by dsimp [budget,coefficient]; positivity
  have hselected (selected : Finset (Fin 4)) (hs : selected ≠ ∅) :
      inputWeight p body (pool n) bodyPool radius
        (inversePrimarySeed p body (v7Activation C n) operator
          (referenceCoefficientSeed p r (independentPairedPositiveMass C n (beta n) charts) selected)) ≤ budget := by
    have hinv := hi body bodyPool radius hradius
      (referenceCoefficientSeed p r (independentPairedPositiveMass C n (beta n) charts) selected)
    unfold responseInputWeight at hinv
    rw [referenceCoefficientSeed_weight] at hinv
    have horder : (referenceCoefficientSeed p r (independentPairedPositiveMass C n (beta n) charts) selected).primaryOrder = selected.card := by
      simp only [referenceCoefficientSeed,primaryFiniteSeed,Fintype.card_coe]
    rw [horder] at hinv
    simp only [← one_div] at hinv
    change _ ≤ (4/v7Activation C n)^selected.card*MixedKernel.activity
      (fun _ : selected => rate) (fun _ : selected => p)
      (LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => p) (fun _ : Fin 4 => r)
        (independentPairedPositiveMass C n (beta n) charts) selected) at hinv
    by_cases hone : selected.card=1
    · have hraw := hl charts hc selected hone rate hrate.1.le hrate.2.1
      have hbound := hinv.trans (mul_le_mul_of_nonneg_left hraw (pow_nonneg (div_nonneg (by norm_num) hrho.le) _))
      have he : (4/v7Activation C n)^selected.card*(4112*rate)=4112*cost := by
        rw [hone,pow_one]
        dsimp [cost,independentCoordinateCost,rate]
        ring
      change _ ≤ (4/v7Activation C n)^selected.card*(4112*rate) at hbound
      rw [he] at hbound
      apply hbound.trans
      have hh := mul_le_mul_of_nonneg_left (independentCoordinateCost_le C hC n (pool n) hn ht.2.2)
        (by norm_num : (0 : ℝ) ≤ 4112)
      apply hh.trans
      dsimp [budget,coefficient]
      rw [add_div]
      have hnonneg : 0 ≤ (2*2097152*100000000 : ℝ)*(8*activationConstant C)^2/(n : ℝ)^(43/4 : ℝ) := by positivity
      convert le_add_of_nonneg_right (a := 4112*(8*activationConstant C)/(n : ℝ)^(43/4 : ℝ)) hnonneg using 1; ring
    · have hdegree : 2 ≤ selected.card := by
        have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        omega
      have hraw := hh charts hc selected rate hrate.1.le hrate.2.1 hrate.2.2
      have hbound := hinv.trans (mul_le_mul_of_nonneg_left hraw (pow_nonneg (div_nonneg (by norm_num) hrho.le) _))
      have he : (4/v7Activation C n)^selected.card*((2*2097152*100000000)*rate^selected.card*(n : ℝ)^4) =
          coefficient*cost^selected.card*(n : ℝ)^4 := by
        dsimp [coefficient,cost,independentCoordinateCost,rate]
        rw [mul_pow]
        ring
      change _ ≤ (4/v7Activation C n)^selected.card*((2*2097152*100000000)*rate^selected.card*(n : ℝ)^4) at hbound
      rw [he] at hbound
      apply hbound.trans
      have hpow := pow_le_pow_of_le_one hcost0 hcost.1 hdegree
      have hnext : coefficient*cost^selected.card*(n : ℝ)^4 ≤
          coefficient*((8*activationConstant C)^2/(n : ℝ)^(43/4 : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (n : ℝ)^4 by positivity)
        have hmult := mul_le_mul_of_nonneg_left (hh.trans hcost.2) (show 0 ≤ coefficient by norm_num [coefficient])
        calc
          _ = coefficient*(cost^selected.card*(n : ℝ)^4) := by ring
          _ ≤ _ := hmult
      apply hnext.trans
      dsimp [budget]
      rw [add_div]
      have hnonneg : 0 ≤ 4112*(8*activationConstant C)/(n : ℝ)^(43/4 : ℝ) := by positivity
      convert le_add_of_nonneg_left (a := coefficient*(8*activationConstant C)^2/(n : ℝ)^(43/4 : ℝ)) hnonneg using 1; ring
  have htable := referenceCoefficientTable_inverse_activity_le p body r (pool n) bodyPool radius
    (v7Activation C n) hradius operator (independentPairedPositiveMass C n (beta n) charts) (fun _ => budget) hselected
  apply htable.trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 4))).erase ∅).card : ℝ) ≤ 16 := by
    exact_mod_cast ((Finset.card_le_univ ((Finset.univ : Finset (Finset (Fin 4))).erase ∅)).trans_eq (by simp))
  rw [Finset.sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcard hbudget).trans_eq (by
    dsimp [budget,coefficient,independentPositiveInputConstant]
    ring)


def independentPositiveReciprocal (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) (depth : ℕ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  finiteCorrection (independentPositiveInputTable C n beta operator charts) depth

/-- Every finite local reciprocal has activity at most two, with its
smallness discharged from the actual V7 parameters, uniformly in depth. -/
theorem independentPositiveReciprocal_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius → ∀ depth : ℕ,
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (pool n) bodyPool radius) (independentPositiveReciprocal C n (beta n) operator charts depth) ≤ 2 := by
  have ht : Tendsto (fun n : ℕ => independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ)) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 43/4)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop _
  have hs := Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2) ht
  filter_upwards [independentPositiveInputTable_activity_eventually C hC beta pool htypical,hs]
    with n h hs operator hop charts hc bodyPool radius hradius depth
  exact activity_finiteCorrection_le_two _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _
    ((h operator hop charts hc bodyPool radius hradius).trans hs)

end
end AFT.V7Calibration

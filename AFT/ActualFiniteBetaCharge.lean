import AFT.ActualFiniteBetaReference
import AFT.ZeroSumHistogram

/-! # Finite beta sampling followed by actual zero-charge conditioning -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualFiniteBetaChargeFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualReferenceZeroChargeHistogram (C : ℝ) (n : ℕ) (beta : ℝ) :
    FiniteDist (Histogram (Parameters.dimension n) (Fin (Parameters.modulus n))) :=
  let law := actualPositiveReferenceHistogram C n beta
  let event := fun hist => histogramCharge (Parameters.dimension n) hist=0
  if h : 0 < law.eventMass event then law.condition event h
  else uniformZeroSumHistogram (Parameters.dimension n) (Fin (Parameters.modulus n))

def actualFiniteBetaZeroChargeHistogram (C : ℝ) (n : ℕ) :
    FiniteDist (Histogram (Parameters.dimension n) (Fin (Parameters.modulus n))) :=
  (actualFiniteBetaSource n).mix fun j => actualReferenceZeroChargeHistogram C n (actualFiniteBetaValue n j)

def actualBetaChargeSamplingError (C : ℝ) (n : ℕ) : ℝ :=
  2*actualReferenceChargeError C n+4*(Parameters.modulus n : ℝ)*actualBetaSamplingError C n

private theorem modulus_population_upper :
    ∀ᶠ n in atTop,Parameters.modulus n ≤ 2*n^60 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hq := (Parameters.modulus_bounds n).2
  rw [Parameters.security_eq n hn] at hq
  exact hq.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 40 ≤ 60)))

/-- The actual finite beta mixture, with charge imposed separately at each
sampled parameter, has the full histogram of uniform zero-sum vectors as its
target. No interchange of mixture and conditioning is assumed. -/
theorem actual_finite_beta_zero_charge_histogram_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,FiniteDist.TVBound (actualFiniteBetaZeroChargeHistogram C n)
      (uniformZeroSumHistogram (Parameters.dimension n) (Fin (Parameters.modulus n)))
      (actualBetaChargeSamplingError C n) := by
  have hsmall := ((actualBetaSamplingError_negligible C hC).const_mul 4).inverse_population_bound
    Parameters.modulus (fun n => (Parameters.modulus_prime n).pos) modulus_population_upper 1
  filter_upwards [actual_finite_beta_uniform_histogram_eventually C hC,
    actual_reference_mix_charge_eventually C hC,hsmall] with n htv hmix hs
  have hq : (0 : ℝ) < Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hN : 0 < Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hb := Parameters.bodies_positive n
    omega
  let event := fun hist : Histogram (Parameters.dimension n) (Fin (Parameters.modulus n)) =>
    histogramCharge (Parameters.dimension n) hist=0
  have hsmall' : 2*actualBetaSamplingError C n ≤ (Parameters.modulus n : ℝ)⁻¹/2 := by
    rw [pow_one,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hs
    have hh := le_abs_self (actualBetaSamplingError C n)
    simpa only [one_div] using (show 2*actualBetaSamplingError C n ≤ (1/(Parameters.modulus n : ℝ))/2 by linarith)
  obtain ⟨hpos,hcond⟩ := htv.condition event (inv_pos.mpr hq)
    (by dsimp only [event]; rw [uniform_histogram_charge_decidable _ hN]; simp only [Fintype.card_fin,le_refl]) hsmall'
  have htarget := uniform_histogram_condition_decidable (G:=Fin (Parameters.modulus n)) (Parameters.dimension n) hN
  have hcond' : FiniteDist.TVBound ((actualFiniteBetaHistogram C n).condition event hpos)
      (uniformZeroSumHistogram (Parameters.dimension n) (Fin (Parameters.modulus n)))
      (4*(Parameters.modulus n : ℝ)*actualBetaSamplingError C n) := by
    dsimp only [event] at hcond
    rw [htarget] at hcond
    simpa only [div_inv_eq_mul,mul_assoc,mul_left_comm,mul_comm] using hcond
  obtain ⟨hmpos,hlaw,hl1⟩ := hmix (Fin (2^n)) (actualFiniteBetaSource n) (actualFiniteBetaValue n) 0
  have hinterchange : FiniteDist.TVBound (actualFiniteBetaZeroChargeHistogram C n)
      ((actualFiniteBetaHistogram C n).condition event hpos) (2*actualReferenceChargeError C n) := by
    apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr
    rw [FiniteDist.totalVariation_eq_half_l1]
    have he : actualFiniteBetaZeroChargeHistogram C n=
        (actualFiniteBetaSource n).mix (fun j => (actualPositiveReferenceHistogram C n (actualFiniteBetaValue n j)).condition event (hlaw j)) := by
      unfold actualFiniteBetaZeroChargeHistogram
      congr 1
      funext j
      simp only [actualReferenceZeroChargeHistogram,dif_pos (hlaw j)]
      rfl
    rw [he]
    change (∑ hist,|((actualFiniteBetaSource n).mix
      (fun j => (actualPositiveReferenceHistogram C n (actualFiniteBetaValue n j)).condition event (hlaw j))).weight hist-
      ((actualFiniteBetaHistogram C n).condition event hpos).weight hist|)/2 ≤ _
    change (∑ hist,|((actualFiniteBetaSource n).mix
      (fun j => (actualPositiveReferenceHistogram C n (actualFiniteBetaValue n j)).condition event (hlaw j))).weight hist-
      ((actualFiniteBetaHistogram C n).condition event hmpos).weight hist|) ≤ _ at hl1
    linarith
  exact hinterchange.triangle hcond'

theorem actualBetaChargeSamplingError_negligible (C : ℝ) (hC : 1 ≤ C) :
    Negligible (actualBetaChargeSamplingError C) := by
  have hweighted : Negligible (fun n => (Parameters.modulus n : ℝ)*actualBetaSamplingError C n) := by
    apply ((actualBetaSamplingError_negligible C hC).mul_polynomial 60 |>.const_mul 2).of_eventually_le
    filter_upwards [modulus_population_upper] with n hn
    have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^60 := by exact_mod_cast hn
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (2*(n : ℝ)^60)*|actualBetaSamplingError C n| := mul_le_mul_of_nonneg_right hq (abs_nonneg _)
      _ = _ := by simp only [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)^60)]; ring
  have hh := ((actual_reference_charge_error_negligible C hC).const_mul 2).add (hweighted.const_mul 4)
  convert hh using 1
  funext n
  unfold actualBetaChargeSamplingError
  ring

end
end AFT.V7Calibration

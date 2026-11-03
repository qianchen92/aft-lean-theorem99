import AFT.PairDensityFibers
import AFT.V7PairInputFibers

/-! # The complete safe-pair residual has the required mixed activity -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G]

theorem pair_residual_density_fibers (parameter q constant : ℝ)
    (hp : 0 < parameter) (hq : 0 < q) (hc : 0 ≤ constant)
    (hqUpper : q ≤ 2 * parameter ^ 40) (reference : G → ℝ)
    (href : ∀ x, 1 / (4 * q) ≤ reference x) (mass : G × G → ℝ)
    (hrow : RowBound (4 * constant / (q * parameter ^ 16)) mass)
    (hcolumn : RowBound (4 * constant / (q * parameter ^ 16)) (fun point => mass point.swap))
    (hpoint : SupBound (8 * constant / (q * parameter ^ 32)) mass) :
    (∑ x, ∑ y, reference x * reference y * (mass (x,y) / (reference x * reference y)) ^ 2) ≤
      16 * (q * countingL2 mass) ^ 2 ∧
    (∀ x, (∑ y, reference y * (mass (x,y) / (reference x * reference y)) ^ 2) ≤
      (64 * constant * parameter ^ 4) ^ 2) ∧
    (∀ y, (∑ x, reference x * (mass (x,y) / (reference x * reference y)) ^ 2) ≤
      (64 * constant * parameter ^ 4) ^ 2) ∧
    (∀ x y, |mass (x,y) / (reference x * reference y)| ≤ 256 * constant * parameter ^ 8) := by
  have hscalar : (4 * constant / (q * parameter ^ 16)) ^ 2 / (1 / (4*q)) ^ 3 ≤
      (64 * constant * parameter ^ 4) ^ 2 := by
    calc
      _ = 1024 * constant ^ 2 * q / parameter ^ 32 := by field_simp; ring
      _ ≤ 1024 * constant ^ 2 * (2 * parameter ^ 40) / parameter ^ 32 := by gcongr
      _ = 2048 * constant ^ 2 * parameter ^ 8 := by field_simp; ring
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg constant) (pow_nonneg hp.le 8)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (pair_density_energy_le mass reference (1/(4*q)) (countingL2 mass)
      (by positivity) href le_rfl).trans_eq (by field_simp; ring)
  · intro x
    exact (hrow.density_fiber reference (1/(4*q)) (by positivity) href x).trans hscalar
  · intro y
    have hh := (hcolumn.density_fiber reference (1/(4*q)) (by positivity) href y).trans hscalar
    simpa only [mul_comm] using hh
  · intro x y
    apply (TrimmedSlice.pairDifference_density_sup (fun x y => mass (x,y)) reference (1/(4*q))
      (8*constant/(q*parameter^32)) (by positivity) (by positivity) href (fun x y => hpoint (x,y)) x y).trans
    calc
      _ = 128 * constant * q / parameter ^ 32 := by field_simp; ring
      _ ≤ 128 * constant * (2 * parameter ^ 40) / parameter ^ 32 := by gcongr
      _ = _ := by field_simp; ring

/-- The full-error square and the two coarse fixed fibers suffice for the
complete activity: every fixed-coordinate subset remains present. -/
theorem activated_pair_residual_activity_le (parameter q constant activationCost completeCost rate : ℝ)
    (hp : 1 ≤ parameter) (hq : 0 < q) (hc : 0 ≤ constant) (_ha : 0 ≤ activationCost)
    (hcomplete : 0 ≤ completeCost) (hrate0 : 0 ≤ rate) (hrate : rate ≤ 2 / parameter ^ 15)
    (hqUpper : q ≤ 2 * parameter ^ 40) (reference : FiniteDist G)
    (href : ∀ x, 1 / (4 * q) ≤ reference.weight x) (mass : G × G → ℝ) (activationInverse : ℝ)
    (hactivation0 : 0 ≤ activationInverse) (hactivation : activationInverse ≤ activationCost ^ 2 * parameter ^ 9)
    (hfull : (activationInverse * (q * countingL2 mass)) ^ 2 ≤ activationCost ^ 4 * completeCost / parameter ^ 4)
    (hrow : RowBound (4 * constant / (q * parameter ^ 16)) mass)
    (hcolumn : RowBound (4 * constant / (q * parameter ^ 16)) (fun point => mass point.swap))
    (hpoint : SupBound (8 * constant / (q * parameter ^ 32)) mass) :
    MixedKernel.activity ![rate,rate] (MixedKernel.pairReference reference reference)
      (MixedKernel.pairKernel (fun x y => activationInverse * mass (x,y) / (reference.weight x * reference.weight y))) ≤
      rate ^ 2 * (activationCost ^ 2 * (4 * Real.sqrt completeCost + 1280 * constant) / parameter ^ 2) := by
  have hp0 : 0 < parameter := zero_lt_one.trans_le hp
  have hf := pair_residual_density_fibers parameter q constant hp0 hq hc hqUpper reference.weight href mass hrow hcolumn hpoint
  have hfull' : (∑ x, ∑ y, reference.weight x * reference.weight y *
      (activationInverse * mass (x,y) / (reference.weight x * reference.weight y)) ^ 2) ≤
      (4 * activationCost ^ 2 * Real.sqrt completeCost / parameter ^ 2) ^ 2 := by
    calc
      _ = activationInverse ^ 2 * (∑ x, ∑ y, reference.weight x * reference.weight y *
          (mass (x,y) / (reference.weight x * reference.weight y)) ^ 2) := by
        simp only [Finset.mul_sum]
        congr 1; ext x
        congr 1; ext y
        ring
      _ ≤ activationInverse ^ 2 * (16 * (q * countingL2 mass) ^ 2) :=
        mul_le_mul_of_nonneg_left hf.1 (sq_nonneg _)
      _ = 16 * (activationInverse * (q * countingL2 mass)) ^ 2 := by ring
      _ ≤ 16 * (activationCost ^ 4 * completeCost / parameter ^ 4) := by gcongr
      _ = _ := by rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hcomplete]; ring
  have hfixed (density : G → ℝ) (h : (∑ x, reference.weight x * density x ^ 2) ≤ (64*constant*parameter^4)^2) :
      (∑ x, reference.weight x * (activationInverse*density x)^2) ≤ (64*activationCost^2*constant*parameter^13)^2 := by
    calc
      _ = activationInverse ^ 2 * ∑ x, reference.weight x * density x ^ 2 := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ activationInverse ^ 2 * (64*constant*parameter^4)^2 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ ≤ (activationCost ^ 2 * parameter ^ 9) ^ 2 * (64*constant*parameter^4)^2 := by gcongr
      _ = _ := by ring
  have hpoint' (x y : G) :
      |activationInverse * mass (x,y) / (reference.weight x * reference.weight y)| ≤
        256*activationCost^2*constant*parameter^17 := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg hactivation0]
    exact (mul_le_mul hactivation (hf.2.2.2 x y) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hactivity := MixedKernel.pair_activity_le reference reference
    (fun x y => activationInverse * mass (x,y) / (reference.weight x * reference.weight y)) rate rate
    (4*activationCost^2*Real.sqrt completeCost/parameter^2)
    (64*activationCost^2*constant*parameter^13) (64*activationCost^2*constant*parameter^13)
    (256*activationCost^2*constant*parameter^17) hrate0 hrate0 (by positivity) (by positivity) (by positivity) (by positivity)
    hfull' (fun x => by simpa only [mul_div_assoc] using hfixed _ (hf.2.1 x))
    (fun y => by simpa only [mul_div_assoc] using hfixed _ (hf.2.2.1 y)) hpoint'
  apply hactivity.trans
  have hfixedRate : rate * (64*activationCost^2*constant*parameter^13) ≤
      128*activationCost^2*constant / parameter^2 := by
    calc
      _ ≤ (2/parameter^15) * (64*activationCost^2*constant*parameter^13) := by gcongr
      _ = _ := by field_simp; ring
  have hsupRate : rate ^ 2 * (256*activationCost^2*constant*parameter^17) ≤
      1024*activationCost^2*constant / parameter^2 := by
    calc
      _ ≤ (2/parameter^15)^2 * (256*activationCost^2*constant*parameter^17) := by gcongr
      _ = 1024*activationCost^2*constant / parameter^13 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hp (by decide))
  rw [← pow_two]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg rate)
  exact (add_le_add (add_le_add (add_le_add le_rfl hfixedRate) hfixedRate) hsupRate).trans_eq (by ring)

end AFT.SafeConvolution

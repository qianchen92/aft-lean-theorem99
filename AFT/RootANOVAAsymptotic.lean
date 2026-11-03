import AFT.RootANOVAParameters

/-!
# Half-order decay for the actual V7 root kernels
-/

namespace AFT.GaussianSource

open Filter
open scoped Classical Topology

noncomputable section

def rootANOVAConstant (order : ℕ) : ℝ :=
  let halfOrder := (order + 1) / 2
  4 * ((order : ℝ) + 1) ^ (2 * halfOrder) *
      (((2 * halfOrder).factorial : ℝ) / (1 / 8 : ℝ) ^ (2 * halfOrder)) *
        rootMomentConstant ^ order + 4 * rootMomentConstant ^ order

theorem rootMomentConstant_pos : 0 < rootMomentConstant := by
  unfold rootMomentConstant
  positivity

theorem rootANOVAConstant_pos (order : ℕ) : 0 < rootANOVAConstant order := by
  unfold rootANOVAConstant
  have hm := rootMomentConstant_pos
  positivity

theorem root_anova_budget_bound (population prefactor error : ℝ) (order : ℕ)
    (hn : 0 < population) (hc : prefactor ^ 2 ≤ 2)
    (he : |error| ≤ 1 / population ^ ((order + 1) / 2)) :
    let halfOrder := (order + 1) / 2
    2 * prefactor ^ 2 * ((((order : ℝ) + 1) / population) ^ (2 * halfOrder) *
      (((2 * halfOrder).factorial : ℝ) / (1 / 8 : ℝ) ^ (2 * halfOrder)) *
        rootMomentConstant ^ order) +
      2 * (prefactor * error) ^ 2 * rootMomentConstant ^ order ≤
      rootANOVAConstant order / population ^ (2 * halfOrder) := by
  dsimp only
  let r := (order + 1) / 2
  let moment := (((2 * r).factorial : ℝ) / (1 / 8 : ℝ) ^ (2 * r))
  have hm : 0 < rootMomentConstant := rootMomentConstant_pos
  have hmoment : 0 ≤ moment := by dsimp [moment]; positivity
  have hesq : error ^ 2 ≤ 1 / population ^ (2 * r) := by
    calc
      _ = |error| ^ 2 := (sq_abs error).symm
      _ ≤ (1 / population ^ r) ^ 2 := by gcongr
      _ = _ := by rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm]
  have hmain0 : 0 ≤ (((order : ℝ) + 1) / population) ^ (2 * r) *
      moment * rootMomentConstant ^ order := by positivity
  have hmain := mul_le_mul_of_nonneg_right hc hmain0
  have herr := mul_le_mul hc hesq (sq_nonneg error) (by norm_num : (0 : ℝ) ≤ 2)
  have herr' := mul_le_mul_of_nonneg_right herr (pow_nonneg hm.le order)
  have heq : rootANOVAConstant order / population ^ (2 * r) =
      4 * ((((order : ℝ) + 1) / population) ^ (2 * r) * moment * rootMomentConstant ^ order) +
        4 * (1 / population ^ (2 * r)) * rootMomentConstant ^ order := by
    unfold rootANOVAConstant
    dsimp only [r, moment]
    simp only [div_pow]
    ring
  rw [heq]
  change 2 * prefactor ^ 2 *
      ((((order : ℝ) + 1) / population) ^ (2 * r) * moment * rootMomentConstant ^ order) +
      2 * (prefactor * error) ^ 2 * rootMomentConstant ^ order ≤ _
  nlinarith [hmain, herr']

/-- Lemma 9.12's half-order bound for the squared norm of every fixed
positive order, on the actual V7 clipped-root marginal and population.
All analytic inputs have been instantiated; only the fixed order is a
parameter of this theorem. -/
theorem v7RootKernelSq_decay (order : ℕ) (ho : 0 < order) :
    ∀ᶠ parameter : ℕ in atTop,
      v7RootKernelSq order parameter ≤
        rootANOVAConstant order / (Parameters.bodies parameter : ℝ) ^ (2 * ((order + 1) / 2)) := by
  have hnegligible := negligible_ratioError v7RootErrorBound_negligible
    (Eventually.of_forall v7RootErrorBound_nonneg) order
  have hupper : ∀ᶠ parameter : ℕ in atTop, Parameters.bodies parameter ≤ 2 * parameter ^ 60 := by
    simpa only [Nat.sub_zero] using bodies_sub_fixed_upper_eventually 0
  have hevent := hnegligible.inverse_population_bound Parameters.bodies Parameters.bodies_positive
    hupper ((order + 1) / 2)
  filter_upwards [v7RootKernelSq_explicit_bound_eventually order ho, hevent,
    bodies_sub_fixed_lower_eventually 0, eventually_ge_atTop (2 * order + 2)]
    with parameter hbound he hN hp
  have hp1 : 1 ≤ parameter := by omega
  have hNlarge : 2 * order ≤ Parameters.bodies parameter := by
    have hh : parameter ≤ parameter ^ 3 := le_self_pow₀ hp1 (by decide : 3 ≠ 0)
    omega
  have hw : 0 < v7RootWidth parameter := zero_lt_one.trans_le (v7RootWidth_ge_one parameter hp1)
  have hz : 0 < realNormalizer (v7RootWidth parameter) :=
    zero_lt_one.trans_le (realNormalizer_ge_one (v7RootWidth parameter) hw)
  have hc0 := rootModelPrefactor_positive (v7RootWidth parameter)
    (realNormalizer (v7RootWidth parameter)) (Parameters.bodies parameter) order hw hz ho (by omega)
  have hc := rootModelPrefactor_le_sqrt_two (v7RootWidth parameter)
    (realNormalizer (v7RootWidth parameter)) (Parameters.bodies parameter) order hw hz ho hNlarge
  have hcsq : rootModelPrefactor (v7RootWidth parameter) (realNormalizer (v7RootWidth parameter))
      (Parameters.bodies parameter) order ^ 2 ≤ 2 := by
    have hh := (sq_le_sq₀ hc0.le (Real.sqrt_nonneg 2)).mpr hc
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hh
  exact hbound.trans (root_anova_budget_bound (Parameters.bodies parameter)
    (rootModelPrefactor (v7RootWidth parameter) (realNormalizer (v7RootWidth parameter))
      (Parameters.bodies parameter) order)
    (ratioError (v7RootErrorBound parameter) order) order
    (by exact_mod_cast Parameters.bodies_positive parameter) hcsq he)

end

end AFT.GaussianSource

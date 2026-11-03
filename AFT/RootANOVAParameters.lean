import AFT.RootANOVA
import AFT.RootOneMarginal
import AFT.RootErrorAlgebra

/-!
# Instantiating the root ANOVA estimates at the fixed V7 parameters
-/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem v7RootThetaBound_negligible : AFT.Negligible v7RootThetaBound := by
  have h := AFT.negligible_polynomial_stretched_exponential
    4 0 2 (4 * Real.pi) (by norm_num) (by norm_num) (by positivity)
  convert h using 1
  funext parameter
  simp only [v7RootThetaBound, pow_zero, mul_one, Real.rpow_two]
  congr 1
  congr 1
  ring

theorem v7RootErrorBound_nonneg (parameter : ℕ) : 0 ≤ v7RootErrorBound parameter := by
  unfold v7RootErrorBound
  positivity

theorem v7RootWidth_ge_one (parameter : ℕ) (hp : 1 ≤ parameter) : 1 ≤ v7RootWidth parameter := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hs : 1 ≤ Real.sqrt 8 := by norm_num
  unfold v7RootWidth
  nlinarith

theorem v7RootCutoff_contains_width (parameter : ℕ) (hp : 2 ≤ parameter) :
    ⌊v7RootWidth parameter⌋₊ ≤ v7RootCutoff parameter := by
  apply Nat.floor_le_of_le
  have hp' : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hs : Real.sqrt 8 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg 8]
  have hc : 2 * parameter ^ 2 ≤ v7RootCutoff parameter := by
    unfold v7RootCutoff
    have hh : 1 ≤ parameter ^ 2 := one_le_pow₀ (by omega : 1 ≤ parameter)
    omega
  have hc' : 2 * (parameter : ℝ) ^ 2 ≤ v7RootCutoff parameter := by exact_mod_cast hc
  unfold v7RootWidth
  nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg parameter)]

theorem v7Window_abs (parameter : ℕ) (a : Window (v7RootCutoff parameter)) :
    |(a : ℝ)| ≤ 3 * (parameter : ℝ) ^ 2 := by
  have hc : v7RootCutoff parameter ≤ 3 * parameter ^ 2 := Nat.sub_le _ _
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp a.property
  have hc' : (v7RootCutoff parameter : ℝ) ≤ 3 * (parameter : ℝ) ^ 2 := by exact_mod_cast hc
  have ha' : -(v7RootCutoff parameter : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb' : (a : ℝ) ≤ (v7RootCutoff parameter : ℝ) := by exact_mod_cast hb
  have hlo : -(3 * (parameter : ℝ) ^ 2) ≤ (a : ℝ) := by linarith
  have hhi : (a : ℝ) ≤ 3 * (parameter : ℝ) ^ 2 := by linarith
  exact abs_le.mpr ⟨hlo, hhi⟩

theorem v7Window_sum_abs (parameter order : ℕ)
    (x : Fin order → Window (v7RootCutoff parameter)) :
    |((-∑ i, (x i : ℤ) : ℤ) : ℝ)| ≤ 3 * order * (parameter : ℝ) ^ 2 := by
  push_cast
  rw [abs_neg]
  calc
    _ ≤ ∑ i, |(x i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin order, 3 * (parameter : ℝ) ^ 2 :=
      Finset.sum_le_sum fun i _ => v7Window_abs parameter (x i)
    _ = _ := by simp; ring

theorem v7_rootMarginal_le_four_eventually :
    ∀ᶠ parameter : ℕ in atTop, ∀ a : Window (v7RootCutoff parameter),
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter)
        (Parameters.bodies parameter) (Parameters.bodies_positive parameter)).weight a ≤
          4 * (windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter)).weight a := by
  have htheta := v7RootThetaBound_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have herr := v7RootErrorBound_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [v7_bodies_rootSumError_envelope_eventually 0 0,
    v7_bodies_rootSumError_envelope_eventually 1 1, htheta, herr,
    bodies_sub_fixed_lower_eventually 0, eventually_ge_atTop 2]
    with parameter hroot hmarg ht he hN hp
  intro a
  have hw := v7RootWidth_ge_one parameter (by omega)
  have hn : 2 ≤ Parameters.bodies parameter := by
    have hh := Nat.pow_le_pow_left hp 3
    omega
  have h0 : rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter)
      (v7RootCutoff parameter) (Parameters.bodies parameter - 1) 0 ≤ 1 / 4 := by
    have hh := (hroot 0 (by simp)).trans he.le
    simpa only [Nat.sub_zero] using hh
  have h1 : rootSumError (v7RootWidth parameter) (v7RootThetaBound parameter)
      (v7RootCutoff parameter) (Parameters.bodies parameter - 1 - 1) (-(a : ℤ)) ≤ 1 / 4 := by
    apply (hmarg (-(a : ℤ)) _).trans he.le
    simpa using v7Window_abs parameter a
  have hh := (rootProbability_adjacent_le_four (v7RootWidth parameter) (v7RootThetaBound parameter)
    (v7RootCutoff parameter) (Parameters.bodies parameter) (by linarith) hn
    (by unfold v7RootThetaBound; positivity) ht.le
    (v7RootThetaBound_valid parameter (by omega)) (-(a : ℤ)) h0 h1).2
  unfold rootMarginal
  rw [RootSlice.marginalLaw_weight]
  unfold RootSlice.sumProbability
  convert mul_le_mul_of_nonneg_left hh
    (windowGaussian_positive (v7RootWidth parameter) (v7RootCutoff parameter) a).le using 1 <;>
    dsimp only [rootProbability] <;> ring

/-- At small parameters the total prefix population is `max N order`.
For every fixed order it equals the actual V7 body population eventually. -/
def v7RootKernelSq (order parameter : ℕ) : ℝ :=
  let remaining := Parameters.bodies parameter - order
  let hn : 0 < order + remaining := by
    have h := Parameters.bodies_positive parameter
    dsimp only [remaining]
    omega
  let p := fun _ : Fin order =>
    rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (order + remaining) hn
  (FiniteDist.independent p).l2Sq (Hoeffding.projection p Finset.univ
    (rootPrefixDensity (v7RootWidth parameter) (v7RootCutoff parameter) order remaining hn))

def rootMomentConstant : ℝ := 4 * ((1 + 2 / Real.pi) * Real.sqrt 2 * Real.exp Real.pi)

/-- Every premise in the finite root-ANOVA estimate is discharged for the
V7 family. The remaining displayed scalar error is explicitly negligible. -/
theorem v7RootKernelSq_explicit_bound_eventually (order : ℕ) (ho : 0 < order) :
    ∀ᶠ parameter : ℕ in atTop,
    let population := Parameters.bodies parameter
    let c := rootModelPrefactor (v7RootWidth parameter) (realNormalizer (v7RootWidth parameter))
      population order
    let halfOrder := (order + 1) / 2
    v7RootKernelSq order parameter ≤
      2 * c ^ 2 * ((((order : ℝ) + 1) / population) ^ (2 * halfOrder) *
        (((2 * halfOrder).factorial : ℝ) / (1 / 8 : ℝ) ^ (2 * halfOrder)) *
        rootMomentConstant ^ order) +
      2 * (c * ratioError (v7RootErrorBound parameter) order) ^ 2 * rootMomentConstant ^ order := by
  have htheta := v7RootThetaBound_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have herr := v7RootErrorBound_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [v7_bodies_rootSumError_envelope_eventually order order,
    v7_bodies_rootSumError_envelope_eventually 0 0,
    v7_bodies_rootSumError_envelope_eventually 1 1, v7_rootMarginal_le_four_eventually,
    htheta, herr, bodies_sub_fixed_lower_eventually 0,
    eventually_ge_atTop (16 * (order + 1))] with parameter hrem hroot hmarg hcompare ht he hN hp
  have hp2 : 2 ≤ parameter := by omega
  have hNp : parameter ≤ Parameters.bodies parameter := by
    have hh : parameter ≤ parameter ^ 3 := by
      exact le_self_pow₀ (by omega : 1 ≤ parameter) (by decide : 3 ≠ 0)
    omega
  have hNlarge : 16 * (order + 1) ≤ Parameters.bodies parameter := hp.trans hNp
  have hNk : order ≤ Parameters.bodies parameter := by omega
  have heq : order + (Parameters.bodies parameter - order) = Parameters.bodies parameter := by omega
  have h := rootPrefixDensity_anova_bound (v7RootWidth parameter) (v7RootThetaBound parameter)
    (v7RootErrorBound parameter) (v7RootCutoff parameter) order (Parameters.bodies parameter - order)
    ho (by omega) (v7RootWidth_ge_one parameter (by omega)) (v7RootCutoff_contains_width parameter hp2)
    (by unfold v7RootThetaBound; positivity) ht.le (v7RootThetaBound_valid parameter (by omega))
    (v7RootErrorBound_nonneg parameter) he
    (by
      have hNp' : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
      have hlarge : 16 * ((order : ℝ) + 1) ≤ Parameters.bodies parameter := by exact_mod_cast hNlarge
      have hcast : (order : ℝ) + (Parameters.bodies parameter - order : ℕ) = Parameters.bodies parameter :=
        by exact_mod_cast heq
      rw [hcast]
      have hh : ((order : ℝ) + 1) / (Parameters.bodies parameter : ℝ) ≤ 1 / 16 :=
        (div_le_iff₀ hNp').mpr (by linarith)
      linarith)
    (by simpa only [heq] using hcompare)
    (fun x => hrem _ (v7Window_sum_abs parameter order x))
    (by simpa only [heq, Nat.sub_zero] using hroot 0 (by simp))
    (by intro a; simpa only [heq] using hmarg (-(a : ℤ)) (by simpa using v7Window_abs parameter a))
  simpa only [v7RootKernelSq, rootMomentConstant, ← Nat.cast_add, heq] using h

end

end AFT.GaussianSource

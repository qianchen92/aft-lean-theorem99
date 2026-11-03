import AFT.ActualRootVectors

/-! # Physical independent-root Hilbert summands and their V7 budget -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualRootBudgetFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualRootBudgetSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualFockScale (parameter : ℕ) : ℝ :=
  Real.sqrt 2 * ((parameter : ℝ) ^ 2 / Real.sqrt (Parameters.dimension parameter))

def actualRootIndex (parameter : ℕ) : blockIndex parameter ≃ Fin (Parameters.bodies parameter) :=
  blockIndexNumbering parameter

/-- The normalized body vector of one actual unconditioned root input. -/
def actualRootValue (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (queue : blockIndex parameter → ℤ) (index : Fin (Parameters.bodies parameter))
    (sample : Window (v7RootCutoff parameter)) : EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  actualFockScale parameter • actualBlockBodyVector cutoffScale parameter beta
    ((actualRootIndex parameter).symm index) sample (queue ((actualRootIndex parameter).symm index))

/-- Centering is with respect to the real independent clipped Gaussian,
before imposing the integer root sum. -/
def actualCenteredRootValue (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (queue : blockIndex parameter → ℤ) (index : Fin (Parameters.bodies parameter))
    (sample : Window (v7RootCutoff parameter)) : EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  actualRootValue cutoffScale parameter beta queue index sample -
    vectorMean (windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter))
      (actualRootValue cutoffScale parameter beta queue index)

theorem actualCenteredRootValue_mean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (queue : blockIndex parameter → ℤ) (index : Fin (Parameters.bodies parameter)) :
    vectorMean (windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter))
      (actualCenteredRootValue cutoffScale parameter beta queue index) = 0 :=
  vectorMean_centered _ _

theorem actualFockScale_nonneg (parameter : ℕ) : 0 ≤ actualFockScale parameter := by
  unfold actualFockScale
  positivity

theorem actualFockScale_le (parameter : ℕ) (hp : 2 ≤ parameter) :
    actualFockScale parameter ≤ 2 / (parameter : ℝ) ^ 28 := by
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hd : (parameter : ℝ) ^ 60 ≤ Parameters.dimension parameter := by
    exact_mod_cast (show parameter ^ 60 ≤ Parameters.dimension parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.dimension_bounds parameter).1)
  have hroot : (parameter : ℝ) ^ 30 ≤ Real.sqrt (Parameters.dimension parameter) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by convert hd using 1; ring)
  calc
    _ ≤ 2 * ((parameter : ℝ) ^ 2 / (parameter : ℝ) ^ 30) := by
      apply mul_le_mul (Real.sqrt_two_lt_three_halves.le.trans (by norm_num))
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hroot) (by positivity) (by norm_num)
    _ = _ := by field_simp

/-- Every actual independent-root summand has the original normalized
`lambda^-47` size; neither conditioning nor palette size is paid here. -/
theorem actual_centered_root_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : blockIndex parameter → ℤ,
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) →
      ∀ index sample, ‖actualCenteredRootValue cutoffScale parameter (beta parameter) queue index sample‖ ≤
        296 / (parameter : ℝ) ^ 47 := by
  filter_upwards [actual_body_vector_bound_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hb hp queue hqueue index sample
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hraw (sample : Window (v7RootCutoff parameter)) :
      ‖actualRootValue cutoffScale parameter (beta parameter) queue index sample‖ ≤
        148 / (parameter : ℝ) ^ 47 := by
    rw [actualRootValue, norm_smul, Real.norm_eq_abs, abs_of_nonneg (actualFockScale_nonneg parameter)]
    have hh := mul_le_mul (actualFockScale_le parameter hp)
      (hb ((actualRootIndex parameter).symm index) sample (queue ((actualRootIndex parameter).symm index))
        (abs_le.mpr (Finset.mem_Icc.mp sample.property)) (hqueue ((actualRootIndex parameter).symm index))) (norm_nonneg _) (by positivity)
    apply hh.trans_eq
    field_simp
    ring
  have hh := centered_value_norm_le
    (windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter))
    (actualRootValue cutoffScale parameter (beta parameter) queue index)
    (148 / (parameter : ℝ) ^ 47) hraw sample
  exact hh.trans_eq (by ring)

/-- The actual number of independent roots gives the small total Hilbert
budget required by conditional concentration. -/
theorem actual_root_budget (parameter : ℕ) (hp : 1000000000 ≤ parameter) :
    0 < (∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2) ∧
    (∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2) ≤
      175232 / (parameter : ℝ) ^ 34 ∧
    1024 * (∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2) ≤ 1 := by
  have hp2 : 2 ≤ parameter := by omega
  have hxlarge : (1000000000 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hx : (0 : ℝ) < parameter := by linarith
  have hx1 : (1 : ℝ) ≤ parameter := by linarith
  have hdim : (Parameters.dimension parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by
    exact_mod_cast (show Parameters.dimension parameter ≤ 2 * parameter ^ 60 by
      simpa only [Parameters.security_eq parameter hp2] using (Parameters.dimension_bounds parameter).2)
  have hbody : (Parameters.bodies parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by
    have hh : (Parameters.bodies parameter : ℝ) ≤ Parameters.dimension parameter := by
      exact_mod_cast (show Parameters.bodies parameter ≤ Parameters.dimension parameter by unfold Parameters.bodies; omega)
    exact hh.trans hdim
  have hbpos : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbudget : (Parameters.bodies parameter : ℝ) * (296 / (parameter : ℝ) ^ 47) ^ 2 ≤
      175232 / (parameter : ℝ) ^ 34 := by
    calc
      _ ≤ (2 * (parameter : ℝ) ^ 60) * (296 / (parameter : ℝ) ^ 47) ^ 2 :=
        mul_le_mul_of_nonneg_right hbody (sq_nonneg _)
      _ = _ := by field_simp; ring
  refine ⟨by positivity, hbudget, ?_⟩
  calc
    _ ≤ 1024 * (175232 / (parameter : ℝ) ^ 34) := mul_le_mul_of_nonneg_left hbudget (by norm_num)
    _ ≤ 1024 * (175232 / (parameter : ℝ)) := by
      gcongr
      simpa only [pow_one] using pow_le_pow_right₀ hx1 (by decide : 1 ≤ 34)
    _ ≤ 1 := by rw [← mul_div_assoc]; apply (div_le_iff₀ hx).mpr; norm_num; linarith

end

end AFT.V7Calibration

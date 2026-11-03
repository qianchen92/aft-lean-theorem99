import CurrentAFT.RationalActualFamilyApproximation
import CurrentAFT.RationalFamilyBinomialBounds

/-! # Fixed-order population powers of literal approximate coefficient data -/
namespace CurrentAFT.RationalPopulationApproximation
open AFT GradedControlAlgebra ActualControls BackgroundFamilies
open RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem interpret_binomial (security order population : ℕ)
    (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order) :
    interpret security order (RationalFamilyProductProgram.binomial order population table) =
      RationalFamilyProductProgram.binomial order population (interpret security order table) := by
  unfold interpret
  rw [RationalFamilyProductProgram.binomial_cast, RationalFamilyProductProgram.pullback_binomial]

theorem data_binomial (security order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) :
    RationalFamilyProductProgram.binomial order population (data security order family) =
      data security order ((1+family)^population) :=
  RationalFamilyProductProgram.binomial_actual (ProposalPrimary.primaryLaw security) (bodyReference security)
    order population family hzero

def bound (order population : ℕ) (A : ℝ) :=
  ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)*
    (RationalFamilyProductProgram.growth order A 0)^(order+1)

def error (order population : ℕ) (A e : ℝ) :=
  ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)^2*e*
    (RationalFamilyProductProgram.growth order A e)^(order+1)

theorem bound_nonneg (order population : ℕ) (A : ℝ) (hA : 0 ≤ A) : 0 ≤ bound order population A := by
  have hg := (RationalFamilyProductProgram.growth_ge_one order A 0 hA (by norm_num)).trans' (by norm_num : (0:ℝ)≤1)
  unfold bound
  positivity

theorem error_nonneg (order population : ℕ) (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e) :
    0 ≤ error order population A e := by
  have hg := (RationalFamilyProductProgram.growth_ge_one order A e hA he).trans' (by norm_num : (0:ℝ)≤1)
  unfold error
  positivity

theorem binomial_bound (security order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ arity colors centers, |data security order family arity colors centers| ≤ A)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |data security order ((1+family)^population) arity colors centers| ≤ bound order population A := by
  rw [← data_binomial security order population family hzero]
  let scale := RationalFamilyProductProgram.growth order A 0
  have hs : 1 ≤ scale := RationalFamilyProductProgram.growth_ge_one order A 0 hA (by norm_num)
  have hscale : (Nat.card (TruncatedArity order):ℝ)^2*A ≤ scale := by
    unfold scale RationalFamilyProductProgram.growth
    nlinarith [sq_nonneg (Nat.card (TruncatedArity order):ℝ)]
  unfold RationalFamilyProductProgram.binomial
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _count ∈ Finset.range (order+1), ((population+1:ℕ):ℝ)^(order+1)*scale^(order+1) := by
      apply Finset.sum_le_sum
      intro count hcount
      have hc : count ≤ order+1 := by have := Finset.mem_range.mp hcount; omega
      have hn : (population.choose count:ℝ) ≤ ((population+1:ℕ):ℝ)^(order+1) := by
        exact_mod_cast (Nat.choose_le_pow population count).trans
          ((Nat.pow_le_pow_left (by omega : population≤population+1) count).trans (Nat.pow_le_pow_right (by omega : 1≤population+1) hc))
      have hp := (RationalFamilyProductProgram.power_bound order (data security order family) A scale hA hs hscale ha count arity colors centers).trans
        (pow_le_pow_right₀ hs hc)
      rw [abs_mul, abs_of_nonneg (show (0:ℝ)≤population.choose count by positivity)]
      exact mul_le_mul hn hp (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, bound]; dsimp only [scale]; ring

theorem binomial_error (security bits order population : ℕ) (family : ActualFamily security order)
    (hzero : family (zeroArity order)=0) (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (A e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (ha : ∀ arity colors centers, |data security order family arity colors centers| ≤ A)
    (hea : ∀ arity colors centers, |interpret security order table arity colors centers-data security order family arity colors centers| ≤ e*(1/(2:ℝ)^bits))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → FirstHistogram.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalFamilyProductProgram.binomial order population table) arity colors centers-
      data security order ((1+family)^population) arity colors centers| ≤ error order population A e*(1/(2:ℝ)^bits) := by
  have hε : (0:ℝ)≤1/2^bits := by positivity
  have hε1 : 1/(2:ℝ)^bits ≤ 1 :=
    (div_le_one (by positivity : (0:ℝ)<2^bits)).mpr (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  rw [interpret_binomial, ← data_binomial security order population family hzero]
  have h := RationalFamilyProductProgram.binomial_error order population (data security order family)
    (interpret security order table) A (e*(1/(2:ℝ)^bits)) hA (mul_nonneg he hε) ha hea arity colors centers
  apply h.trans
  have hg : RationalFamilyProductProgram.growth order A (e*(1/(2:ℝ)^bits)) ≤ RationalFamilyProductProgram.growth order A e := by
    unfold RationalFamilyProductProgram.growth
    nlinarith [mul_le_mul_of_nonneg_left hε1 he, sq_nonneg (Nat.card (TruncatedArity order):ℝ)]
  calc
    _ ≤ ((population+1:ℕ):ℝ)^(order+1)*((order+1:ℕ):ℝ)^2*(e*(1/(2:ℝ)^bits))*
        (RationalFamilyProductProgram.growth order A e)^(order+1) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by have := RationalFamilyProductProgram.growth_ge_one order A (e*(1/(2:ℝ)^bits)) hA (mul_nonneg he hε); linarith) hg _)
      positivity
    _ = _ := by unfold error; ring

end
end CurrentAFT.RationalPopulationApproximation

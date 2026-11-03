import AFT.ActualRootGaussianProgram
import AFT.RationalFiniteQuantization
import AFT.ActualRootIntegerProgram

/-! # Actual root Gaussian weights, integer tickets, and fair-bit sampling -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- The ticket guard absorbs the support size; the Gaussian program itself
uses one additional precision bit so both errors fit in the requested budget. -/
def actualRootTicketBits (n bits : ℕ) : ℕ := bits+(2*(3*n^2-1)+1)+2

theorem actualRootGaussianWeights_nonneg (n bits : ℕ) (index : Fin (2*(3*n^2-1)+1)) :
    0 ≤ actualRootGaussianWeights n bits index := (windowApproxWeight_positive _ _ _ _).le

theorem actualRootGaussianWeights_sum (n bits : ℕ) : ∑ index,actualRootGaussianWeights n bits index=1 := by
  unfold actualRootGaussianWeights
  rw [(windowIndexEquiv (3*n^2-1)).sum_comp]
  exact windowApproxWeight_sum _ _ _

def actualRootTicketCounts (n bits : ℕ) : Fin (2*(3*n^2-1)+1) → ℕ :=
  RationalFiniteQuantization.counts (actualRootGaussianWeights n (bits+1)) (2^(actualRootTicketBits n bits))

theorem actualRootTicketCounts_sum (n bits : ℕ) :
    ∑ index,actualRootTicketCounts n bits index=2^(actualRootTicketBits n bits) :=
  RationalFiniteQuantization.counts_total _ (actualRootGaussianWeights_nonneg n (bits+1))
    (actualRootGaussianWeights_sum n (bits+1)) _

/-- This actual scalar source uses rational arithmetic and a displayed fixed
number of fair bits. It evaluates neither real exponentials nor real floors. -/
def actualRootGaussianDraw (n bits : ℕ) (word : Fin (actualRootTicketBits n bits) → Fin 2) : Window (3*n^2-1) :=
  windowIndexEquiv _ (RationalFiniteQuantization.draw (actualRootGaussianWeights n (bits+1))
    (actualRootGaussianWeights_nonneg _ _) (actualRootGaussianWeights_sum _ _)
    (actualRootTicketBits n bits) word)

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def actualRootTicketLaw (n bits : ℕ) : FiniteDist (Window (v7RootCutoff n)) :=
  (RationalFiniteQuantization.roundedLaw (actualRootGaussianWeights n (bits+1))
    (actualRootGaussianWeights_nonneg _ _) (actualRootGaussianWeights_sum _ _)
    (2^(actualRootTicketBits n bits)) (by positivity)).map (windowIndexEquiv _)

theorem actualRootGaussianDraw_law (n bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (actualRootTicketBits n bits) => FiniteDist.uniform (Fin 2))).map
      (actualRootGaussianDraw n bits)=actualRootTicketLaw n bits := by
  unfold actualRootGaussianDraw actualRootTicketLaw
  rw [← FiniteDist.map_map,RationalFiniteQuantization.draw_law]

theorem actualRootTicketLaw_weight (n bits : ℕ) (point : Window (v7RootCutoff n)) :
    (actualRootTicketLaw n bits).weight point=
      (actualRootTicketCounts n bits ((windowIndexEquiv _).symm point) : ℝ)/(2 : ℝ)^(actualRootTicketBits n bits) := by
  have hh := FiniteDist.map_equiv_weight
    (RationalFiniteQuantization.roundedLaw (actualRootGaussianWeights n (bits+1))
      (actualRootGaussianWeights_nonneg _ _) (actualRootGaussianWeights_sum _ _)
      (2^(actualRootTicketBits n bits)) (by positivity)) (windowIndexEquiv (3*n^2-1)) point
  simpa only [actualRootTicketLaw,RationalFiniteQuantization.roundedLaw,
    actualRootTicketCounts,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem actualRootTicketLaw_rounding_l1 (n bits : ℕ) :
    (∑ point,|(actualRootTicketLaw n bits).weight point-(actualRootGaussianLaw n (bits+1)).weight point|) ≤
      1/(2 : ℝ)^(bits+1) := by
  have hh := RationalFiniteQuantization.roundedLaw_l1_le (actualRootGaussianWeights n (bits+1))
    (actualRootGaussianWeights_nonneg _ _) (actualRootGaussianWeights_sum _ _)
    (2^(actualRootTicketBits n bits)) (by positivity)
  have heq : (∑ point,|(actualRootTicketLaw n bits).weight point-(actualRootGaussianLaw n (bits+1)).weight point|)=
      ∑ index,|(RationalFiniteQuantization.roundedLaw (actualRootGaussianWeights n (bits+1))
        (actualRootGaussianWeights_nonneg _ _) (actualRootGaussianWeights_sum _ _)
        (2^(actualRootTicketBits n bits)) (by positivity)).weight index-(actualRootGaussianWeights n (bits+1) index : ℝ)| := by
    rw [← (windowIndexEquiv (v7RootCutoff n)).sum_comp]
    apply Finset.sum_congr rfl
    intro index _
    rw [actualRootTicketLaw_weight]
    simp only [v7RootCutoff,Equiv.symm_apply_apply,actualRootGaussianLaw,windowApproxLaw,
      actualRootGaussianWeights,RationalFiniteQuantization.roundedLaw,
      actualRootTicketCounts,Nat.cast_pow,Nat.cast_ofNat]

  rw [heq]
  apply hh.trans
  have hpow : ((2*(3*n^2-1)+1 : ℕ) : ℝ) ≤ (2 : ℝ)^(2*(3*n^2-1)+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=2*(3*n^2-1)+1)).le
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ 2*((2 : ℝ)^(2*(3*n^2-1)+1))/(2 : ℝ)^(actualRootTicketBits n bits) := by
      gcongr
      exact_mod_cast hpow
    _ = _ := by unfold actualRootTicketBits; rw [pow_add,pow_add,pow_add]; field_simp; ring

theorem actualRootTicketLaw_l1 (n bits : ℕ) (hn : 0 < n) :
    (∑ point,|(actualRootTicketLaw n bits).weight point-
      (windowGaussian (v7RootWidth n) (v7RootCutoff n)).weight point|) ≤ 1/(2 : ℝ)^bits := by
  have htriangle := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Window (v7RootCutoff n)))) =>
    abs_sub_le ((actualRootTicketLaw n bits).weight point) ((actualRootGaussianLaw n (bits+1)).weight point)
      ((windowGaussian (v7RootWidth n) (v7RootCutoff n)).weight point))
  rw [Finset.sum_add_distrib] at htriangle
  apply htriangle.trans
  apply (add_le_add (actualRootTicketLaw_rounding_l1 n bits) (actualRootGaussianLaw_l1 n (bits+1) hn)).trans_eq
  rw [pow_succ]
  field_simp
  norm_num

local instance actualRootGaussianTicketsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The fair-bit source, after conditioning all actual roots to sum zero,
approximates the literal protected Gaussian root law with negligible error. -/
theorem actual_root_ticket_conditioning_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ hpos : 0 < RootSlice.sumProbability (actualRootTicketLaw n n)
          (fun point => (point : ℤ)) (Parameters.bodies n) 0,
        TVBound (RootSlice.law (fun _ : Fin (Parameters.bodies n) => actualRootTicketLaw n n)
          (fun point => (point : ℤ)) 0 hpos)
          (RootSlice.law (fun _ : Fin (Parameters.bodies n) => windowGaussian (v7RootWidth n) (v7RootCutoff n))
            (fun point => (point : ℤ)) 0 (window_root_probability_positive _ _ _))
          (actualRootNumericalError n) := by
  filter_upwards [actual_root_numerical_conditioning_eventually,Filter.eventually_ge_atTop 1] with n hh hn
  exact hh (actualRootTicketLaw n n) (actualRootTicketLaw_l1 n n hn)

theorem actualRootTicketBits_bound (n : ℕ) (hn : 2 ≤ n) : actualRootTicketBits n n ≤ 8*n^2 := by
  unfold actualRootTicketBits
  have h : n ≤ n^2 := by nlinarith
  have h1 : 3 ≤ n^2 := by nlinarith
  omega

end
end AFT.V7Calibration

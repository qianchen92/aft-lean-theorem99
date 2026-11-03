import AFT.CenteredGaussianSampling
import AFT.RationalFiniteQuantization

/-! # Executable fair-bit scalar Gaussians at arbitrary rational centers -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

def centeredGaussianWeights (squaredWidth center : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) : ℚ :=
  centeredWindowWeight squaredWidth center cutoff bits (windowIndexEquiv cutoff index)

theorem centeredGaussianWeights_nonneg (squaredWidth center : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    0≤centeredGaussianWeights squaredWidth center cutoff bits index := (centeredWindowWeight_positive _ _ _ _ _).le

theorem centeredGaussianWeights_sum (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    ∑ index,centeredGaussianWeights squaredWidth center cutoff bits index=1 := by
  unfold centeredGaussianWeights
  rw [(windowIndexEquiv cutoff).sum_comp]
  exact centeredWindowWeight_sum _ _ _ _

def centeredTicketCounts (squaredWidth center : ℚ) (cutoff bits : ℕ) : Fin (2*cutoff+1) → ℕ :=
  RationalFiniteQuantization.counts (centeredGaussianWeights squaredWidth center cutoff (bits+1))
    (2^(windowTicketBits cutoff bits))

theorem centeredTicketCounts_sum (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    ∑ index,centeredTicketCounts squaredWidth center cutoff bits index=2^(windowTicketBits cutoff bits) :=
  RationalFiniteQuantization.counts_total _ (centeredGaussianWeights_nonneg _ _ _ _)
    (centeredGaussianWeights_sum _ _ _ _) _

def centeredGaussianDraw (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : Window cutoff :=
  windowIndexEquiv cutoff (RationalFiniteQuantization.draw (centeredGaussianWeights squaredWidth center cutoff (bits+1))
    (centeredGaussianWeights_nonneg _ _ _ _) (centeredGaussianWeights_sum _ _ _ _) (windowTicketBits cutoff bits) word)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def centeredTicketLaw (squaredWidth center : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) :=
  (RationalFiniteQuantization.roundedLaw (centeredGaussianWeights squaredWidth center cutoff (bits+1))
    (centeredGaussianWeights_nonneg _ _ _ _) (centeredGaussianWeights_sum _ _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)).map (windowIndexEquiv cutoff)

theorem centeredGaussianDraw_law (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))).map
      (centeredGaussianDraw squaredWidth center cutoff bits)=centeredTicketLaw squaredWidth center cutoff bits := by
  unfold centeredGaussianDraw centeredTicketLaw
  rw [← FiniteDist.map_map,RationalFiniteQuantization.draw_law]

theorem centeredTicketLaw_weight (squaredWidth center : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (centeredTicketLaw squaredWidth center cutoff bits).weight point=
      (centeredTicketCounts squaredWidth center cutoff bits ((windowIndexEquiv cutoff).symm point) : ℝ)/
        (2 : ℝ)^(windowTicketBits cutoff bits) := by
  have hh := FiniteDist.map_equiv_weight
    (RationalFiniteQuantization.roundedLaw (centeredGaussianWeights squaredWidth center cutoff (bits+1))
      (centeredGaussianWeights_nonneg _ _ _ _) (centeredGaussianWeights_sum _ _ _ _)
      (2^(windowTicketBits cutoff bits)) (by positivity)) (windowIndexEquiv cutoff) point
  simpa only [centeredTicketLaw,RationalFiniteQuantization.roundedLaw,
    centeredTicketCounts,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem centeredTicketLaw_rounding_l1 (squaredWidth center : ℚ) (cutoff bits : ℕ) :
    (∑ point,|(centeredTicketLaw squaredWidth center cutoff bits).weight point-
      (centeredWindowApproxLaw squaredWidth center cutoff (bits+1)).weight point|)≤1/(2 : ℝ)^(bits+1) := by
  have hh := RationalFiniteQuantization.roundedLaw_l1_le (centeredGaussianWeights squaredWidth center cutoff (bits+1))
    (centeredGaussianWeights_nonneg _ _ _ _) (centeredGaussianWeights_sum _ _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)
  have heq : (∑ point,|(centeredTicketLaw squaredWidth center cutoff bits).weight point-
      (centeredWindowApproxLaw squaredWidth center cutoff (bits+1)).weight point|)=
      ∑ index,|(RationalFiniteQuantization.roundedLaw (centeredGaussianWeights squaredWidth center cutoff (bits+1))
        (centeredGaussianWeights_nonneg _ _ _ _) (centeredGaussianWeights_sum _ _ _ _)
        (2^(windowTicketBits cutoff bits)) (by positivity)).weight index-
          (centeredGaussianWeights squaredWidth center cutoff (bits+1) index : ℝ)| := by
    rw [← (windowIndexEquiv cutoff).sum_comp]
    apply Finset.sum_congr rfl
    intro index _
    rw [centeredTicketLaw_weight]
    simp only [Equiv.symm_apply_apply,centeredWindowApproxLaw,centeredGaussianWeights,
      RationalFiniteQuantization.roundedLaw,centeredTicketCounts,Nat.cast_pow,Nat.cast_ofNat]
  rw [heq]
  apply hh.trans
  have hpow : ((2*cutoff+1 : ℕ) : ℝ)≤(2 : ℝ)^(2*cutoff+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1))/(2 : ℝ)^(windowTicketBits cutoff bits) := by
      gcongr
      exact_mod_cast hpow
    _ = _ := by unfold windowTicketBits; rw [pow_add,pow_add,pow_add]; field_simp; ring

/-- Error against the actual Gaussian, including both analytic approximation
and ticket rounding. The square-root relation is only used in the theorem. -/
theorem centeredTicketLaw_l1 (squaredWidth center : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 1≤width) (hsquare : (squaredWidth : ℝ)=width^2) :
    (∑ point,|(centeredTicketLaw squaredWidth center cutoff bits).weight point-
      (centeredWindowLaw width center cutoff).weight point|)≤1/(2 : ℝ)^bits := by
  have htriangle := Finset.sum_le_sum (fun point (_ : point∈(Finset.univ : Finset (Window cutoff))) =>
    abs_sub_le ((centeredTicketLaw squaredWidth center cutoff bits).weight point)
      ((centeredWindowApproxLaw squaredWidth center cutoff (bits+1)).weight point) ((centeredWindowLaw width center cutoff).weight point))
  rw [Finset.sum_add_distrib] at htriangle
  apply htriangle.trans
  apply (add_le_add (centeredTicketLaw_rounding_l1 squaredWidth center cutoff bits)
    (centeredWindowApproxLaw_l1 squaredWidth center width cutoff (bits+1) hwidth hsquare.symm)).trans_eq
  rw [pow_succ]
  field_simp
  norm_num

end
end AFT.RationalNumerics

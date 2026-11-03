import AFT.RationalWindowGaussian
import AFT.RationalFiniteQuantization

/-! # Executable fair-bit approximations to every finite Gaussian window -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

def windowTicketBits (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+2

def windowGaussianWeights (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) : ℚ :=
  windowApproxWeight squaredWidth cutoff bits (windowIndexEquiv cutoff index)

theorem windowGaussianWeights_nonneg (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    0≤windowGaussianWeights squaredWidth cutoff bits index := (windowApproxWeight_positive _ _ _ _).le

theorem windowGaussianWeights_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ index,windowGaussianWeights squaredWidth cutoff bits index=1 := by
  unfold windowGaussianWeights
  rw [(windowIndexEquiv cutoff).sum_comp]
  exact windowApproxWeight_sum _ _ _

def windowTicketCounts (squaredWidth : ℚ) (cutoff bits : ℕ) : Fin (2*cutoff+1) → ℕ :=
  RationalFiniteQuantization.counts (windowGaussianWeights squaredWidth cutoff (bits+1))
    (2^(windowTicketBits cutoff bits))

theorem windowTicketCounts_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ index,windowTicketCounts squaredWidth cutoff bits index=2^(windowTicketBits cutoff bits) :=
  RationalFiniteQuantization.counts_total _ (windowGaussianWeights_nonneg _ _ _)
    (windowGaussianWeights_sum _ _ _) _

def windowGaussianDraw (squaredWidth : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : Window cutoff :=
  windowIndexEquiv cutoff (RationalFiniteQuantization.draw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _) (windowTicketBits cutoff bits) word)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def windowTicketLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) :=
  (RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)).map (windowIndexEquiv cutoff)

theorem windowGaussianDraw_law (squaredWidth : ℚ) (cutoff bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))).map
      (windowGaussianDraw squaredWidth cutoff bits)=windowTicketLaw squaredWidth cutoff bits := by
  unfold windowGaussianDraw windowTicketLaw
  rw [← FiniteDist.map_map,RationalFiniteQuantization.draw_law]

theorem windowTicketLaw_weight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (windowTicketLaw squaredWidth cutoff bits).weight point=
      (windowTicketCounts squaredWidth cutoff bits ((windowIndexEquiv cutoff).symm point) : ℝ)/
        (2 : ℝ)^(windowTicketBits cutoff bits) := by
  have hh := FiniteDist.map_equiv_weight
    (RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
      (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
      (2^(windowTicketBits cutoff bits)) (by positivity)) (windowIndexEquiv cutoff) point
  simpa only [windowTicketLaw,RationalFiniteQuantization.roundedLaw,
    windowTicketCounts,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem windowTicketLaw_rounding_l1 (squaredWidth : ℚ) (cutoff bits : ℕ) :
    (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowApproxLaw squaredWidth cutoff (bits+1)).weight point|)≤1/(2 : ℝ)^(bits+1) := by
  have hh := RationalFiniteQuantization.roundedLaw_l1_le (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)
  have heq : (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowApproxLaw squaredWidth cutoff (bits+1)).weight point|)=
      ∑ index,|(RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
        (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
        (2^(windowTicketBits cutoff bits)) (by positivity)).weight index-
          (windowGaussianWeights squaredWidth cutoff (bits+1) index : ℝ)| := by
    rw [← (windowIndexEquiv cutoff).sum_comp]
    apply Finset.sum_congr rfl
    intro index _
    rw [windowTicketLaw_weight]
    simp only [Equiv.symm_apply_apply,windowApproxLaw,windowGaussianWeights,
      RationalFiniteQuantization.roundedLaw,windowTicketCounts,Nat.cast_pow,Nat.cast_ofNat]
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
theorem windowTicketLaw_l1 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hpositive : 0<squaredWidth) (hsquare : (squaredWidth : ℝ)=width^2) :
    (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|)≤1/(2 : ℝ)^bits := by
  have htriangle := Finset.sum_le_sum (fun point (_ : point∈(Finset.univ : Finset (Window cutoff))) =>
    abs_sub_le ((windowTicketLaw squaredWidth cutoff bits).weight point)
      ((windowApproxLaw squaredWidth cutoff (bits+1)).weight point) ((windowGaussian width cutoff).weight point))
  rw [Finset.sum_add_distrib] at htriangle
  apply htriangle.trans
  apply (add_le_add (windowTicketLaw_rounding_l1 squaredWidth cutoff bits)
    (windowApproxLaw_l1 squaredWidth width cutoff (bits+1) hpositive hsquare.symm)).trans_eq
  rw [pow_succ]
  field_simp
  norm_num

end
end AFT.RationalNumerics

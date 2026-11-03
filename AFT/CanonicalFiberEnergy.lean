import AFT.LocalTensors
import AFT.MixedFiberLower

/-! # Complete mixed fibers of actual canonical local coefficients -/

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance canonicalFiberSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- The literal restricted Hoeffding component has Hilbert norm at most
the full signed density, with no palette or degree loss. -/
theorem restrictedComponent_energy_le (reference : Slot → FiniteDist Color)
    (href : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    (FiniteDist.independent (fun slot : selected => reference slot)).l2Sq
      (restrictedComponent reference mass selected) ≤
      profileSquareNorm (FiniteDist.independent reference).weight mass := by
  have hh := localTensor_energy_le reference href mass selected
  rw [localTensor, whitenedTensor_energy] at hh
  change _ ≤ densitySquareNorm _ _ at hh
  rwa [densityScore_square] at hh

/-- Every fixed-output fiber of every actual canonical local coefficient
is controlled by the correct per-coordinate atom penalty. -/
theorem restrictedComponent_fiber_le (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (fixed : Finset selected) (values : selected → Color) :
    MixedKernel.fiberSq (fun slot : selected => reference slot) (restrictedComponent reference mass selected) fixed values ≤
      profileSquareNorm (FiniteDist.independent reference).weight mass / lower ^ fixed.card := by
  have hf := MixedKernel.fiberSq_le_lower (fun slot : selected => reference slot) lower hlower
    (fun slot color => href slot color) (restrictedComponent reference mass selected) fixed values
  exact hf.trans (div_le_div_of_nonneg_right
    (restrictedComponent_energy_le reference (fun slot color => hlower.trans_le (href slot color)) mass selected)
    (pow_nonneg hlower.le _))

/-- The full activity is formed from the literal restricted coefficient,
not from an infimum over output representations. -/
theorem restrictedComponent_activity_le (reference : Slot → FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (rate : ℝ) (hrate : 0 ≤ rate) :
    MixedKernel.activity (fun _ : selected => rate) (fun slot : selected => reference slot)
      (restrictedComponent reference mass selected) ≤
      rate ^ selected.card * (1 + rate / Real.sqrt lower) ^ selected.card *
        Real.sqrt (profileSquareNorm (FiniteDist.independent reference).weight mass) := by
  have hh := MixedKernel.activity_le_lower (fun slot : selected => reference slot) lower hlower
    (fun slot color => href slot color) rate hrate (restrictedComponent reference mass selected)
  simp only [Fintype.card_coe] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (restrictedComponent_energy_le reference (fun slot color => hlower.trans_le (href slot color)) mass selected))
  exact mul_nonneg (pow_nonneg hrate _) (pow_nonneg (by positivity) _)

end
end AFT.LocalTensors

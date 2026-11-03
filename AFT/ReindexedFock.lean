import AFT.PackedFockEvaluation
import AFT.ReindexedCoefficients

/-! # Exact invariance of the complete tagged budget under physical placement -/
namespace AFT.HistogramNormalization
open scoped BigOperators Classical
noncomputable section
variable {Slot OtherSlot Color : Type*} [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

/-- Any bijective physical placement preserves the entire marked Fock
budget, allowing the paired four outputs to occupy a triple and its separate
compensator position without a loss in the bound. -/
theorem taggedCoefficientEnergy_renamedMass (equiv : Slot ≃ OtherSlot) (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (population : ℕ) (radius : ℝ) :
    BlockProducts.taggedCoefficientEnergy reference (renamedMass equiv mass) population radius =
      BlockProducts.taggedCoefficientEnergy reference mass population radius := by
  rw [LocalTensors.taggedCoefficientEnergy_gaussian, LocalTensors.taggedCoefficientEnergy_gaussian]
  simp_rw [generating_renamedMass]
  rw [Fintype.card_congr equiv]

end
end AFT.HistogramNormalization

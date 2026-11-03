import AFT.SymmetricCoefficients

/-! # Renaming physical output positions preserves all constructed coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot OtherSlot Color : Type*}
variable [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

/-- Rename the actual finite word's physical position type. -/
def renameWord (equiv : Slot ≃ OtherSlot) : (Slot → Color) ≃ (OtherSlot → Color) where
  toFun word := word ∘ equiv.symm
  invFun word := word ∘ equiv
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp

/-- The signed mass of a renamed physical law. -/
noncomputable def renamedMass (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ)
    (word : OtherSlot → Color) : ℝ := mass (word ∘ equiv)

set_option backward.isDefEq.respectTransparency false in
/-- A position renaming leaves the exact centered-color polynomial unchanged. -/
theorem generating_renamedMass (equiv : Slot ≃ OtherSlot) (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : OtherSlot => reference) (renamedMass equiv mass) value =
      LocalTensors.localGenerating (fun _ : Slot => reference) mass value := by
  have h := (renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (mass word : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value))
  have hprod (word : OtherSlot → Color) :
      (∏ slot, (1 + LocalTensors.atomLinear reference ((word ∘ equiv) slot) value)) =
        ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value) :=
    equiv.prod_comp (fun slot => 1 + LocalTensors.atomLinear reference (word slot) value)
  change (∑ word : OtherSlot → Color, (mass (word ∘ equiv) : ℂ) *
    ∏ slot, (1 + LocalTensors.atomLinear reference ((word ∘ equiv) slot) value)) = _ at h
  simpa only [hprod] using h

set_option backward.isDefEq.respectTransparency false in
/-- All actual symmetric coefficients are unchanged by renaming positions. -/
theorem degreeTensor_renamedMass (equiv : Slot ≃ OtherSlot) (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (hdegree : degree ≤ Fintype.card Slot) :
    LocalTensors.degreeTensor (fun _ : OtherSlot => reference) (renamedMass equiv mass) degree =
      LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree := by
  apply TensorFock.series_coefficients_unique (Finset.range (Fintype.card Slot + 1))
    (LocalTensors.degreeTensor (fun _ : OtherSlot => reference) (renamedMass equiv mass))
    (LocalTensors.degreeTensor (fun _ : Slot => reference) mass)
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
    _ degree (Finset.mem_range.mpr (Nat.lt_succ_of_le hdegree))
  intro value
  rw [← LocalTensors.localGenerating_series_of_bound _ _ (Fintype.card Slot)
    (Fintype.card_congr equiv).symm.le, ← LocalTensors.localGenerating_series]
  exact generating_renamedMass equiv reference mass value

/-- The actual renamed finite probability law has the explicit renamed mass. -/
theorem rename_law_weight (equiv : Slot ≃ OtherSlot) (law : FiniteDist (Slot → Color))
    (word : OtherSlot → Color) :
    (law.map (renameWord equiv)).weight word = renamedMass equiv law.weight word := by
  rw [FiniteDist.map_equiv_weight]
  rfl

end HistogramNormalization
end AFT

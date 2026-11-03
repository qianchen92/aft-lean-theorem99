import AFT.FirstCoefficient

/-! # The exact first Fock coefficient of an arbitrary signed finite mass -/

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance signedFirstCoefficientFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The full signed one-point color count, before subtracting its total mass. -/
def signedColorCount (mass : (Slot → Color) → ℝ) (color : Color) : ℝ :=
  ∑ input, mass input * ∑ slot, if input slot = color then (1 : ℝ) else 0

/-- The actual first symmetric coefficient is the sum of the whitened
one-site responses, preserving cancellation between all physical outputs. -/
theorem signed_degreeTensor_one_formula (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ input, mass input * ∑ slot, atomCoefficient reference (input slot) color := by
  have hpiece (selected : Finset Slot) :
      degreePiece (fun _ => reference) mass 1 selected (fun _ => color) =
        if selected.card = 1 then localTensor (fun _ => reference) mass selected (fun _ => color) else 0 := by
    by_cases h : selected.card = 1
    · have hh : Fintype.card selected = 1 := by simpa using h
      simp only [degreePiece, dif_pos hh, if_pos h, Function.comp_def]
    · have hh : Fintype.card selected ≠ 1 := by simpa using h
      simp only [degreePiece, dif_neg hh, if_neg h]
  have hsym : degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      ∑ selected : Finset Slot, degreePiece (fun _ => reference) mass 1 selected (fun _ => color) := by
    unfold degreeTensor BlockFock.symmetrize
    simp only [Function.comp_def]
    rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rw [hsym]
  simp_rw [hpiece]
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun selected : Finset Slot => selected.card = 1) =
      Finset.univ.powersetCard 1 := by ext selected; simp
  rw [hsets, Finset.powersetCard_one, Finset.sum_map]
  simp_rw [localTensor_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  congr 1
  change (∏ selected : ({slot} : Finset Slot), atomCoefficient reference (input selected) color) = _
  exact (Finset.prod_coe_sort ({slot} : Finset Slot)
    (fun index => atomCoefficient reference (input index) color)).trans (Finset.prod_singleton _ _)

/-- For zero total signed mass the exact first coefficient is the whitened
signed count profile, with no loss from bounding the output slots separately. -/
theorem degreeTensor_one_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) (color : Color) :
    degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) =
      signedColorCount mass color / Real.sqrt (reference.weight color) := by
  rw [signed_degreeTensor_one_formula]
  have hs : Real.sqrt (reference.weight color) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (href color))
  have hsq := Real.sq_sqrt (reference.nonneg color)
  have hatom (input : Color) : atomCoefficient reference input color =
      (if input = color then (1 : ℝ) else 0) / Real.sqrt (reference.weight color) -
        Real.sqrt (reference.weight color) := by
    unfold atomCoefficient Hoeffding.centeredAtom
    split_ifs <;> field_simp [hs, (href color).ne'] <;> nlinarith [hsq]
  simp_rw [hatom]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_sub]
  rw [← Finset.sum_mul, hmass, zero_mul, sub_zero]
  unfold signedColorCount
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.sum_div]
  ring

/-- The first-degree Fock energy equals the actual signed count-profile
energy exactly. This applies to every finite output block and signed mass. -/
theorem degreeTensor_one_energy_zero_mass (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∑ input, mass input = 0) :
    BlockFock.tensorEnergy (degreeTensor (fun _ : Slot => reference) mass 1) =
      profileSquareNorm reference.weight (signedColorCount mass) := by
  unfold BlockFock.tensorEnergy profileSquareNorm
  have he := (Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word => degreeTensor (fun _ : Slot => reference) mass 1 word ^ 2)
  rw [← he]
  apply Finset.sum_congr rfl
  intro color _
  change degreeTensor (fun _ : Slot => reference) mass 1 (fun _ => color) ^ 2 = _
  rw [degreeTensor_one_zero_mass reference href mass hmass, div_pow,
    Real.sq_sqrt (reference.nonneg color)]

end
end AFT.LocalTensors

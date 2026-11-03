import AFT.LocalCoefficientLinear
import AFT.V7Blocks

/-! # Complete Fock energy of a genuine canonical singleton response -/

namespace AFT.LocalTensors

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance singletonFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The degree-zero tensor is exactly the total signed mass. -/
theorem degreeTensor_zero_formula (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (word : Fin 0 → Color) :
    degreeTensor reference mass 0 word = ∑ input, mass input := by
  have hp (selected : Finset Slot) (point : Fin 0 → Color) :
      degreePiece reference mass 0 selected point = if selected = ∅ then ∑ input, mass input else 0 := by
    by_cases hs : selected = ∅
    · subst selected
      simp [degreePiece, localTensor_formula]
    · have hc : Fintype.card selected ≠ 0 := fun hh => hs (Finset.card_eq_zero.mp (by simpa only [Fintype.card_coe] using hh))
      simp only [degreePiece, dif_neg hc, if_neg hs]
  simp only [degreeTensor, BlockFock.symmetrize, hp, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

omit [Fintype Slot] in
/-- The signed singleton output has exactly its weighted profile energy. -/
theorem singleton_density_energy (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (profile : Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 1 => reference)).l2Sq
      (fun word => profile (word 0) / (FiniteDist.independent (fun _ : Fin 1 => reference)).weight word) =
      profileSquareNorm reference.weight profile := by
  unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent profileSquareNorm
  simp only [Fin.prod_univ_one]
  have heq (word : Fin 1 → Color) :
      reference.weight (word 0) * (profile (word 0) / reference.weight (word 0)) ^ 2 =
        profile (word 0) ^ 2 / reference.weight (word 0) := by field_simp [(href (word 0)).ne']
  simp only [heq]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp (fun word => profile (word 0) ^ 2 / reference.weight (word 0))).symm

omit [Fintype Slot] in
/-- The complete canonical singleton Fock response has the required one
power of radius divided by square-root population. -/
theorem singleton_tagged_energy_le (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (profile : Color → ℝ) (hzero : ∑ color, profile color = 0) (population : ℕ) (radius : ℝ) :
    BlockProducts.taggedCoefficientEnergy reference (fun word : Fin 1 → Color => profile (word 0)) population radius ≤
      8 * (radius / Real.sqrt population) ^ 2 * profileSquareNorm reference.weight profile := by
  have hm : (∑ word : Fin 1 → Color, profile (word 0)) = 0 := by
    rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp (fun word => profile (word 0))]
    exact hzero
  have hz (word : Fin 0 → Color) : degreeTensor (fun _ : Fin 1 => reference) (fun word => profile (word 0)) 0 word = 0 := by
    rw [degreeTensor_zero_formula, hm]
  have he := degreeTensor_energy_le (fun _ : Fin 1 => reference) (fun _ => href)
    (fun word => profile (word 0)) 1
  rw [singleton_density_energy reference href] at he
  simp only [Fintype.card_fin, pow_one] at he
  unfold BlockProducts.taggedCoefficientEnergy TensorFock.normalizedTensor
  simp only [Fintype.card_fin, show 1 + 1 = 2 by rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, hz, BlockFock.tensorEnergy, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, one_mul, mul_pow,
    ← Finset.mul_sum]
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, one_pow, Finset.sum_const_zero, mul_zero, zero_add, Nat.cast_ofNat]
  change 2 * (2 * ((radius / Real.sqrt population) ^ 2 *
    BlockFock.tensorEnergy (degreeTensor (fun _ : Fin 1 => reference) (fun word => profile (word 0)) 1))) ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (radius / Real.sqrt population))]

end
end AFT.LocalTensors

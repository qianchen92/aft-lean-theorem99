import AFT.FirstCoefficient

/-! # Exact first coefficient of a genuine physical block -/

namespace AFT.LocalTensors

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

omit [Fintype Color] in
/-- A constant color word is fixed by every slot permutation. -/
theorem symmetrize_constant {Index : Type*} [Fintype Index]
    (tensor : BlockFock.Tensor Index Color) (color : Color) :
    BlockFock.symmetrize tensor (fun _ => color) = tensor (fun _ => color) := by
  simp only [BlockFock.symmetrize, Function.comp_def, ← Finset.sum_mul,
    (FiniteDist.uniform (Equiv.Perm Index)).sum_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-one array is the sum of the whitened centered
marginals, with no estimate or replacement of the joint law. -/
theorem degreeTensor_one_formula (reference : Slot → FiniteDist Color)
    (law : FiniteDist (Slot → Color)) (color : Color) :
    degreeTensor reference law.weight 1 (fun _ => color) =
      ∑ slot, Real.sqrt ((reference slot).weight color) *
        ((law.map (fun input => input slot)).weight color / (reference slot).weight color - 1) := by
  rw [degreeTensor, symmetrize_constant]
  have hpiece (selected : Finset Slot) :
      degreePiece reference law.weight 1 selected (fun _ => color) =
        if selected.card = 1 then localTensor reference law.weight selected (fun _ => color) else 0 := by
    by_cases h : selected.card = 1
    · have h' : Fintype.card selected = 1 := by simpa using h
      simp only [degreePiece, dif_pos h', if_pos h, Function.comp_def]
    · have h' : Fintype.card selected ≠ 1 := by simpa using h
      simp only [degreePiece, dif_neg h', if_neg h]
  simp only [hpiece]
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun selected : Finset Slot => selected.card = 1) =
      Finset.univ.powersetCard 1 := by ext selected; simp
  rw [hsets, Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro slot _
  change localTensor reference law.weight {slot} (fun _ => color) = _
  unfold localTensor whitenedTensor
  have hprod : (∏ index : ({slot} : Finset Slot),
      Real.sqrt ((reference index).weight color)) = Real.sqrt ((reference slot).weight color) := by
    exact (Finset.prod_coe_sort ({slot} : Finset Slot) (fun index =>
      Real.sqrt ((reference index).weight color))).trans (by simp)
  rw [hprod]
  have heq := restrictedComponent_eq reference law.weight {slot} (fun _ => color)
  rw [heq, densityComponent_singleton]

/-- With a positive reference, the first coefficient is exactly the
whitened sum of marginal deviations. -/
theorem degreeTensor_one_whitened (reference : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) (law : FiniteDist (Slot → Color)) (color : Color) :
    degreeTensor (fun _ => reference) law.weight 1 (fun _ => color) =
      (∑ slot, ((law.map (fun input => input slot)).weight color - reference.weight color)) /
        Real.sqrt (reference.weight color) := by
  rw [degreeTensor_one_formula, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro slot _
  have hs := Real.sq_sqrt (href color).le
  have hsp := Real.sqrt_pos.mpr (href color)
  field_simp [(href color).ne', hsp.ne']
  rw [hs]

end AFT.LocalTensors

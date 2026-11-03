import AFT.LocalTensors

/-! # Actual first block coefficient from its marginal color laws -/

namespace AFT.LocalTensors

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

theorem independent_single_coordinate (reference : Slot → FiniteDist Color) (slot : Slot)
    (value : Color → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => value (word slot)) =
      (reference slot).expectation value := by
  rw [FiniteDist.expectation_independent_split reference slot]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_true]
  rw [← Finset.sum_mul]
  have hmass := (FiniteDist.independent (fun rest : {other : Slot // other ≠ slot} => reference rest)).sum_one
  change (∑ rest : {other : Slot // other ≠ slot} → Color,
    ∏ other : {other : Slot // other ≠ slot}, (reference other).weight (rest other)) = 1 at hmass
  rw [hmass, one_mul]
  rfl

/-- A genuine one-site canonical coefficient is exactly its marginal density
minus one. Its input is the actual joint block law. -/
theorem densityComponent_singleton (reference : Slot → FiniteDist Color)
    (law : FiniteDist (Slot → Color)) (slot : Slot) (word : Slot → Color) :
    Hoeffding.densityComponent reference law.weight {slot} word =
      (law.map (fun input => input slot)).weight (word slot) / (reference slot).weight (word slot) - 1 := by
  unfold Hoeffding.densityComponent Hoeffding.centeredAtom
  simp only [Finset.prod_singleton, mul_sub, mul_one, Finset.sum_sub_distrib, law.sum_one]
  congr 1
  simp only [FiniteDist.map_weight, div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul, mul_ite, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual first marginal coefficient has precisely its centered profile
energy; unused output positions integrate out exactly. -/
theorem singleton_energy (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (law : FiniteDist (Slot → Color)) (slot : Slot) :
    BlockFock.tensorEnergy (localTensor reference law.weight {slot}) =
      profileSquareNorm (reference slot).weight
        (fun color => (law.map (fun input => input slot)).weight color - (reference slot).weight color) := by
  rw [localTensor_energy_eq reference law.weight {slot}]
  unfold FiniteDist.l2Sq
  simp_rw [densityComponent_singleton]
  rw [independent_single_coordinate reference slot
    (fun color => ((law.map (fun input => input slot)).weight color / (reference slot).weight color - 1) ^ 2)]
  unfold FiniteDist.expectation profileSquareNorm
  apply Finset.sum_congr rfl
  intro color _
  field_simp [(hreference slot color).ne']

/-- Every fixed-degree coefficient retains only its true selected marginals
in the finite Cauchy--Schwarz bound. -/
theorem degreeTensor_selected_energy_le (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (degreeTensor reference mass degree) ≤
      (2 : ℝ) ^ Fintype.card Slot *
        ∑ selected : Finset Slot, if selected.card = degree then
          BlockFock.tensorEnergy (localTensor reference mass selected) else 0 := by
  apply (BlockFock.symmetrize_energy_le _).trans
  apply (tensorEnergy_sum_le (degreePiece reference mass degree)).trans
  have hpiece (selected : Finset Slot) :
      BlockFock.tensorEnergy (degreePiece reference mass degree selected) =
        if selected.card = degree then BlockFock.tensorEnergy (localTensor reference mass selected) else 0 := by
    by_cases h : selected.card = degree
    · have h' : Fintype.card selected = degree := by simpa using h
      simp only [degreePiece, dif_pos h', if_pos h]
      exact tensorEnergy_reindex _ _
    · have h' : Fintype.card selected ≠ degree := by simpa using h
      simp only [degreePiece, dif_neg h', if_neg h, BlockFock.tensorEnergy, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
  simp only [hpiece, Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
  exact le_rfl

/-- The first coefficient of any concrete block is bounded by its actual
centered one-site marginals. This preserves the much smaller first-order
scale than bounding by the entire triple density. -/
theorem first_degree_energy_le (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (law : FiniteDist (Slot → Color)) :
    BlockFock.tensorEnergy (degreeTensor reference law.weight 1) ≤
      (2 : ℝ) ^ Fintype.card Slot * ∑ slot,
        profileSquareNorm (reference slot).weight
          (fun color => (law.map (fun input => input slot)).weight color - (reference slot).weight color) := by
  apply (degreeTensor_selected_energy_le reference law.weight 1).trans_eq
  congr 1
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun selected : Finset Slot => selected.card = 1) =
      Finset.univ.powersetCard 1 := by ext selected; simp
  rw [hsets, Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro slot _
  exact singleton_energy reference hreference law slot

end AFT.LocalTensors

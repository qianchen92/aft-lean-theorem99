import AFT.FiniteDisintegration

/-! # Independent coordinates conditioned on their complete public record -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot State Record : Type*} [Fintype Slot] [Fintype State] [Fintype Record]

theorem independent_map_coordinates (law : Slot → FiniteDist State) (record : Slot → State → Record) :
    (independent law).map (fun word slot => record slot (word slot)) =
      independent (fun slot => (law slot).map (record slot)) := by
  ext values
  simp only [map_weight, independent]
  change (∑ word : Slot → State, if (fun slot => record slot (word slot)) = values then ∏ slot, (law slot).weight (word slot) else 0) =
    ∏ slot, ∑ point, if record slot point = values slot then (law slot).weight point else 0
  have he := Fintype.prod_sum (fun slot point => if record slot point = values slot then (law slot).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

theorem independent_record_mass (law : Slot → FiniteDist State) (record : Slot → State → Record)
    (values : Slot → Record) :
    (independent law).eventMass (fun word => (fun slot => record slot (word slot)) = values) =
      ∏ slot, (law slot).eventMass (fun point => record slot point = values slot) := by
  change ((independent law).map (fun word slot => record slot (word slot))).weight values = _
  rw [independent_map_coordinates]
  rfl

theorem independent_record_coordinate_positive (law : Slot → FiniteDist State) (record : Slot → State → Record)
    (values : Slot → Record)
    (hpos : 0 < (independent law).eventMass (fun word => (fun slot => record slot (word slot)) = values)) (slot : Slot) :
    0 < (law slot).eventMass (fun point => record slot point = values slot) := by
  rw [independent_record_mass] at hpos
  have hn : (law slot).eventMass (fun point => record slot point = values slot) ≠ 0 := by
    intro hz
    have he := Finset.prod_eq_zero (f := fun slot => (law slot).eventMass (fun point => record slot point = values slot)) (Finset.mem_univ slot) hz
    exact hpos.ne' he
  exact lt_of_le_of_ne ((law slot).eventMass_nonneg _) (Ne.symm hn)

/-- Exact product conditional law, with no lower bound on a cell mass. -/
theorem independent_condition_record (law : Slot → FiniteDist State) (record : Slot → State → Record)
    (values : Slot → Record)
    (hpos : 0 < (independent law).eventMass (fun word => (fun slot => record slot (word slot)) = values)) :
    (independent law).condition (fun word => (fun slot => record slot (word slot)) = values) hpos =
      independent (fun slot => (law slot).condition (fun point => record slot point = values slot)
        (independent_record_coordinate_positive law record values hpos slot)) := by
  ext word
  simp only [condition, independent]
  change (if (fun slot => record slot (word slot)) = values then ∏ slot, (law slot).weight (word slot) else 0) /
      (independent law).eventMass (fun word => (fun slot => record slot (word slot)) = values) =
    ∏ slot, ((if record slot (word slot) = values slot then (law slot).weight (word slot) else 0) /
      (law slot).eventMass (fun point => record slot point = values slot))
  rw [Finset.prod_div_distrib, Fintype.prod_ite_zero, independent_record_mass]
  simp only [funext_iff]

theorem recordConditional_independent (law : Slot → FiniteDist State) (record : Slot → State → Record)
    (cell : {values // 0 < ((independent law).map (fun word slot => record slot (word slot))).weight values}) :
    recordConditional (independent law) (fun word slot => record slot (word slot)) cell =
      independent (fun slot => (law slot).condition (fun point => record slot point = cell.val slot)
        (independent_record_coordinate_positive law record cell.val cell.property slot)) :=
  independent_condition_record law record cell.val cell.property
end
end AFT.FiniteDist

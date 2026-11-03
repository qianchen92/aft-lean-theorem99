import AFT.PhysicalBlockTensors

/-! # Exact mass and first-count Fubini formulas for four signed outputs -/

namespace AFT.PhysicalBlockTensors

open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem four_output_sum (function : (Fin 4 → Color) → ℝ) :
    (∑ word, function word) =
      ∑ first, ∑ second, ∑ attached, ∑ compensator,
        function ![first, second, attached, compensator] := by
  rw [← quadrupleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

theorem four_output_product_mass (triple : Color → Color → Color → ℝ) (last : Color → ℝ) :
    (∑ word : Fin 4 → Color, triple (word 0) (word 1) (word 2) * last (word 3)) =
      (∑ first, ∑ second, ∑ attached, triple first second attached) * ∑ compensator, last compensator := by
  rw [four_output_sum]
  change (∑ first, ∑ second, ∑ attached, ∑ compensator, triple first second attached * last compensator) = _
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

def fourOutputCount (mass : (Fin 4 → Color) → ℝ) (color : Color) : ℝ :=
  ∑ word, mass word * ∑ slot : Fin 4, if word slot = color then 1 else 0

def tripleOutputCount (mass : Color → Color → Color → ℝ) (color : Color) : ℝ :=
  ∑ first, ∑ second, ∑ attached, mass first second attached *
    ((if first = color then 1 else 0) + (if second = color then 1 else 0) +
      (if attached = color then 1 else 0))

/-- A signed attached triple and an independent signed compensator. Neither
factor is required to be nonnegative or normalized. -/
theorem four_output_product_count (triple : Color → Color → Color → ℝ)
    (last : Color → ℝ) (color : Color) :
    fourOutputCount (fun word => triple (word 0) (word 1) (word 2) * last (word 3)) color =
      tripleOutputCount triple color * (∑ compensator, last compensator) +
        (∑ first, ∑ second, ∑ attached, triple first second attached) * last color := by
  unfold fourOutputCount
  rw [four_output_sum]
  simp only [Fin.sum_univ_four]
  change (∑ first, ∑ second, ∑ attached, ∑ compensator,
    triple first second attached * last compensator *
      ((if first = color then 1 else 0) + (if second = color then 1 else 0) +
        (if attached = color then 1 else 0) + (if compensator = color then 1 else 0))) = _
  have hpoint (first second attached : Color) :
      (∑ compensator, triple first second attached * last compensator *
        ((if first = color then 1 else 0) + (if second = color then 1 else 0) +
          (if attached = color then 1 else 0) + (if compensator = color then 1 else 0))) =
      triple first second attached *
        ((if first = color then 1 else 0) + (if second = color then 1 else 0) +
          (if attached = color then 1 else 0)) * (∑ compensator, last compensator) +
        triple first second attached * last color := by
    calc
      _ = ∑ compensator,
          (triple first second attached *
            ((if first = color then 1 else 0) + (if second = color then 1 else 0) +
              (if attached = color then 1 else 0)) * last compensator +
            triple first second attached * (if compensator = color then last compensator else 0)) := by
        apply Finset.sum_congr rfl
        intro compensator _
        split_ifs <;> ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, tripleOutputCount]

theorem triple_output_count_marginals (triple : Color → Color → Color → ℝ) (color : Color) :
    tripleOutputCount triple color =
      (∑ second, ∑ attached, triple color second attached) +
      (∑ first, ∑ attached, triple first color attached) +
      (∑ first, ∑ second, triple first second color) := by
  simp only [tripleOutputCount, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fourOutputCount_sum {Index : Type*} [Fintype Index]
    (mass : Index → (Fin 4 → Color) → ℝ) (color : Color) :
    fourOutputCount (fun word => ∑ index, mass index word) color =
      ∑ index, fourOutputCount (mass index) color := by
  simp only [fourOutputCount, Finset.sum_mul]
  exact Finset.sum_comm

theorem fourOutputCount_smul (mass : (Fin 4 → Color) → ℝ) (scalar : ℝ) (color : Color) :
    fourOutputCount (fun word => scalar * mass word) color = scalar * fourOutputCount mass color := by
  simp only [fourOutputCount, mul_assoc, ← Finset.mul_sum]

end
end AFT.PhysicalBlockTensors

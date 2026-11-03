import AFT.FourOutputCounts
import AFT.SignedFirstCoefficient

/-! # Instance-independent finite four-output mass and count formulas -/
namespace AFT.PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

/-- Fubini's four-output mass formula for every choice of finite-coordinate
decidable equality. Only an enumeration transport is involved. -/
theorem four_output_product_mass_instance [decision : DecidableEq (Fin 4)]
    (triple : Color → Color → Color → ℝ) (last : Color → ℝ) :
    (∑ word : Fin 4 → Color, triple (word 0) (word 1) (word 2) * last (word 3)) =
      (∑ first, ∑ second, ∑ attached, triple first second attached) * ∑ compensator, last compensator := by
  have hd : decision = instDecidableEqFin 4 := Subsingleton.elim _ _
  cases hd
  exact four_output_product_mass triple last

/-- Both physical count definitions are the same finite sum, regardless of
the enumeration instance fixed when each generic definition was elaborated. -/
theorem fourOutputCount_eq_signedColorCount (mass : (Fin 4 → Color) → ℝ) (color : Color) :
    fourOutputCount mass color = LocalTensors.signedColorCount mass color := by
  unfold fourOutputCount LocalTensors.signedColorCount
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

end
end AFT.PhysicalBlockTensors

import AFT.RootSlice
import AFT.ConditionalRepair

/-! # Exact centering inside every retained boundary-label skeleton cell -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def boundaryRecord (interior : Finset Color) (color : Color) : Option Color :=
  if color ∈ interior then none else some color

/-- A boundary-ideal profile remains centered after retaining either the
interior symbol or an individual boundary label, including rare cells. -/
theorem boundary_condition_centered (law : FiniteDist Color) (interior : Finset Color)
    (record : Option Color) (hpos : 0 < law.eventMass (fun color => boundaryRecord interior color = record))
    (value : Color → ℝ) (hmean : law.expectation value = 0)
    (houtside : ∀ color, color ∉ interior → value color = 0) :
    (law.condition (fun color => boundaryRecord interior color = record) hpos).expectation value = 0 := by

  simp only [expectation, condition, div_mul_eq_mul_div, ← Finset.sum_div]
  have hz : (∑ color, (if boundaryRecord interior color = record then law.weight color else 0) * value color) = 0 := by
    cases record with
    | none =>
      calc
        _ = law.expectation value := by
          apply Finset.sum_congr rfl
          intro color _
          by_cases hc : color ∈ interior
          · simp [boundaryRecord, hc]
          · simp [boundaryRecord, hc, houtside color hc]
        _ = 0 := hmean
    | some boundary =>
      apply Finset.sum_eq_zero
      intro color _
      by_cases hc : color ∈ interior
      · simp [boundaryRecord, hc]
      · simp [houtside color hc]
  apply div_eq_zero_iff.mpr
  left
  apply Eq.trans ?_ hz
  apply Finset.sum_congr rfl
  intro color _
  split_ifs <;> rfl

end
end AFT.FiniteDist

namespace AFT.Hoeffding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Every controlled input coordinate has an actual zero boundary value.
This is stronger than unconditional canonicality. -/
def BoundaryVanishing (interior : Slot → Finset Color) (kernel : (Slot → Color) → ℝ) : Prop :=
  ∀ slot word, word slot ∉ interior slot → kernel word = 0

/-- Full joint canonicality survives every legal boundary skeleton cell.
No factor depending on the probability of that cell occurs in the identity. -/
theorem canonical_boundary_condition (reference : Slot → FiniteDist Color)
    (interior : Slot → Finset Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Canonical reference Finset.univ kernel) (hboundary : BoundaryVanishing interior kernel)
    (record : Slot → Option Color)
    (hpos : ∀ slot, 0 < (reference slot).eventMass
      (fun color => FiniteDist.boundaryRecord (interior slot) color = record slot)) :
    Canonical (fun slot => (reference slot).condition
      (fun color => FiniteDist.boundaryRecord (interior slot) color = record slot) (hpos slot)) Finset.univ kernel := by
  refine ⟨hcanonical.1, ?_⟩
  intro slot hslot word
  exact FiniteDist.boundary_condition_centered (reference slot) (interior slot) (record slot) (hpos slot)
    (fun color => kernel (Function.update word slot color)) (hcanonical.2 slot hslot word)
    (fun color hc => hboundary slot (Function.update word slot color) (by simpa only [Function.update_self] using hc))

end
end AFT.Hoeffding

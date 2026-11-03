import AFT.V7CubicSmallness

/-! # Physical block complements preserve the complete Fock conditions -/

namespace AFT.BlockProducts

open scoped BigOperators Classical

noncomputable section

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

omit [Fintype Color] in
/-- Marked slots and their literal block complement partition the full
physical output positions exactly. -/
def splitSlotsEquiv (selected : Finset Index) :
    (Sigma (fun index : {i : Index // i ∈ selected} => Slots index) ⊕
      Sigma (fun index : {i : Index // i ∉ selected} => Slots index)) ≃ Sigma Slots where
  toFun point := match point with
    | .inl point => ⟨point.1, point.2⟩
    | .inr point => ⟨point.1, point.2⟩
  invFun point := if h : point.1 ∈ selected then .inl ⟨⟨point.1, h⟩, point.2⟩
    else .inr ⟨⟨point.1, h⟩, point.2⟩
  left_inv point := by cases point with
    | inl point => rcases point with ⟨⟨index, hi⟩, slot⟩; simp only [dif_pos hi]
    | inr point => rcases point with ⟨⟨index, hi⟩, slot⟩; simp only [dif_neg hi]
  right_inv point := by
    rcases point with ⟨index, slot⟩
    by_cases hi : index ∈ selected
    · simp only [dif_pos hi]
    · simp only [dif_neg hi]

omit [Fintype Color] in
theorem splitSlots_card (selected : Finset Index) :
    Fintype.card (Sigma (fun index : {i : Index // i ∈ selected} => Slots index) ⊕
      Sigma (fun index : {i : Index // i ∉ selected} => Slots index)) = Fintype.card (Sigma Slots) :=
  Fintype.card_congr (splitSlotsEquiv Slots selected)

omit [Fintype Color] in
theorem sum_subtype_le (predicate : Index → Prop) [DecidablePred predicate] (value : Index → ℝ) (hn : ∀ index, 0 ≤ value index) :
    (∑ index : {i : Index // predicate i}, value index) ≤ ∑ index, value index := by
  have hh := Fintype.sum_subtype_add_sum_subtype predicate value
  have hc : 0 ≤ ∑ index : {i : Index // ¬predicate i}, value index :=
    Finset.sum_nonneg fun index _ => hn index
  linarith

/-- Taking the actual complement of any marked blocks retains all three
local Fock conditions at the original population normalization. -/
theorem CubicBlockConditions_restrict (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (population capacity : ℕ) (radius : ℝ)
    (hcapacity : Fintype.card Index ≤ capacity)
    (hlocal : CubicBlockConditions Slots reference law population capacity radius) (selected : Finset Index) :
    CubicBlockConditions (fun index : {i : Index // i ∉ selected} => Slots index) reference
      (fun index => law index) population capacity radius := by
  refine ⟨(Finset.card_le_univ _).trans ((Fintype.card_subtype_le _).trans hcapacity), ?_, ?_⟩
  · exact (sum_subtype_le (fun index => index ∉ selected)
      (fun index => ∑ color, (Real.sqrt 2 * normalizedLinear Slots reference law
        (radius / Real.sqrt population) index color) ^ 2)
      (fun index => Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hlocal.2.1
  · exact (sum_subtype_le (fun index => index ∉ selected)
      (fun index => 128 * SelectionBound.localPairNorm
        (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
          (radius / Real.sqrt population) index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
            (radius / Real.sqrt population) index word) index)
      (fun index => by unfold SelectionBound.localPairNorm SelectionBound.localTripleNorm; positivity)).trans hlocal.2.2

end

end AFT.BlockProducts

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology

noncomputable section

local instance restrictedBlocksFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance restrictedBlocksSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- Every actual independent complement of a marked output tensor satisfies
the full Fock conditions, with the unchanged whole-population denominator. -/
theorem actual_restricted_cubic_conditions_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : blockIndex parameter → ℤ,
      (∀ index, |root index| ≤ (v7RootCutoff parameter : ℤ)) →
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) → ∀ selected : Finset (blockIndex parameter),
      CubicBlockConditions (fun index : {i : blockIndex parameter // i ∉ selected} => blockSlots parameter index)
        (actualReferenceLaw cutoffScale parameter (beta parameter))
        (fun index => actualBlockFamily cutoffScale parameter (beta parameter) root queue index)
        (Parameters.dimension parameter) (Parameters.bodies parameter) ((parameter : ℝ) ^ 2) := by
  filter_upwards [actual_cubic_conditions_eventually cutoffScale hscale beta hbeta]
    with parameter h root queue hr hq selected
  exact CubicBlockConditions_restrict (blockSlots parameter) _ _ _ _ _
    (blockIndex_card parameter).le (h root queue hr hq) selected

end

end AFT.V7Calibration

import AFT.ReferenceHigherTable

/-! # The exact sum of all nonlinear physical coefficient forms -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem referenceHigherForm_sum (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ)
    (hmass : (∑ word,mass word)=0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => 2≤selected.card),
      referenceCoefficientForm primary reference mass selected) =
      centeredGeneratingLinear reference.weight mass-profileForm (physicalFirstProfile mass) := by
  rw [centeredGeneratingLinear_reference_expansion primary reference hp mass]
  have hsplit : (∑ selected : Finset Slot,referenceCoefficientForm primary reference mass selected) =
      referenceCoefficientForm primary reference mass ∅+
      (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card=1),
        referenceCoefficientForm primary reference mass selected)+
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).filter (fun selected => 2≤selected.card),
        referenceCoefficientForm primary reference mass selected := by
    calc
      _ = ∑ selected : Finset Slot,
          ((if selected=∅ then referenceCoefficientForm primary reference mass selected else 0)+
          (if selected.card=1 then referenceCoefficientForm primary reference mass selected else 0)+
          (if 2≤selected.card then referenceCoefficientForm primary reference mass selected else 0)) := by
        apply Finset.sum_congr rfl
        intro selected _
        by_cases he : selected=∅
        · simp [he]
        · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
          by_cases ho : selected.card=1
          · simp [he,ho]
          · simp [he,ho,show 2≤selected.card by omega]
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_filter,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hsplit,referenceCoefficientForm_empty,hmass,map_zero,zero_add,
    referenceCoefficientForm_linear_sum primary reference hp mass hmass]
  ring

end
end AFT.RepresentedPolynomial

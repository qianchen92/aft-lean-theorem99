import CurrentAFT.CycleRootExpansion

/-! # The actual Hoeffding component is the quantitative selected-root coefficient -/
namespace CurrentAFT.SelectedRootComponent
open AFT CycleSelections CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize
local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem selectedCoefficient_eq (security count : ℕ)
    (labels : CycleSelections.Selection (Parameters.bodySize security) count)
    (word : Vertex security → Root security) :
    selectedCoefficient security count labels (word ∘ labels) =
      Hoeffding.densityComponent (fun _ => rootReference security) (rootLaw security).weight
        (Finset.univ.map labels) word := by
  unfold selectedCoefficient centeredRootDensity
  rw [FiniteDist.expectation_map]
  simp only [FiniteDist.expectation, Hoeffding.densityComponent, Finset.prod_map,
    Function.comp_apply, SupportedHoeffding.centeredRootAtom_eq]
  congr 3
  exact Subsingleton.elim _ _

/-- The identity holds for arbitrary joint vector-valued tests; no
factorization or nonzero-atom hypothesis is needed. -/
theorem actualComponent_eq {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (security count : ℕ) (labels : CycleSelections.Selection (Parameters.bodySize security) count)
    (test : (Vertex security → Root security) → Value) :
    actualComponent security (Finset.univ.map labels) test =
      ∑ word, ((FiniteDist.independent (fun _ : Vertex security => rootReference security)).weight word *
        selectedCoefficient security count labels (word ∘ labels)) • test word := by
  simp only [actualComponent, componentResponse, LinearMap.coe_mk, AddHom.coe_mk,
    selectedCoefficient_eq]

/-- Every tagged root coordinate is centered under its true marginal,
including when that marginal has zero atoms. -/
theorem selectedCoefficient_centered (security count : ℕ)
    (labels : CycleSelections.Selection (Parameters.bodySize security) count) (index : Fin count) :
    Hoeffding.CenteredAt (fun _ => rootReference security) index
      (selectedCoefficient security count labels) := by
  let joint := (rootLaw security).map (fun roots slot => roots (labels slot))
  have hmarginal (slot : Fin count) :
      joint.map (fun roots => roots slot) = rootReference security := by
    dsimp only [joint]
    rw [FiniteDist.map_map]
    exact rootLaw_coordinate security (labels slot)
  have hcanonical := SupportedHoeffding.densityComponent_canonical_of_support
    (fun _ : Fin count => rootReference security) joint.weight
    (marginal_support joint (fun _ => rootReference security) hmarginal) Finset.univ
  have hequal : selectedCoefficient security count labels =
      Hoeffding.densityComponent (fun _ : Fin count => rootReference security) joint.weight Finset.univ := by
    funext word
    simp only [selectedCoefficient, centeredRootDensity, FiniteDist.expectation,
      Hoeffding.densityComponent, SupportedHoeffding.centeredRootAtom_eq, joint]
    congr 3
    exact Subsingleton.elim _ _
  rw [hequal]
  exact hcanonical.2 index (Finset.mem_univ index)

end
end CurrentAFT.SelectedRootComponent

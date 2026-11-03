import AFT.IndependentInverseColumns
import AFT.PendingPrimaryGeometry

/-! # Literal pending replacement in the original finite coordinate numbering -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {New Primary Body Color : Type*} [Fintype New] [Fintype Primary] [Fintype Body]
  [Fintype Color] [DecidableEq New] [DecidableEq Primary] [DecidableEq Body]

omit [Fintype Color] [DecidableEq New] [DecidableEq Primary] [DecidableEq Body] in
theorem groupedFiniteSeed_kernel_coordinates (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ)
    (word : Fin (Fintype.card (New ⊕ Primary)+Fintype.card Body) → Color) :
    (groupedFiniteSeed kernel).kernel word=
      kernel (Sum.elim
        (fun new : New => word (Fin.castAdd _ (Fintype.equivFin (New ⊕ Primary) (Sum.inl new))))
        (Sum.elim
          (fun old : Primary => word (Fin.castAdd _ (Fintype.equivFin (New ⊕ Primary) (Sum.inr old))))
          (fun old : Body => word (Fin.natAdd _ (Fintype.equivFin Body old))))) := by
  change kernel ((word ∘ mixedFiniteEquiv) ∘ (Equiv.sumAssoc New Primary Body).symm)=_
  congr 1
  funext slot
  rcases slot with slot|(slot|slot) <;> simp [mixedFiniteEquiv,Function.comp_apply]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance pendingHigherColumnsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingHigherColumnsSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _

/-- A column formula for the exact literal seed used by the analytic U.
The displayed finite permutations are the ones stored by the fixed-order
numbering program, and no separability of the old kernel is assumed. -/
theorem pendingPrimaryHigherSeed_columns (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (point : Fin seed.primaryOrder)
    (selected : Finset (Fin 4)) (word : ℕ → Fin (Parameters.modulus n)) :
    (pendingPrimaryHigherSeed C n beta operator charts seed point selected).kernel (fun slot => word slot.val)=
      ∑ color,seed.kernel (Fin.addCases
        (fun slot => if h : slot=point then color else
          word ((Fintype.equivFin (selected ⊕ {other : Fin seed.primaryOrder // other≠point})) (Sum.inr ⟨slot,h⟩)).val)
        (fun slot => word (Fintype.card (selected ⊕ {other : Fin seed.primaryOrder // other≠point})+
          (Fintype.equivFin (Fin seed.bodyOrder) slot).val)))*
        independentInverseColumn C n beta operator charts selected color
          (fun slot => word ((Fintype.equivFin (selected ⊕ {other : Fin seed.primaryOrder // other≠point})) (Sum.inl slot)).val) := by
  unfold pendingPrimaryHigherSeed independentJointHigherSeed
  rw [groupedFiniteSeed_kernel_coordinates,independentJointInverse_columns]
  apply Finset.sum_congr rfl
  intro color _
  congr 1
  unfold splitPrimaryKernel
  congr 1
  funext slot
  refine Fin.addCases ?_ ?_ slot
  · intro old
    by_cases ho : old=point
    · subst old
      simp [splitPrimaryIndex,primarySplitEquiv]
    · simp [splitPrimaryIndex,primarySplitEquiv,ho]
  · intro old
    simp [splitPrimaryIndex,primarySplitEquiv]

end
end AFT.V7Calibration

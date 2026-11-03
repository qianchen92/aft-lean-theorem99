import AFT.MixedSumFibers

/-! # Literal one-coordinate slices and their exact mixed Hilbert fibers -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Rest Color : Type*} [Fintype Rest] [Fintype Color] [DecidableEq Rest]

def singletonJoin (kernel : Color → (Rest → Color) → ℝ) : (Unit ⊕ Rest → Color) → ℝ :=
  fun word => kernel (word (Sum.inl ())) (word ∘ Sum.inr)

def singletonSlice (kernel : Color → (Rest → Color) → ℝ) (fixed : Finset Rest)
    (values : Rest → Color) : Color → (Rest → Color) → ℝ :=
  fun color rest => kernel color (freeze fixed values rest)

theorem independent_unit_expectation (primary : FiniteDist Color) (value : (Unit → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Unit => primary)).expectation value =
      primary.expectation (fun color => value (fun _ => color)) := by
  unfold FiniteDist.expectation
  rw [← (Equiv.funUnique Unit Color).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro color _
  simp only [FiniteDist.independent,Fintype.prod_unique]
  rfl

theorem singletonSlice_integrated_eq (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : Color → (Rest → Color) → ℝ) (fixed : Finset Rest)
    (values : Rest → Color) (color : Color) :
    (FiniteDist.independent other).expectation (fun rest => primary.l2Sq (fun input =>
      singletonSlice kernel fixed values input rest)) =
    fiberSq (Sum.elim (fun _ : Unit => primary) other) (singletonJoin kernel)
      ((∅ : Finset Unit).disjSum fixed) (Sum.elim (fun _ => color) values) := by
  rw [show singletonJoin kernel = (fun word => (fun left right => kernel (left ()) right)
    (word ∘ Sum.inl) (word ∘ Sum.inr)) by rfl]
  rw [fiberSq_sum_apply (fun _ : Unit => primary) other
    (fun left right => kernel (left ()) right) ∅ fixed (Sum.elim (fun _ => color) values)]
  simp only [fiberSq,FiniteDist.l2Sq]
  apply Finset.sum_congr rfl
  intro rest _
  congr 1
  dsimp only
  rw [independent_unit_expectation]
  rfl

theorem singletonSlice_fixed_eq (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : Color → (Rest → Color) → ℝ) (fixed : Finset Rest)
    (values : Rest → Color) (color : Color) :
    (FiniteDist.independent other).l2Sq (singletonSlice kernel fixed values color) =
    fiberSq (Sum.elim (fun _ : Unit => primary) other) (singletonJoin kernel)
      ((Finset.univ : Finset Unit).disjSum fixed) (Sum.elim (fun _ => color) values) := by
  rw [show singletonJoin kernel = (fun word => (fun left right => kernel (left ()) right)
    (word ∘ Sum.inl) (word ∘ Sum.inr)) by rfl]
  rw [fiberSq_sum_apply (fun _ : Unit => primary) other
    (fun left right => kernel (left ()) right) Finset.univ fixed (Sum.elim (fun _ => color) values)]
  unfold fiberSq FiniteDist.l2Sq
  apply Finset.sum_congr rfl
  intro rest _
  congr 1
  simp only [freeze,Finset.mem_univ,if_true,Sum.elim_inl,Function.comp_apply]
  rw [FiniteDist.expectation_const]
  rfl

/-- The actual mixed sup supplies both old Hilbert budgets without a
factor from the number of remaining inputs. -/
theorem singletonSlice_budgets (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : Color → (Rest → Color) → ℝ) (fixed : Finset Rest) (values : Rest → Color)
    [Nonempty Color] :
    ((FiniteDist.independent other).expectation (fun rest => primary.l2Sq (fun color =>
      singletonSlice kernel fixed values color rest)) ≤
      fiberNorm (Sum.elim (fun _ : Unit => primary) other) (singletonJoin kernel)
        ((∅ : Finset Unit).disjSum fixed)^2) ∧
    (∀ color,(FiniteDist.independent other).l2Sq (singletonSlice kernel fixed values color) ≤
      fiberNorm (Sum.elim (fun _ : Unit => primary) other) (singletonJoin kernel)
        ((Finset.univ : Finset Unit).disjSum fixed)^2) := by
  constructor
  · rw [singletonSlice_integrated_eq primary other kernel fixed values (Classical.choice inferInstance)]
    exact fiberSq_le_norm_sq _ _ _ _
  · intro color
    rw [singletonSlice_fixed_eq]
    exact fiberSq_le_norm_sq _ _ _ _

end
end AFT.MixedKernel

import AFT.CanonicalPolynomialChannel

/-! # Canonical joint kernels eliminate constant terms in every output channel -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color Output : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem jointChannelPolynomial_add_at (reference : Slot → FiniteDist Color)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ)
    (slot : Slot) (extra : Color → Table Output) :
    jointChannelPolynomial reference (Function.update forms slot (fun color => forms slot color+extra color)) kernel=
      jointChannelPolynomial reference forms kernel+
        jointChannelPolynomial reference (Function.update forms slot extra) kernel := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold jointChannelPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro word _
  have hu (value : Color → Table Output) :
      (fun other => Function.update forms slot value other (word other))=
        Function.update (fun other => forms other (word other)) slot (value (word slot)) := by
    funext other
    by_cases ho : other=slot
    · subst other; simp
    · simp [Function.update_of_ne ho]
  rw [hu,hu,Finset.prod_update_of_mem (Finset.mem_univ slot),
    Finset.prod_update_of_mem (Finset.mem_univ slot),
    ← Finset.mul_prod_erase Finset.univ (fun other => forms other (word other)) (Finset.mem_univ slot)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem jointChannelPolynomial_constant_at (reference : Slot → FiniteDist Color)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ)
    (slot : Slot) (constant : Table Output) (hc : Hoeffding.CenteredAt reference slot kernel) :
    jointChannelPolynomial reference (Function.update forms slot (fun color => forms slot color+constant)) kernel=
      jointChannelPolynomial reference forms kernel := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hz := jointChannelPolynomial_zero reference (Function.update forms slot (fun _ => constant)) kernel slot constant hc
    (by intro color _; simp)
  rw [jointChannelPolynomial_add_at,hz,add_zero]

theorem jointChannelPolynomial_add_constants (reference : Slot → FiniteDist Color)
    (forms : Slot → Color → Table Output) (constants : Slot → Table Output) (kernel : (Slot → Color) → ℝ)
    (hc : ∀ slot,Hoeffding.CenteredAt reference slot kernel) :
    jointChannelPolynomial reference (fun slot color => forms slot color+constants slot) kernel=
      jointChannelPolynomial reference forms kernel := by
  have hi (selected : Finset Slot) :
      jointChannelPolynomial reference
        (fun slot color => forms slot color+if slot∈selected then constants slot else 0) kernel=
      jointChannelPolynomial reference forms kernel := by
    induction selected using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty,if_false,add_zero]
    | @insert slot selected hs ih =>
      let previous := fun other color => forms other color+if other∈selected then constants other else 0
      have he : (fun other color => forms other color+if other∈insert slot selected then constants other else 0)=
          Function.update previous slot (fun color => previous slot color+constants slot) := by
        funext other color
        by_cases ho : other=slot
        · subst other; simp [previous,hs]
        · simp [previous,ho]
      rw [he,jointChannelPolynomial_constant_at reference previous kernel slot (constants slot) (hc slot)]
      exact ih
  simpa only [Finset.mem_univ,if_true] using hi Finset.univ

end
end AFT.RepresentedPolynomial

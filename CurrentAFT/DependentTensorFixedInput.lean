import CurrentAFT.DependentTensorComposition

/-! # Coordinatewise fixed points of dependent tensor channels

The hypotheses fix each complete one-coordinate slice of a joint input. They
do not require the joint input to factor across its dependent alphabets.
-/

namespace CurrentAFT.DependentTensorFixedInput
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Successive dependent contraction fixes a joint kernel whenever every local
map fixes every slice in its own coordinate. Idempotence of the local maps is
unnecessary. -/
theorem applyFin_eq_self (count : ℕ) {Input : Fin count → Type*}
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Fin count) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    DependentTensorChannel.applyFin count projector kernel = kernel := by
  induction count with
  | zero =>
      funext word
      change kernel (fun index => Fin.elim0 index) = kernel word
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      have htail (first : Input 0) :
          ∀ index word, projector index.succ
            (fun value => kernel (Fin.cons first (Function.update word index value))) =
              fun value => kernel (Fin.cons first (Function.update word index value)) := by
        intro index word
        simpa only [Fin.cons_update] using hfixed index.succ (Fin.cons first word)
      have ht (first : Input 0) :
          DependentTensorChannel.applyFin count (fun index => projector index.succ)
            (fun rest => kernel (Fin.cons first rest)) =
              fun rest => kernel (Fin.cons first rest) :=
        ih (fun index => projector index.succ) (fun rest => kernel (Fin.cons first rest))
          (htail first)
      funext output
      change projector 0 (fun first =>
        DependentTensorChannel.applyFin count (fun index => projector index.succ)
          (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ))
            (output 0) = kernel output
      simp_rw [ht]
      have hcons : Fin.cons (output 0) (fun index => output index.succ) = output := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      have hh := congrFun (hfixed 0
        (Fin.cons (output 0) (fun index => output index.succ))) (output 0)
      simp only [Fin.update_cons_zero] at hh
      rw [hcons] at hh
      exact hh

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input : Index → Type*} [∀ index, Fintype (Input index)]

omit [Fintype Index] [∀ index, Fintype (Input index)] in
private theorem reindex_update {Index' : Type*} [DecidableEq Index']
    (equiv : Index' ≃ Index) (word : ∀ index, Input (equiv index))
    (index : Index') (value : Input (equiv index)) :
    Equiv.piCongrLeft Input equiv (Function.update word index value) =
      Function.update (Equiv.piCongrLeft Input equiv word) (equiv index) value := by
  simpa only [Equiv.piCongrLeft, Equiv.symm_symm] using
    Function.piCongrLeft'_symm_update Input equiv.symm word index value

/-- The literal full joint dependent tensor fixes every input whose slices are
fixed by the corresponding local maps. No nonemptiness, separability, or
idempotence assumption is needed. -/
theorem apply_eq_self
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Index) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    DependentTensorChannel.apply projector kernel = kernel := by
  let equiv : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hfixed' (index : Fin (Fintype.card Index)) (word : ∀ index, Input (equiv index)) :
      projector (equiv index)
        (fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value))) =
          fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value)) := by
    simpa only [reindex_update] using
      hfixed (equiv index) (Equiv.piCongrLeft Input equiv word)
  have hh := applyFin_eq_self (Fintype.card Index) (fun index => projector (equiv index))
    (fun word => kernel (Equiv.piCongrLeft Input equiv word)) hfixed'
  funext output
  have heq := congrFun hh ((Equiv.piCongrLeft Input equiv).symm output)
  rw [DependentTensorChannel.applyFin_formula] at heq
  have hreindex :
      (∑ point : (index : Fin (Fintype.card Index)) → Input (equiv index),
        kernel (Equiv.piCongrLeft Input equiv point) *
          ∏ index, projector (equiv index) (Pi.single (point index) 1)
            (((Equiv.piCongrLeft Input equiv).symm output) index)) =
        DependentTensorChannel.apply projector kernel output := by
    unfold DependentTensorChannel.apply
    rw [← (Equiv.piCongrLeft Input equiv).sum_comp]
    apply Finset.sum_congr rfl
    intro point _
    congr 1
    rw [← equiv.prod_comp]
    simp only [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_symm_apply]
  rw [hreindex] at heq
  simpa only [Equiv.apply_symm_apply] using heq

/-- Precomposing physical local channels with slice-preserving projectors does
not change their full joint response. -/
theorem apply_comp_eq {Output : Index → Type*} [∀ index, Fintype (Output index)]
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (channel : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Output index → ℝ))
    (kernel : ((index : Index) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    DependentTensorChannel.apply (fun index => (channel index).comp (projector index)) kernel =
      DependentTensorChannel.apply channel kernel := by
  rw [DependentTensorComposition.apply_comp, apply_eq_self projector kernel hfixed]

end
end CurrentAFT.DependentTensorFixedInput

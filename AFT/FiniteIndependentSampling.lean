import AFT.FiniteConditionalSampling
import AFT.DependentTensorChannel

/-! # Product samplers with coordinate-dependent output alphabets -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 theorem sampling_dependentIndependent_map_coordinates {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Input Output : Index → Type*} [∀ i,Fintype (Input i)] [∀ i,Fintype (Output i)]
    (law : ∀ i,FiniteDist (Input i)) (function : ∀ i,Input i → Output i) :
    (dependentIndependent law).map (fun word i => function i (word i))=
      dependentIndependent (fun i => (law i).map (function i)) := by
  ext target
  simp only [map_weight,dependentIndependent_weight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_ite_zero]
  have he : (∀ i∈(Finset.univ : Finset Index),function i (word i)=target i)↔(fun i => function i (word i))=target := by
    simp only [Finset.mem_univ,forall_true_left,funext_iff]
  simp only [he]

 theorem uniform_function {Index State : Type*} [Fintype Index] [DecidableEq Index] [Fintype State] [Nonempty State] :
    uniform (Index → State)=independent (fun _ : Index => uniform State) := by
  ext word
  simp only [uniform_weight,independent,Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

 theorem uniform_map_dependent_coordinates {Index Tape : Type*} [Fintype Index] [DecidableEq Index] [Fintype Tape] [Nonempty Tape]
    {Output : Index → Type*} [∀ i,Fintype (Output i)] (function : ∀ i,Tape → Output i) :
    (uniform (Index → Tape)).map (fun word i => function i (word i))=
      dependentIndependent (fun i => (uniform Tape).map (function i)) := by
  rw [uniform_function]
  exact sampling_dependentIndependent_map_coordinates (fun _ => uniform Tape) function

 theorem l1_dependentIndependent_fin_le (count : ℕ) (State : Fin count → Type*)
    [∀ i,Fintype (State i)] (first second : ∀ i,FiniteDist (State i)) :
    (∑ word,|(dependentIndependent first).weight word-(dependentIndependent second).weight word|)≤
      ∑ i,∑ point,|(first i).weight point-(second i).weight point| := by
  induction count with
  | zero => simp only [dependentIndependent_weight,Fin.prod_univ_zero,sub_self,abs_zero,Finset.sum_const_zero,Fin.sum_univ_zero,le_refl]
  | succ count ih =>
    have hsplit (law : ∀ i : Fin (count+1),FiniteDist (State i)) :
        dependentIndependent law=
          ((law 0).prod (dependentIndependent (fun i : Fin count => law i.succ))).map (Fin.consEquiv State) := by
      ext word
      rw [map_equiv_weight]
      change (∏ i,(law i).weight (word i))=(law 0).weight (word 0)*∏ i : Fin count,(law i.succ).weight (word i.succ)
      exact Fin.prod_univ_succ _
    rw [hsplit first,hsplit second,Fin.sum_univ_succ]
    apply (l1_map_le _ _ _).trans
    apply (l1_prod_le _ _ _ _).trans
    exact add_le_add le_rfl (ih (fun i => State i.succ) (fun i => first i.succ) (fun i => second i.succ))

 theorem l1_independent_le {Index State : Type*} [Fintype Index] [DecidableEq Index] [Fintype State]
    (first second : Index → FiniteDist State) :
    (∑ word,|(independent first).weight word-(independent second).weight word|)≤
      ∑ i,∑ point,|(first i).weight point-(second i).weight point| := by
  let e := Fintype.equivFin Index
  let ew : (Fin (Fintype.card Index) → State) ≃ (Index → State) :=
    Equiv.arrowCongr e.symm (Equiv.refl State)
  have he (law : Index → FiniteDist State) : independent law=
      (independent (fun i => law (e.symm i))).map ew := by
    ext word
    rw [map_equiv_weight]
    change (∏ i,(law i).weight (word i))=∏ i,(law (e.symm i)).weight (word (e.symm i))
    exact (e.symm.prod_comp (fun i => (law i).weight (word i))).symm
  rw [he first,he second]
  apply (l1_map_le _ _ _).trans
  apply (l1_independent_fin_le _ _ _).trans
  exact le_of_eq (e.symm.sum_comp (fun i => ∑ point,|(first i).weight point-(second i).weight point|))

end
end AFT.FiniteDist

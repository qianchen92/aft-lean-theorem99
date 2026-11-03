import AFT.FiniteConcentration
import AFT.MixtureConditioning
import AFT.JointPairOutput

/-! # Total variation of actual independent finite products -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B]

theorem l1_map_le (first second : FiniteDist A) (map : A → B) :
    (∑ b,|(first.map map).weight b-(second.map map).weight b|) ≤ ∑ a,|first.weight a-second.weight a| := by
  simp only [map_weight,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b,∑ a,|(if map a=b then first.weight a else 0)-(if map a=b then second.weight a else 0)| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (map a)]
      · simp
      · intro b _ hba
        simp [Ne.symm hba]
      · simp

theorem l1_prod_le (first first' : FiniteDist A) (second second' : FiniteDist B) :
    (∑ pair,|(first.prod second).weight pair-(first'.prod second').weight pair|) ≤
      (∑ a,|first.weight a-first'.weight a|)+(∑ b,|second.weight b-second'.weight b|) := by
  simp only [prod_weight,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a,∑ b,(|first.weight a-first'.weight a| *second.weight b+
        first'.weight a*|second.weight b-second'.weight b|) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have he : first.weight a*second.weight b-first'.weight a*second'.weight b=
          (first.weight a-first'.weight a)*second.weight b+first'.weight a*(second.weight b-second'.weight b) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg (second.nonneg _),abs_of_nonneg (first'.nonneg _)] using abs_add_le
        ((first.weight a-first'.weight a)*second.weight b) (first'.weight a*(second.weight b-second'.weight b))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,second.sum_one,mul_one,← Finset.sum_mul,first'.sum_one,one_mul]

omit [Fintype B] in
/-- The comparison is for the literal finite product law; all coordinate
errors are summed once. -/
theorem l1_independent_fin_le (count : ℕ) (first second : Fin count → FiniteDist A) :
    (∑ word,|(independent first).weight word-(independent second).weight word|) ≤
      ∑ i,∑ a,|(first i).weight a-(second i).weight a| := by
  induction count with
  | zero => simp only [independent,Fin.prod_univ_zero,sub_self,abs_zero,Finset.sum_const_zero,Fin.sum_univ_zero,le_refl]
  | succ count ih =>
    let tailFirst := independent (fun i : Fin count => first i.succ)
    let tailSecond := independent (fun i : Fin count => second i.succ)
    have hsplit (law : Fin (count+1) → FiniteDist A) : independent law=
        ((law 0).prod (independent (fun i : Fin count => law i.succ))).map (Fin.consEquiv (fun _ : Fin (count+1) => A)) := by
      ext word
      rw [map_equiv_weight]
      change (∏ i,(law i).weight (word i))=(law 0).weight (word 0)*∏ i : Fin count,(law i.succ).weight (word i.succ)
      exact Fin.prod_univ_succ _
    rw [hsplit first,hsplit second,Fin.sum_univ_succ]
    apply (l1_map_le _ _ _).trans
    exact (l1_prod_le (first 0) (second 0) tailFirst tailSecond).trans (add_le_add le_rfl (ih _ _))

/-- A common independent population contributes no additional error. -/
theorem l1_sumtype_common_le (left : FiniteDist A) (first second : FiniteDist A) (n m : ℕ) :
    (∑ word,|(independent (Sum.elim (fun _ : Fin n => left) (fun _ : Fin m => first))).weight word-
      (independent (Sum.elim (fun _ : Fin n => left) (fun _ : Fin m => second))).weight word|) ≤
        m*(∑ a,|first.weight a-second.weight a|) := by
  let e := (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) A).symm
  have he (right : FiniteDist A) : independent (Sum.elim (fun _ : Fin n => left) (fun _ : Fin m => right))=
      ((independent (fun _ : Fin n => left)).prod (independent (fun _ : Fin m => right))).map e := by
    ext word
    rw [map_equiv_weight]
    simp only [independent,prod_weight,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
    rfl
  rw [he first,he second]
  apply (l1_map_le _ _ _).trans
  have hp := l1_prod_le (independent (fun _ : Fin n => left)) (independent (fun _ : Fin n => left))
    (independent (fun _ : Fin m => first)) (independent (fun _ : Fin m => second))
  simp only [sub_self,abs_zero,Finset.sum_const_zero,zero_add] at hp
  apply hp.trans
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    l1_independent_fin_le m (fun _ => first) (fun _ => second)

end
end AFT.FiniteDist

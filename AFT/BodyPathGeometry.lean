import AFT.Tree

/-! # The actual path incidence has the quantitative bounds of V7 Lemma 7.1

The bounds are established on the real incidence map, using adjacent
coordinates for the upper bound and exact prefix recovery for the lower.
-/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The incidence of the consistently oriented path, including both endpoints. -/
def realPath {edges : ℕ} (input : Fin edges → ℝ) : Fin (edges+1) → ℝ :=
  Fin.snoc input 0-Fin.cons 0 input

/-- The real incidence uses the same endpoint convention as the integral
path basis used by the actual affine construction. -/
theorem realPath_cons {edges : ℕ} (first : ℝ) (tail : Fin edges → ℝ) :
    realPath (Fin.cons first tail) = Fin.cons first
      (fun vertex => realPath tail vertex - if vertex=0 then first else 0) := by
  funext vertex
  unfold realPath
  rw [← Fin.cons_snoc_eq_snoc_cons]
  refine Fin.cases ?_ (fun vertex => ?_) vertex
  · simp
  · simp only [Pi.sub_apply,Fin.cons_succ]
    refine Fin.cases ?_ (fun vertex => ?_) vertex
    · simp
    · simp

theorem realPath_intCast {edges : ℕ} (input : Fin edges → ℤ) :
    realPath (fun edge => (input edge : ℝ)) = fun vertex => (pathLoad edges input vertex : ℝ) := by
  induction edges with
  | zero =>
    funext vertex
    have hv : vertex=Fin.last 0 := Fin.ext (by omega)
    subst vertex
    simp only [realPath,pathLoad,Pi.sub_apply,Pi.zero_apply,Int.cast_zero,Fin.snoc_last]
    simp

  | succ edges ih =>
    have hi : (fun edge => (input edge : ℝ))=Fin.cons (input 0 : ℝ)
        (fun edge => (Fin.tail input edge : ℝ)) := by
      funext edge
      refine Fin.cases ?_ (fun _ => ?_) edge <;> rfl
    rw [hi,realPath_cons,ih]
    funext vertex
    refine Fin.cases ?_ (fun vertex => ?_) vertex
    · simp [pathLoad]
    · simp only [pathLoad,Fin.cons_succ,Int.cast_sub]
      congr 1
      split_ifs <;> simp

/-- Exact agreement with the signed integer matrix, not merely with an
isomorphic real path model. -/
theorem realPath_signedIncidence {edges : ℕ} (input : Fin edges → ℤ) :
    realPath (fun edge => (input edge : ℝ)) = fun vertex =>
      ((Matrix.mulVec (GrowingTree.signedIncidence (GrowingTree.path edges)) input) vertex : ℝ) := by
  rw [GrowingTree.signedIncidence_mulVec,GrowingTree.load_path]
  exact realPath_intCast input

theorem realPath_sum {edges : ℕ} (input : Fin edges → ℝ) : ∑ vertex,realPath input vertex=0 := by
  simp only [realPath,Pi.sub_apply,Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
  simp

theorem realPath_square_upper {edges : ℕ} (input : Fin edges → ℝ) :
    (∑ vertex,realPath input vertex^2) ≤ 4*∑ edge,input edge^2 := by
  calc
    _ ≤ ∑ vertex : Fin (edges+1),(2*((Fin.snoc input (0 : ℝ) : Fin (edges+1) → ℝ) vertex)^2+2*((Fin.cons (0 : ℝ) input : Fin (edges+1) → ℝ) vertex)^2) := by
      apply Finset.sum_le_sum
      intro vertex _
      dsimp [realPath]
      nlinarith [sq_nonneg ((Fin.snoc input (0 : ℝ) : Fin (edges+1) → ℝ) vertex+(Fin.cons (0 : ℝ) input : Fin (edges+1) → ℝ) vertex)]
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        Fin.sum_univ_castSucc,Fin.sum_univ_succ]
      simp only [Fin.snoc_castSucc,Fin.snoc_last,Fin.cons_zero,Fin.cons_succ,zero_pow (by decide : 2≠0),add_zero,zero_add]
      ring

/-- Every edge value is recovered as the corresponding vertex prefix sum. -/
theorem realPath_prefix {edges : ℕ} (input : Fin edges → ℝ) (edge : Fin edges) :
    (∑ vertex : Fin (edges+1),if vertex.val≤edge.val then realPath input vertex else 0)=input edge := by
  have he (vertex : Fin (edges+1)) :
      (if vertex.val≤edge.val then realPath input vertex else 0)=
      (if vertex.val≤edge.val then (Fin.snoc input (0 : ℝ) : Fin (edges+1) → ℝ) vertex else 0)-
        (if vertex.val≤edge.val then (Fin.cons (0 : ℝ) input : Fin (edges+1) → ℝ) vertex else 0) := by
    unfold realPath
    split_ifs <;> simp only [Pi.sub_apply,sub_zero]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Fin.sum_univ_castSucc,Fin.sum_univ_succ]
  simp only [Fin.val_castSucc,Fin.snoc_castSucc,Fin.val_last,Fin.snoc_last,ite_self,add_zero,
    Fin.val_zero,Nat.zero_le,Fin.cons_zero,Fin.val_succ,Fin.cons_succ,zero_add]
  rw [← Finset.sum_sub_distrib]
  have hd (other : Fin edges) :
      (if other.val≤edge.val then input other else 0)-(if other.val+1≤edge.val then input other else 0)=
        if other=edge then input edge else 0 := by
    by_cases hh : other=edge
    · subst other; simp
    · have hv : other.val≠edge.val := fun h => hh (Fin.ext h)
      split_ifs <;> simp_all <;> omega
  simp only [hd,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem realPath_edge_square_le {edges : ℕ} (input : Fin edges → ℝ) (edge : Fin edges) :
    input edge^2 ≤ (edges+1 : ℝ)*∑ vertex,realPath input vertex^2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (edges+1)))
    (fun vertex => if vertex.val≤edge.val then realPath input vertex else 0) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,realPath_prefix] at hc
  rw [mul_comm] at hc
  simp only [Nat.cast_add,Nat.cast_one] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro vertex _
  split_ifs <;> simp [sq_nonneg]

/-- This is `(edges+1)⁻² I ≤ DᵀD`, stated without matrix-order notation. -/
theorem realPath_square_lower {edges : ℕ} (input : Fin edges → ℝ) :
    (∑ edge,input edge^2) ≤ (edges+1 : ℝ)^2*∑ vertex,realPath input vertex^2 := by
  calc
    _ ≤ ∑ edge : Fin edges,(edges+1 : ℝ)*∑ vertex,realPath input vertex^2 :=
      Finset.sum_le_sum fun edge _ => realPath_edge_square_le input edge
    _ = (edges : ℝ)*(edges+1)*(∑ vertex,realPath input vertex^2) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    _ ≤ _ := by
      have hs : 0 ≤ ∑ vertex,realPath input vertex^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith

end
end AFT.BodyPadding

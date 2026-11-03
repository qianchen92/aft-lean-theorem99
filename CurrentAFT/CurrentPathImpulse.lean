import CurrentAFT.CurrentBinaryIncidence

/-! The actual executed path entry is the full integral path-incidence basis column. -/
namespace CurrentAFT.CurrentPathImpulse
open AFT
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

 theorem pathLoad_indicator (count column : ℕ) (vertex : Fin (count + 1)) :
    pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex =
      if column < count then (if vertex.val = column then 1 else 0) -
        (if vertex.val = column + 1 then 1 else 0) else 0 := by
  induction count generalizing column with
  | zero => simp only [pathLoad, Pi.zero_apply, Nat.not_lt_zero, if_false]
  | succ count ih =>
    cases column with
    | zero =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = 0 then (1 : ℤ) else 0) = 0 := by
          funext edge
          simp [Fin.tail]
        rw [pathLoad, Fin.cons_succ, ht, pathLoad_zero]
        have he : rest.val + 1 = 1 ↔ rest = 0 := by
          constructor
          · intro h; apply Fin.ext; change rest.val = 0; omega
          · rintro rfl; rfl
        change (0 - if rest = 0 then (1 : ℤ) else 0) =
          if 0 < count + 1 then (if rest.val + 1 = 0 then 1 else 0) -
            (if rest.val + 1 = 1 then 1 else 0) else 0
        simp only [Nat.zero_lt_succ, if_true, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, he]
    | succ column =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = column + 1 then (1 : ℤ) else 0) =
            (fun edge : Fin count => if edge.val = column then 1 else 0) := by
          funext edge
          simp [Fin.tail]
        rw [pathLoad, Fin.cons_succ, ht, ih]
        have hf : ((0 : Fin (count + 1)).val = column + 1) = False := by simp
        have hp : rest.succ.val = column + 1 ↔ rest.val = column := by simp
        have hn : rest.succ.val = column + 1 + 1 ↔ rest.val = column + 1 := by simp
        simp only [hf, if_false, ite_self, Nat.add_lt_add_iff_right, hp, hn]
        exact sub_zero _

 theorem pathEntry_basis (count column : ℕ) (vertex : Fin (count + 1)) :
    (CurrentBinaryIncidence.pathEntry count column vertex.val).value.decode =
      pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex := by
  rw [CurrentBinaryIncidence.pathEntry_value, pathLoad_indicator]

end CurrentAFT.CurrentPathImpulse

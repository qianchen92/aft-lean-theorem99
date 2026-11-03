import CurrentAFT.AffineBaseline
import CurrentAFT.ActualBlockMean

/-! # The public closing edge gives exactly the protected closed cycle -/
namespace CurrentAFT.CyclePathClosure
open AFT PublicCharge AffineBaseline
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem pathLoad_snoc_sub_cons (count : ℕ) (edges : Fin count → ℤ) :
    pathLoad count edges = Fin.snoc edges 0 - Fin.cons 0 edges := by
  induction count with
  | zero =>
    funext index
    have hi : index = (0 : Fin 1) := Fin.eq_zero index
    subst index
    simp [pathLoad, Fin.snoc_zero]
  | succ count ih =>
    have he : edges = Fin.cons (edges 0) (Fin.tail edges) := (Fin.cons_self_tail edges).symm
    conv_rhs => rw [he, ← Fin.cons_snoc_eq_snoc_cons]
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp [pathLoad]
    · simp only [pathLoad, Fin.cons_succ, Pi.sub_apply, ih]
      refine Fin.cases ?_ (fun next => ?_) rest <;> simp

theorem predecessor_snoc (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.snoc count (fun _ => ℤ) edges scalar) ((finRotate (count + 1)).symm index) =
      (@Fin.cons count (fun _ => ℤ) scalar edges) index := by
  rw [Fin.snoc_eq_cons_rotate]
  simp only [Equiv.apply_symm_apply]

theorem snoc_difference (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.snoc count (fun _ => ℤ) edges scalar) index =
      (@Fin.snoc count (fun _ => ℤ) edges 0) index + if index = Fin.last count then scalar else 0 := by
  refine Fin.lastCases ?_ (fun rest => ?_) index <;> simp

theorem cons_difference (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.cons count (fun _ => ℤ) scalar edges) index =
      (@Fin.cons count (fun _ => ℤ) 0 edges) index + if index = 0 then scalar else 0 := by
  refine Fin.cases ?_ (fun rest => ?_) index <;> simp

theorem cycle_eq_path_closure (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) :
    cycleDifference (Fin.snoc edges scalar) = pathLoad count edges + closure count scalar := by
  funext index
  rw [cycleDifference, predecessor_snoc, pathLoad_snoc_sub_cons]
  simp only [Pi.add_apply, Pi.sub_apply, AffineBaseline.closure]
  rw [snoc_difference, cons_difference]
  ring

theorem latent_eq_path_closure (count : ℕ) (latent : Fin (count + 1) → ℤ) :
    cycleDifference latent = pathLoad count (Fin.init latent) + closure count (latent (Fin.last count)) := by
  have hlatent : Fin.snoc (Fin.init latent) (latent (Fin.last count)) = latent := Fin.snoc_init_self latent
  rw [← hlatent]
  simpa only [Fin.init_snoc, Fin.snoc_last] using cycle_eq_path_closure count (Fin.init latent) (latent (Fin.last count))

theorem placed_cycle_eq_path_closure (count : ℕ) (placement : Equiv.Perm (Fin (count + 1)))
    (latent : Fin (count + 1) → ℤ) (vertex : Fin (count + 1)) :
    cycleDifference latent (placement.symm vertex) =
      pathLoad count (Fin.init latent) (placement.symm vertex) +
        closure count (latent (Fin.last count)) (placement.symm vertex) :=
  congrFun (latent_eq_path_closure count latent) (placement.symm vertex)

end
end CurrentAFT.CyclePathClosure

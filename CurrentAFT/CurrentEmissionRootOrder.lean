import CurrentAFT.CurrentLayoutDraw
import CurrentAFT.CurrentMaterializedCore

/-! Actual cached path-root positions for the physical root order
attachments, centers, queues. The explicit rotation maps that order to the
placement's center, queue, attachment order before two stored permutation reads. -/
namespace CurrentAFT.CurrentEmissionRootOrder
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources CurrentCoreProposal
open ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount
  CurrentCoreProposal.draw addCounter subtractCounter lessCounter


def rotate (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) : CountedValue (Fin count) :=
  let boundary := subtractCounter count front
  let selected := lessCounter index.val front
  if h : selected.value then
    let added := addCounter boundary.count index.val
    have hi : added.count < count := by
      have hs := (lessCounter_value _ _).mp h
      rw [addCounter_value, subtractCounter_value]
      omega
    ⟨⟨added.count, hi⟩, boundary.work + selected.work + added.work + 3⟩
  else
    let reduced := subtractCounter index.val front
    have hi : reduced.count < count := by rw [subtractCounter_value]; exact (Nat.sub_le _ _).trans_lt index.isLt
    ⟨⟨reduced.count, hi⟩, boundary.work + selected.work + reduced.work + 3⟩

 theorem rotate_value (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) :
    (rotate count front hprefix index).value.val = if index.val < front then count - front + index.val else index.val - front := by
  by_cases hi : index.val < front
  · have hs : (lessCounter index.val front).value = true := (lessCounter_value _ _).mpr hi
    simp only [rotate, dif_pos hs, Fin.val_mk, addCounter_value, subtractCounter_value, if_pos hi]
  · have hs : ¬(lessCounter index.val front).value = true := by simpa only [lessCounter_value] using hi
    simp only [rotate, dif_neg hs, Fin.val_mk, subtractCounter_value, if_neg hi]

 theorem rotate_work (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) :
    (rotate count front hprefix index).work ≤ 7 * count + 8 := by
  have hb := subtractCounter_work_left count front
  have hs := lessCounter_work_left index.val front
  have ha := addCounter_work (subtractCounter count front).count index.val
  have hr := subtractCounter_work_left index.val front
  have hbc : (subtractCounter count front).count ≤ count := by rw [subtractCounter_value]; exact Nat.sub_le _ _
  have hi := index.isLt
  dsimp only [rotate]
  split_ifs <;> dsimp only <;> omega

abbrev RootIndex (security : ℕ) := Fin (Parameters.legCount security) ⊕
  (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))

 theorem root_count (security : ℕ) : Parameters.legCount security + (centerCount security + Parameters.modulus security) =
    (current security).body := by
  rw [(current_values security).2.2.1]
  have h := ProposalPrimary.population_room security
  unfold centerCount
  omega

def rootNumbering (security : ℕ) : RootIndex security ≃ Fin (current security).body :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (root_count security))

def rootToRole (security : ℕ) : RootIndex security ≃ RoleIndex security where
  toFun
    | .inl leg => .inr (.inr leg)
    | .inr (.inl center) => .inl center
    | .inr (.inr queue) => .inr (.inl queue)
  invFun
    | .inl center => .inr (.inl center)
    | .inr (.inl queue) => .inr (.inr queue)
    | .inr (.inr leg) => .inl leg
  left_inv := by rintro (leg | (center | queue)) <;> rfl
  right_inv := by rintro (center | (queue | leg)) <;> rfl

 theorem legs_le_body (security : ℕ) : (current security).legs ≤ (current security).body := by
  rw [(current_values security).2.1, (current_values security).2.2.1]
  have h := ProposalPrimary.population_room security
  omega

 theorem rotate_role (security : ℕ) (index : Fin (current security).body) :
    CurrentProposalDimensions.bodyEquiv security
      (rotate (current security).body (current security).legs (legs_le_body security) index).value =
    CurrentLayoutDraw.canonicalLayout security (rootToRole security ((rootNumbering security).symm index)) := by
  obtain ⟨leg | (center | queue), rfl⟩ := (rootNumbering security).surjective index
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals apply Fin.ext
  · have hi : leg.val < (current security).legs := by simpa only [(current_values security).2.1] using leg.isLt
    have hcount := root_count security
    change (rotate _ _ _ (rootNumbering security (.inl leg))).value.val = _
    rw [rotate_value]
    have hv : (rootNumbering security (.inl leg)).val = leg.val := rfl
    rw [hv, if_pos hi]
    change (current security).body - (current security).legs + leg.val =
      BackgroundPopulationBounds.freeCount security + (Parameters.modulus security + leg.val)
    rw [(current_values security).2.1]
    unfold BackgroundPopulationBounds.freeCount centerCount at *
    omega
  · change (rotate _ _ _ (rootNumbering security (.inr (.inl center)))).value.val = _
    rw [rotate_value]
    have hv : (rootNumbering security (.inr (.inl center))).val = Parameters.legCount security + center.val := rfl
    rw [hv]
    have hn : ¬Parameters.legCount security + center.val < (current security).legs := by
      rw [(current_values security).2.1]; omega
    rw [if_neg hn]
    change Parameters.legCount security + center.val - (current security).legs = center.val
    rw [(current_values security).2.1]
    omega
  · change (rotate _ _ _ (rootNumbering security (.inr (.inr queue)))).value.val = _
    rw [rotate_value]
    have hv : (rootNumbering security (.inr (.inr queue))).val = Parameters.legCount security + (centerCount security + queue.val) := rfl
    rw [hv]
    have hn : ¬Parameters.legCount security + (centerCount security + queue.val) < (current security).legs := by
      rw [(current_values security).2.1]; omega
    rw [if_neg hn]
    change Parameters.legCount security + (centerCount security + queue.val) - (current security).legs =
      BackgroundPopulationBounds.freeCount security + queue.val
    rw [(current_values security).2.1]
    unfold BackgroundPopulationBounds.freeCount centerCount
    omega


def positions (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security) :
    CountedValue (Vector (Fin (current security).body) (current security).body) :=
  storeData (current security).body (fun index =>
    let rotated := rotate (current security).body (current security).legs (legs_le_body security) index
    let placed := readVector index layout.forward rotated.value
    let path := readVector index data.body.inverse placed.value
    ⟨path.value, rotated.work + placed.work + path.work + 3⟩)

 theorem positions_value (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security)
    (index : Fin (current security).body) :
    (positions security layout data).value.get index =
      data.body.inverse.get (layout.forward.get (rotate (current security).body (current security).legs (legs_le_body security) index).value) := by
  simp only [positions, storeData_get, readVector_value]

 theorem positions_work (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security) :
    (positions security layout data).work ≤ (current security).body * (13 * (current security).body + 19) + 2 := by
  apply storeData_work
  intro index
  have hr := rotate_work (current security).body (current security).legs (legs_le_body security) index
  have hp := readVector_work index layout.forward
    (rotate (current security).body (current security).legs (legs_le_body security) index).value
  have hi := readVector_work index data.body.inverse
    (readVector index layout.forward (rotate (current security).body (current security).legs (legs_le_body security) index).value).value
  change (rotate _ _ _ index).work + (readVector index layout.forward _).work + (readVector index data.body.inverse _).work + 3 ≤ _
  omega


private theorem conjugate_inverse {State Target : Type*} (equiv : State ≃ Target) (permutation : Equiv.Perm State) (state : State) :
    (equiv.permCongr permutation).symm (equiv state) = equiv (permutation.symm state) := by
  apply (equiv.permCongr permutation).injective
  simp only [Equiv.apply_symm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]

 theorem positions_actual (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security)
    (index : Fin (current security).body) :
    CurrentProposalDimensions.bodyEquiv security ((positions security layout data).value.get index) =
      data.core.bodyPermutation.symm (layout.layout (rootToRole security ((rootNumbering security).symm index))) := by
  rw [positions_value]
  change CurrentProposalDimensions.bodyEquiv security
      (data.body.toEquiv.symm (layout.toEquiv (rotate _ _ _ index).value)) =
    ((CurrentProposalDimensions.bodyEquiv security).permCongr data.body.toEquiv).symm
      (((CurrentProposalDimensions.bodyEquiv security).permCongr layout.toEquiv)
        (CurrentLayoutDraw.canonicalLayout security (rootToRole security ((rootNumbering security).symm index))))
  rw [← rotate_role security index, Equiv.permCongr_apply, Equiv.symm_apply_apply, conjugate_inverse]

end CurrentAFT.CurrentEmissionRootOrder

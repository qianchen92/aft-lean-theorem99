import CurrentAFT.RationalPackedRootUntagged

/-! # Untagged reference errors use one factor per actual root slot -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedUntaggedBoundsFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedUntaggedBoundsSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedUntaggedBoundsSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

theorem rootSlot_card_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Fintype.card (Slot selection tagged) ≤ 2 * groupCount selection tagged := by
  have hi : Function.Injective (CurrentRootSlotIndex.encode selection tagged (ordering selection tagged)) := by
    intro first second h
    have hd := congrArg (CurrentRootSlotIndex.decode selection tagged (ordering selection tagged)) h
    simpa only [decode_encode, Option.some.injEq] using hd
  have h := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_fin, Nat.mul_comm] using h

theorem untaggedFactor_bounds {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) :
    0 ≤ (untaggedFactor bits selection tagged source root : ℝ) ∧
      (untaggedFactor bits selection tagged source root : ℝ) ≤ 1 := by
  unfold untaggedFactor
  split_ifs
  · norm_num
  · exact RootSignedMassProgram.referenceEntry_bounds security bits _

theorem untagged_bounds {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    0 ≤ (untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) ∧
    (untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) ≤ 1 := by
  rw [untagged_sourceIndex, Rat.cast_prod]
  exact ⟨Finset.prod_nonneg (fun root _ => (untaggedFactor_bounds bits selection tagged source root).1),
    Finset.prod_le_one (fun root _ => (untaggedFactor_bounds bits selection tagged source root).1)
      (fun root _ => (untaggedFactor_bounds bits selection tagged source root).2)⟩

theorem untaggedWeight_bounds {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    0 ≤ RootWeightedSynthesis.untaggedWeight selection tagged source ∧
      RootWeightedSynthesis.untaggedWeight selection tagged source ≤ 1 := by
  rw [untaggedWeight_product]
  have hb (root : Slot selection tagged) :
      0 ≤ (if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (rootReference security).weight ((source root.fst).1 root.snd)) ∧
      (if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
        (rootReference security).weight ((source root.fst).1 root.snd)) ≤ 1 := by
    split_ifs
    · norm_num
    · exact ⟨FiniteDist.nonneg _ _, FiniteDist.atom_le_one _ _⟩
  exact ⟨Finset.prod_nonneg (fun root _ => (hb root).1),
    Finset.prod_le_one (fun root _ => (hb root).1) (fun root _ => (hb root).2)⟩

theorem untagged_error {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    |(untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      RootWeightedSynthesis.untaggedWeight selection tagged source| ≤
      (4 * groupCount selection tagged : ℕ) * (1 / (2 : ℝ)^bits) := by
  rw [untagged_sourceIndex, Rat.cast_prod, untaggedWeight_product]
  let first := fun root : Slot selection tagged => (untaggedFactor bits selection tagged source root : ℝ)
  let second := fun root : Slot selection tagged =>
    if rootEmbedding selection tagged root ∈ tagged then (1 : ℝ) else
      (rootReference security).weight ((source root.fst).1 root.snd)
  have hsecond (root : Slot selection tagged) : |second root| ≤ 1 := by
    dsimp only [second]
    split_ifs
    · norm_num
    · rw [abs_of_nonneg ((rootReference security).nonneg ((source root.fst).1 root.snd))]
      exact (rootReference security).atom_le_one _
  have hdiff (root : Slot selection tagged) : |first root - second root| ≤ 2 / (2 : ℝ)^bits := by
    dsimp only [first, second, untaggedFactor]
    split_ifs
    · simp only [Rat.cast_one, sub_self, abs_zero]; positivity
    · exact RootSignedMassProgram.referenceEntry_error security bits _
  have h := RationalTensorInverseProgram.product_difference_bound Finset.univ first second 1
    (2 / (2 : ℝ)^bits) (by norm_num) (by positivity)
    (fun root _ => (abs_of_nonneg (untaggedFactor_bounds bits selection tagged source root).1).trans_le
      (untaggedFactor_bounds bits selection tagged source root).2)
    (fun root _ => hsecond root) (fun root _ => hdiff root)
  simp only [Finset.card_univ, one_pow, mul_one] at h
  refine h.trans ?_
  have hc : (Fintype.card (Slot selection tagged) : ℝ) ≤ 2 * groupCount selection tagged := by
    exact_mod_cast rootSlot_card_le selection tagged
  calc
    _ ≤ (2 * groupCount selection tagged : ℝ) * (2 / (2 : ℝ)^bits) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by push_cast; ring

end
end CurrentAFT.RationalPackedRootProgram

import AFT.FiniteSetNumbering
import AFT.V7PublicPlacement

/-! # Actual disjoint public control and reserve pools -/

namespace AFT.PublicPools

open scoped BigOperators Classical

noncomputable section

variable {Position : Type*} [Fintype Position] [DecidableEq Position]

def controls (legs queue : Finset Position) := legs \ queue

def available (legs queue : Finset Position) := (legs ∪ queue)ᶜ

omit [Fintype Position] in
theorem controls_card_le (legs queue : Finset Position) : (controls legs queue).card ≤ legs.card :=
  Finset.card_le_card Finset.sdiff_subset

theorem available_card_lower (legs queue : Finset Position) :
    Fintype.card Position - legs.card - queue.card ≤ (available legs queue).card := by
  rw [available, Finset.card_compl]
  have hh := Finset.card_union_le legs queue
  omega

/-- Enough unoccupied positions exist for one distinct compensator per
retained leg. The witness is an explicit composition of finite numberings. -/
def matching (legs queue : Finset Position)
    (hsize : 2 * legs.card + queue.card ≤ Fintype.card Position) :
    controls legs queue ↪ available legs queue :=
  (Fintype.equivFin (controls legs queue)).toEmbedding.trans
    ((Fin.castLEEmb (by
      have hc := controls_card_le legs queue
      have ha := available_card_lower legs queue
      simp only [Fintype.card_coe]
      omega)).trans (Fintype.equivFin (available legs queue)).symm.toEmbedding)

def matchingPositions (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  Finset.univ.map ⟨fun control => (pairing control).val,
    fun _ _ h => pairing.injective (Subtype.ext h)⟩

@[simp] theorem matchingPositions_card (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    (matchingPositions legs queue pairing).card = (controls legs queue).card := by
  simp only [matchingPositions, Finset.card_map, Finset.card_univ, Fintype.card_coe]

theorem matchingPositions_subset (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    matchingPositions legs queue pairing ⊆ available legs queue := by
  intro position hp
  obtain ⟨control, _, rfl⟩ := Finset.mem_map.mp hp
  exact (pairing control).property

def reserve (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) : Finset Position :=
  available legs queue \ matchingPositions legs queue pairing

theorem reserve_card_lower (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    Fintype.card Position - 2 * legs.card - queue.card ≤ (reserve legs queue pairing).card := by
  have hh := Finset.card_sdiff_add_card_eq_card (matchingPositions_subset legs queue pairing)
  rw [matchingPositions_card] at hh
  have hc := controls_card_le legs queue
  have ha := available_card_lower legs queue
  change (reserve legs queue pairing).card + (controls legs queue).card = (available legs queue).card at hh
  omega

theorem reserve_disjoint (legs queue : Finset Position)
    (pairing : controls legs queue ↪ available legs queue) :
    Disjoint (reserve legs queue pairing) legs ∧ Disjoint (reserve legs queue pairing) queue ∧
      Disjoint (reserve legs queue pairing) (matchingPositions legs queue pairing) := by
  refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
  · intro position hp hl
    have ha := (Finset.mem_sdiff.mp hp).1
    exact (Finset.mem_compl.mp ha) (Finset.mem_union_left queue hl)
  · intro position hp hq
    have ha := (Finset.mem_sdiff.mp hp).1
    exact (Finset.mem_compl.mp ha) (Finset.mem_union_right legs hq)
  · intro position hp hm
    exact (Finset.mem_sdiff.mp hp).2 hm

end
end AFT.PublicPools

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration PublicPools FiniteDist

noncomputable section

/-- The actual V7 sizes leave more than half of all bodies after removing
all attachments, queue positions, and one compensator for each leg. -/
theorem actual_pool_budget (parameter : ℕ) :
    2 * (2 * Parameters.legs parameter + Parameters.modulus parameter) ≤ Parameters.bodies parameter := by
  have hsecurity : 1 ≤ Parameters.security parameter := (by decide : 1 ≤ 2).trans (Parameters.security_ge_two parameter)
  have hleg : Parameters.legs parameter ≤ Parameters.modulus parameter :=
    (pow_le_pow_right₀ hsecurity (by omega : 30 ≤ 40)).trans (Parameters.modulus_bounds parameter).1
  have hmean : 8 ≤ Parameters.meanDensity parameter := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 20
    dsimp [Parameters.meanDensity]
    omega
  have hdim : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    simpa only [Parameters.dimension, Nat.mul_comm] using Nat.mul_le_mul_left (Parameters.modulus parameter) hmean
  have hpop := Parameters.population_identity parameter
  omega

def actualLegBodies (parameter : ℕ) : Finset (blockIndex parameter) :=
  (Finset.univ : Finset (Fin (Parameters.legs parameter))).map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem actualLegBodies_card (parameter : ℕ) :
    (actualLegBodies parameter).card = Parameters.legs parameter := by
  simp only [actualLegBodies, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def actualControlMatching (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    controls (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) ↪
      available (actualLegBodies parameter) (permutationMask (actualQueueSelection parameter) placement) :=
  finiteSetMatching (blockIndexNumbering parameter) _ _ (by
    have hc := controls_card_le (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    have ha := available_card_lower (actualLegBodies parameter)
      (permutationMask (actualQueueSelection parameter) placement)
    simp only [actualLegBodies_card, permutationMask_card, actualQueueSelection_card, blockIndex_card] at hc ha
    have hh := actual_pool_budget parameter
    omega)

def actualReservedBodies (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    Finset (blockIndex parameter) :=
  reserve _ _ (actualControlMatching parameter placement)

/-- The reserve is large for every public queue placement, including those
with an atypically large attachment overlap. -/
theorem actualReservedBodies_large (parameter : ℕ) (placement : Equiv.Perm (blockIndex parameter)) :
    Parameters.bodies parameter ≤ 2 * (actualReservedBodies parameter placement).card := by
  have hh := reserve_card_lower _ _ (actualControlMatching parameter placement)
  simp only [blockIndex_card, actualLegBodies_card, permutationMask_card, actualQueueSelection_card] at hh
  change Parameters.bodies parameter - 2 * Parameters.legs parameter - Parameters.modulus parameter ≤
    (actualReservedBodies parameter placement).card at hh
  have hb := actual_pool_budget parameter
  omega

end
end AFT.GaussianSource

import AFT.PublicSourceEmbedding
import AFT.ActualInputMixedTail

/-! # Actual public choices have disjoint, queue-free physical root sources -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev actualControlPool (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :=
  controls (actualLegBodies n) (permutationMask (actualQueueSelection n) placement)

abbrev ActualPublicPrimaryChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Primary : Type*) :=
  Primary ↪ actualControlPool n placement

abbrev ActualPublicBodyChoice (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (Body : Type*) :=
  Body ↪ actualReservedBodies n placement

def actualPublicSourceEmbedding (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (Primary ⊕ Primary) ⊕ Body ↪ blockIndex n :=
  sourceEmbedding _ _ (actualControlMatching n placement) primary body

def actualPublicSelected (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) : Finset (blockIndex n) :=
  sourceSelection _ _ (actualControlMatching n placement) primary body

def actualPublicSourceEquiv (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ actualPublicSelected n placement primary body :=
  sourceEquiv _ _ (actualControlMatching n placement) primary body

@[simp] theorem actualPublicSourceEquiv_val (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (actualPublicSourceEquiv n placement primary body source).val=actualPublicSourceEmbedding n placement primary body source := rfl

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_queue_zero (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (queue : Window (queueCutoff n)) (source : (Primary ⊕ Primary) ⊕ Body) :
    actualQueueShifts n (queue,placement) (actualPublicSourceEmbedding n placement primary body source)=0 := by
  have hh := sourceEmbedding_queue_free _ _ (actualControlMatching n placement) primary body source
  rw [permutationMask_mem] at hh
  exact if_neg hh

theorem mem_actualLegBodies_iff (n : ℕ) (index : blockIndex n) :
    index∈actualLegBodies n ↔ ∃ leg,index=Sum.inl leg := by
  simp only [actualLegBodies,Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coeFn_mk]
  exact exists_congr fun _ => eq_comm

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_attached (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ leg,actualPublicSourceEmbedding n placement primary body (.inl (.inl index))=Sum.inl leg := by
  apply (mem_actualLegBodies_iff n _).mp
  exact (Finset.mem_sdiff.mp (primary index).property).1

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_compensator (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Primary) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inl (.inr index))=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inl (.inr index))∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (actualControlMatching n placement (primary index)).property)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩

omit [Fintype Primary] [Fintype Body] in
theorem actualPublicSource_body (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (index : Body) : ∃ free,actualPublicSourceEmbedding n placement primary body (.inr index)=Sum.inr free := by
  have hn : actualPublicSourceEmbedding n placement primary body (.inr index)∉actualLegBodies n := by
    exact fun h => (Finset.mem_compl.mp (Finset.mem_sdiff.mp (body index).property).1)
      (Finset.mem_union_left _ h)
  cases he : actualPublicSourceEmbedding n placement primary body (.inr index) with
  | inl leg => exact False.elim (hn ((mem_actualLegBodies_iff n _).mpr ⟨leg,he⟩))
  | inr free => exact ⟨free,rfl⟩


@[simp] theorem actualPublicSelected_card (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body) :
    (actualPublicSelected n placement primary body).card=2*Fintype.card Primary+Fintype.card Body := by
  simp only [actualPublicSelected,sourceSelection,Finset.card_map,Finset.card_univ,Fintype.card_sum]
  omega

theorem actualPublicSelected_queue_zero (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (primary : ActualPublicPrimaryChoice n placement Primary) (body : ActualPublicBodyChoice n placement Body)
    (queue : Window (queueCutoff n)) (index : actualPublicSelected n placement primary body) :
    actualQueueShifts n (queue,placement) index.val=0 := by
  obtain ⟨source,rfl⟩ := (actualPublicSourceEquiv n placement primary body).surjective index
  exact actualPublicSource_queue_zero n placement primary body queue source

/-- Canonical finite numberings turn any legal distinct pool indices into
actual public choices; no matching or source-disjointness hypothesis is used. -/
def actualPublicPrimaryFromIndices (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (indices : Primary ↪ Fin (actualControlPool n placement).card) : ActualPublicPrimaryChoice n placement Primary :=
  indices.trans (finiteSetNumbering (blockIndexNumbering n) (actualControlPool n placement)).toEmbedding

def actualPublicBodyFromIndices (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (indices : Body ↪ Fin (actualReservedBodies n placement).card) : ActualPublicBodyChoice n placement Body :=
  indices.trans (finiteSetNumbering (blockIndexNumbering n) (actualReservedBodies n placement)).toEmbedding

theorem actualPublicPrimaryChoice_nonempty (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (hsize : Fintype.card Primary≤(actualControlPool n placement).card) :
    Nonempty (ActualPublicPrimaryChoice n placement Primary) := by
  exact ⟨actualPublicPrimaryFromIndices n placement ((Fintype.equivFin Primary).toEmbedding.trans (Fin.castLEEmb hsize))⟩

theorem actualPublicBodyChoice_nonempty (n : ℕ) (placement : Equiv.Perm (blockIndex n))
    (hsize : Fintype.card Body≤(actualReservedBodies n placement).card) :
    Nonempty (ActualPublicBodyChoice n placement Body) := by
  exact ⟨actualPublicBodyFromIndices n placement ((Fintype.equivFin Body).toEmbedding.trans (Fin.castLEEmb hsize))⟩

end
end AFT.V7Calibration

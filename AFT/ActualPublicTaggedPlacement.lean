import AFT.ActualPublicSources
import AFT.RoleSourceSlots

/-! # Concrete tagged placements from the actual public pools -/
namespace AFT.V7Calibration
open GaussianSource PublicPools FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {count : ℕ} (n : ℕ) (placement : Equiv.Perm (blockIndex n)) (role : Fin count → Bool)
    (primary : ActualPublicPrimaryChoice n placement (PrimaryRoles role))
    (body : ActualPublicBodyChoice n placement (BodyRoles role))

def actualPublicSourceSlotEquiv (source : RoleSources role) :
    roleSourceSlots role source ≃ blockSlots n (actualPublicSourceEmbedding n placement primary body source) :=
  Equiv.cast (by
    rcases source with ⟨index|index⟩|index
    · obtain ⟨leg,hleg⟩ := actualPublicSource_attached n placement primary body index
      rw [hleg]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_compensator n placement primary body index
      rw [hfree]
      rfl
    · obtain ⟨free,hfree⟩ := actualPublicSource_body n placement primary body index
      rw [hfree]
      rfl)

def actualPublicSlotsEquiv : Sigma (fun index => actualRoleSlots (role index)) ≃
    actualMarkedSlots n (actualPublicSelected n placement primary body) :=
  ((roleOutputSourceEquiv role).trans (Equiv.sigmaCongrRight
    (actualPublicSourceSlotEquiv n placement role primary body))).trans
    (Equiv.sigmaCongrLeft (β:=fun source : actualPublicSelected n placement primary body => blockSlots n source.val)
      (actualPublicSourceEquiv n placement primary body))

def actualPublicAttached (index : Fin count) : blockIndex n :=
  if h : role index=true then (primary ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicCompensator (index : Fin count) : blockIndex n :=
  if h : role index=true then (actualControlMatching n placement (primary ⟨index,h⟩)).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicBody (index : Fin count) : blockIndex n :=
  if h : ¬role index=true then (body ⟨index,h⟩).val else
    Sum.inl ⟨0,by have hh := Parameters.security_ge_two n; unfold Parameters.legs; positivity⟩

def actualPublicTaggedPlacement : ActualTaggedPlacement n count role (actualPublicSelected n placement primary body) where
  attached := actualPublicAttached n placement role primary
  compensator := actualPublicCompensator n placement role primary
  body := actualPublicBody n placement role body
  slots := actualPublicSlotsEquiv n placement role primary body

@[simp] theorem actualPublicAttached_source (index : PrimaryRoles role) :
    actualPublicAttached n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inl index)) := by
  simp only [actualPublicAttached,dif_pos index.property]
  rfl

@[simp] theorem actualPublicCompensator_source (index : PrimaryRoles role) :
    actualPublicCompensator n placement role primary index.val=
      actualPublicSourceEmbedding n placement primary body (.inl (.inr index)) := by
  simp only [actualPublicCompensator,dif_pos index.property]
  rfl

@[simp] theorem actualPublicBody_source (index : BodyRoles role) :
    actualPublicBody n placement role body index.val=
      actualPublicSourceEmbedding n placement primary body (.inr index) := by
  simp only [actualPublicBody,dif_pos index.property]
  rfl

/-- The actual public tuple uses disjoint roots; this includes both roots of
each primary operation and every controlled ordinary body. -/
theorem actualPublicTaggedPlacement_sources_injective :
    Function.Injective (fun source : RoleSources role => match source with
      | .inl (.inl index) => (actualPublicTaggedPlacement n placement role primary body).attached index.val
      | .inl (.inr index) => (actualPublicTaggedPlacement n placement role primary body).compensator index.val
      | .inr index => (actualPublicTaggedPlacement n placement role primary body).body index.val) := by
  have heq : (fun source : RoleSources role => match source with
      | .inl (.inl index) => (actualPublicTaggedPlacement n placement role primary body).attached index.val
      | .inl (.inr index) => (actualPublicTaggedPlacement n placement role primary body).compensator index.val
      | .inr index => (actualPublicTaggedPlacement n placement role primary body).body index.val)=
      actualPublicSourceEmbedding n placement primary body := by
    funext source
    rcases source with ⟨index|index⟩|index
    · exact actualPublicAttached_source n placement role primary body index
    · exact actualPublicCompensator_source n placement role primary body index
    · exact actualPublicBody_source n placement role primary body index
  rw [heq]
  exact (actualPublicSourceEmbedding n placement primary body).injective


/-- The slot equivalence preserves the actual physical source index, rather
than merely its cardinality. -/
@[simp] theorem actualPublicSlotsEquiv_source
    (coordinate : Sigma (fun index => actualRoleSlots (role index))) :
    (actualPublicSlotsEquiv n placement role primary body coordinate).1.val=
      actualPublicSourceEmbedding n placement primary body ((roleOutputSourceEquiv role coordinate).1) := rfl

theorem actualPublicTaggedPlacement_primary_queue_zero (queue : Window (queueCutoff n)) (index : PrimaryRoles role) :
    actualQueueShifts n (queue,placement) ((actualPublicTaggedPlacement n placement role primary body).attached index.val)=0 ∧
      actualQueueShifts n (queue,placement) ((actualPublicTaggedPlacement n placement role primary body).compensator index.val)=0 := by
  change actualQueueShifts n (queue,placement) (actualPublicAttached n placement role primary index.val)=0 ∧
    actualQueueShifts n (queue,placement) (actualPublicCompensator n placement role primary index.val)=0
  rw [actualPublicAttached_source n placement role primary body index,
    actualPublicCompensator_source n placement role primary body index]
  exact ⟨actualPublicSource_queue_zero n placement primary body queue _,actualPublicSource_queue_zero n placement primary body queue _⟩

theorem actualPublicTaggedPlacement_body_queue_zero (queue : Window (queueCutoff n)) (index : BodyRoles role) :
    actualQueueShifts n (queue,placement) ((actualPublicTaggedPlacement n placement role primary body).body index.val)=0 := by
  change actualQueueShifts n (queue,placement) (actualPublicBody n placement role body index.val)=0
  rw [actualPublicBody_source n placement role primary body index]
  exact actualPublicSource_queue_zero n placement primary body queue _

end
end AFT.V7Calibration

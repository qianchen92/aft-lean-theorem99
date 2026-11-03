import AFT.PublicPools

/-! # Distinct physical sources from the real public matching and reserve -/
namespace AFT.PublicPools
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Position Primary Body : Type*} [Fintype Position] [DecidableEq Position]

/-- Attached sources, their injectively matched compensators, and reserved
body sources are three genuinely disjoint populations. -/
def sourceFunction (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body → Position
  | .inl (.inl index) => (primary index).val
  | .inl (.inr index) => (pairing (primary index)).val
  | .inr index => (body index).val

theorem sourceFunction_injective (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    Function.Injective (sourceFunction legs queue pairing primary body) := by
  have hp (i : Primary) : (primary i).val∈legs := (Finset.mem_sdiff.mp (primary i).property).1
  have hc (i : Primary) : (pairing (primary i)).val∉legs := by
    have hh := Finset.mem_compl.mp (pairing (primary i)).property
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hb (i : Body) : (body i).val∉legs := by
    have hh := Finset.mem_compl.mp (Finset.mem_sdiff.mp (body i).property).1
    exact fun hi => hh (Finset.mem_union_left queue hi)
  have hm (i : Primary) : (pairing (primary i)).val∈matchingPositions legs queue pairing :=
    Finset.mem_map.mpr ⟨primary i,Finset.mem_univ _,rfl⟩
  have hbm (i : Body) : (body i).val∉matchingPositions legs queue pairing :=
    (Finset.mem_sdiff.mp (body i).property).2
  rintro (⟨i|i⟩|i) (⟨j|j⟩|j) he <;> dsimp only [sourceFunction] at he
  · exact congrArg (Sum.inl ∘ Sum.inl) (primary.injective (Subtype.ext he))
  · exact False.elim (hc j (he ▸ hp i))
  · exact False.elim (hb j (he ▸ hp i))
  · exact False.elim (hc i (he.symm ▸ hp j))
  · exact congrArg (Sum.inl ∘ Sum.inr) (primary.injective (pairing.injective (Subtype.ext he)))
  · exact False.elim (hbm j (he ▸ hm i))
  · exact False.elim (hb i (he.symm ▸ hp j))
  · exact False.elim (hbm i (he.symm ▸ hm j))
  · exact congrArg Sum.inr (body.injective (Subtype.ext he))

def sourceEmbedding (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    (Primary ⊕ Primary) ⊕ Body ↪ Position :=
  ⟨sourceFunction legs queue pairing primary body,sourceFunction_injective legs queue pairing primary body⟩

theorem sourceEmbedding_queue_free (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing)
    (source : (Primary ⊕ Primary) ⊕ Body) : sourceEmbedding legs queue pairing primary body source∉queue := by
  rcases source with ⟨index|index⟩|index
  · exact (Finset.mem_sdiff.mp (primary index).property).2
  · exact fun hq => (Finset.mem_compl.mp (pairing (primary index)).property) (Finset.mem_union_right legs hq)
  · exact fun hq => (Finset.mem_compl.mp (Finset.mem_sdiff.mp (body index).property).1) (Finset.mem_union_right legs hq)

variable [Fintype Primary] [Fintype Body]

def sourceSelection (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) : Finset Position :=
  Finset.univ.map (sourceEmbedding legs queue pairing primary body)

def sourceEquiv (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing) :
    ((Primary ⊕ Primary) ⊕ Body) ≃ sourceSelection legs queue pairing primary body :=
  Equiv.ofBijective (fun source => ⟨sourceEmbedding legs queue pairing primary body source,
    Finset.mem_map.mpr ⟨source,Finset.mem_univ _,rfl⟩⟩) ⟨
      fun a b h => (sourceEmbedding legs queue pairing primary body).injective (congrArg Subtype.val h),by
      rintro ⟨position,hposition⟩
      obtain ⟨source,_,hs⟩ := Finset.mem_map.mp hposition
      exact ⟨source,Subtype.ext hs⟩⟩

@[simp] theorem sourceEquiv_val (legs queue : Finset Position) (pairing : controls legs queue ↪ available legs queue)
    (primary : Primary ↪ controls legs queue) (body : Body ↪ reserve legs queue pairing)
    (source : (Primary ⊕ Primary) ⊕ Body) :
    (sourceEquiv legs queue pairing primary body source).val=sourceEmbedding legs queue pairing primary body source := rfl

end
end AFT.PublicPools

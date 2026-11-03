import AFT.PendingFiniteIndices

/-! # Fixed-order bounds preserved by executable pending expansion -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingProgramValidityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem pendingPrimaryCount (primary : ℕ) (point : Fin primary) (selected : Finset (Fin 4)) :
    Fintype.card (selected ⊕ {other : Fin primary // other≠point})=selected.card+(primary-1) := by
  have hh := Fintype.card_congr (primarySplitEquiv point)
  simp only [Fintype.card_sum,Fintype.card_unique,Fintype.card_fin] at hh
  simp only [Fintype.card_sum,Fintype.card_coe]
  omega

theorem storedPendingOld_lt {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (primary : ℕ) (hp : primary≤bound) (point : Fin primary) (mask : Fin 16)
    (old : Fin primary) (ho : old≠point) :
    numbering.primaryLookup ⟨primary,by omega⟩ ⟨point.val,by omega⟩ mask ⟨old.val+4,by omega⟩<
      (pendingMask mask).card+(primary-1) := by
  rw [hnumbering]
  rw [pendingNumberingMeaning_old (⟨primary,by omega⟩ : Fin (bound+1)) ⟨point.val,by omega⟩ point.isLt mask ⟨old,ho⟩]
  have hh := (Fintype.equivFin (pendingMask mask ⊕ {other : Fin primary // other≠point}) (Sum.inr ⟨old,ho⟩)).isLt
  simpa only [pendingPrimaryCount] using hh

theorem pendingProgramLinear_valid {Leaf : Type*} {bound : ℕ} {leafShape : Leaf → KernelShape}
    {state : PendingProgramState Leaf} (hs : state.Valid bound leafShape) :
    (pendingProgramLinear state).Valid bound leafShape := by
  unfold pendingProgramLinear
  split_ifs with hn
  · refine ⟨hs.1,?_,?_⟩
    · intro point hp;exact hs.2.1 point (Finset.mem_of_mem_erase hp)
    · have hh := Finset.card_le_card (Finset.erase_subset (state.pending.min' hn) state.pending)
      change (state.kernel.shape leafShape).primary+3*(state.pending.erase _).card≤bound
      have hpot := hs.2.2
      omega
  · exact hs

theorem pendingProgramHigher_valid {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    {leafShape : Leaf → KernelShape} {state : PendingProgramState Leaf}
    (hs : state.Valid bound leafShape) (mask : Fin 16) :
    (pendingProgramHigher numbering leafShape state mask).Valid bound leafShape := by
  by_cases hn : state.pending.Nonempty
  · let point := state.pending.min' hn
    have hpoint : point∈state.pending := Finset.min'_mem _ hn
    have hlt : point<(state.kernel.shape leafShape).primary := hs.2.1 point hpoint
    have hbound := hs.1.shape_bound
    have hmask : (pendingMask mask).card≤4 := by
      exact (Finset.card_le_univ (pendingMask mask)).trans_eq (Fintype.card_fin 4)
    have hcard := Finset.card_erase_add_one hpoint
    have hpot := hs.2.2
    have hnew : (pendingMask mask).card+((state.kernel.shape leafShape).primary-1)≤bound := by omega
    have hb : (state.kernel.shape leafShape).primary≤bound ∧ point<(state.kernel.shape leafShape).primary := ⟨hbound.1,hlt⟩
    dsimp only [point] at hlt hb
    simp only [pendingProgramHigher,dif_pos hn]
    rw [dif_pos hb]
    refine ⟨⟨hs.1,hlt,hnew⟩,?_,?_⟩
    · intro new hnewmem
      obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hnewmem
      have ho := hs.2.1 old (Finset.mem_of_mem_erase hold)
      have hne : (⟨old,ho⟩ : Fin (state.kernel.shape leafShape).primary)≠⟨point,hlt⟩ := by
        intro he;exact (Finset.mem_erase.mp hold).1 (congrArg Fin.val he)
      simp only [PendingKernelCode.shape,if_pos hlt,dif_pos ho]
      exact storedPendingOld_lt numbering hnumbering _ hbound.1 ⟨point,hlt⟩ mask ⟨old,ho⟩ hne
    · simp only [PendingKernelCode.shape,if_pos hlt]
      have himage := Finset.card_image_le (s := state.pending.erase point)
        (f := fun other => if ho : other<(state.kernel.shape leafShape).primary then
          numbering.primaryLookup ⟨(state.kernel.shape leafShape).primary,by omega⟩ ⟨point,by omega⟩ mask ⟨other+4,by omega⟩ else 0)
      dsimp only [point] at himage hcard
      omega
  · simpa only [pendingProgramHigher,dif_neg hn] using hs

end
end AFT.RationalNumerics

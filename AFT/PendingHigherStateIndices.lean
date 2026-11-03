import AFT.PendingStateSemantics

/-! # Stored indices agree with the actual old-coordinate embedding -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingHigherStateIndicesFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem pendingHigherState_natural {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (hp : state.seed.primaryOrder≤bound)
    (point : Fin state.seed.primaryOrder) (mask : Fin 16) :
    (pendingHigherState C n beta operator charts state point (pendingMask mask)).pending.image Fin.val=
      ((state.pending.image Fin.val).erase point.val).image (fun other =>
        if ho : other<state.seed.primaryOrder then numbering.primaryLookup
          ⟨state.seed.primaryOrder,by omega⟩ ⟨point.val,by omega⟩ mask ⟨other+4,by omega⟩ else 0) := by
  rw [←Finset.image_erase Fin.val_injective]
  ext new
  constructor
  · intro hnew
    obtain ⟨output,houtput,rfl⟩ := Finset.mem_image.mp hnew
    obtain ⟨old,_,rfl⟩ := Finset.mem_map.mp houtput
    have hne := (Finset.mem_erase.mp old.property).1
    refine Finset.mem_image.mpr ⟨old.val.val,Finset.mem_image.mpr ⟨old.val,old.property,rfl⟩,?_⟩
    simp only [dif_pos old.val.isLt]
    exact numbering.pendingHigherOldEmbedding hnumbering C n beta operator charts state.seed hp point mask ⟨old.val,hne⟩
  · intro hnew
    obtain ⟨other,hother,rfl⟩ := Finset.mem_image.mp hnew
    obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hother
    have hne := (Finset.mem_erase.mp hold).1
    simp only [dif_pos old.isLt]
    rw [numbering.pendingHigherOldEmbedding hnumbering C n beta operator charts state.seed hp point mask ⟨old,hne⟩]
    refine Finset.mem_image.mpr ⟨pendingHigherOldEmbedding C n beta operator charts state.seed point (pendingMask mask) ⟨old,hne⟩,?_,rfl⟩
    exact Finset.mem_map.mpr ⟨⟨old,hold⟩,Finset.mem_attach _ _,rfl⟩

end
end AFT.RationalNumerics

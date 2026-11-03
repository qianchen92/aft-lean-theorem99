import AFT.PendingPrimaryGeometry
import Mathlib.Data.Vector.Basic

/-! # Finite stored numbering for each fixed input-order bound

The numerical program takes the vectors below as finite constant data. Their
existence does not require computing `Fintype.equivFin` at runtime. The stored
vectors depend only on the fixed order bound, and on no security parameter,
source law, beta, channel, or input kernel.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- A mask is the ordinary four-bit output subset. -/
def pendingMask (mask : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun slot => mask.val.testBit slot.val)

def pendingNumberingIndex (bound : ℕ) :
    (Fin (bound+1) × (Fin (bound+1) × (Fin 16 × Fin (bound+4)))) ≃
      Fin ((bound+1)*((bound+1)*(16*(bound+4)))) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finProdFinEquiv

structure FixedOrderNumberingCode (bound : ℕ) where
  primary : Vector ℕ ((bound+1)*((bound+1)*(16*(bound+4))))
  body : Vector ℕ ((bound+1)*(bound+1))

def FixedOrderNumberingCode.primaryLookup {bound : ℕ} (code : FixedOrderNumberingCode bound)
    (order point : Fin (bound+1)) (mask : Fin 16) (slot : Fin (bound+4)) : ℕ :=
  code.primary.get (pendingNumberingIndex bound (order,point,mask,slot))

def FixedOrderNumberingCode.bodyLookup {bound : ℕ} (code : FixedOrderNumberingCode bound)
    (order slot : Fin (bound+1)) : ℕ :=
  code.body.get (finProdFinEquiv (order,slot))

noncomputable section
open RepresentedPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance fixedOrderNumberingFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Semantic target for the stored vector; this function is never called
by the executable lookup. -/
def pendingNumberingMeaning {bound : ℕ} (order point : Fin (bound+1))
    (mask : Fin 16) (slot : Fin (bound+4)) : ℕ :=
  if hp : point.val<order.val then
    let selected := pendingMask mask
    let oldPoint : Fin order.val := ⟨point.val,hp⟩
    if hs : slot.val<4 then
      if hm : (⟨slot.val,hs⟩ : Fin 4)∈selected then
        (Fintype.equivFin (selected ⊕ {other : Fin order.val // other≠oldPoint}) (Sum.inl ⟨⟨slot.val,hs⟩,hm⟩)).val
      else 0
    else if ho : slot.val-4<order.val then
      if hd : (⟨slot.val-4,ho⟩ : Fin order.val)≠oldPoint then
        (Fintype.equivFin (selected ⊕ {other : Fin order.val // other≠oldPoint}) (Sum.inr ⟨⟨slot.val-4,ho⟩,hd⟩)).val
      else 0
    else 0
  else 0

def bodyNumberingMeaning {bound : ℕ} (order slot : Fin (bound+1)) : ℕ :=
  if hs : slot.val<order.val then (Fintype.equivFin (Fin order.val) ⟨slot.val,hs⟩).val else 0

/-- For fixed order there is a finite vector of numeral data implementing
all numbering choices in the literal pending expansion, exactly. -/
theorem fixedOrderNumberingCode_exists (bound : ℕ) :
    ∃ code : FixedOrderNumberingCode bound,
      (∀ order point mask slot,code.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot) ∧
      (∀ order slot,code.bodyLookup order slot=bodyNumberingMeaning order slot) := by
  let code : FixedOrderNumberingCode bound := {
    primary := Vector.ofFn (fun index =>
      let query := (pendingNumberingIndex bound).symm index
      pendingNumberingMeaning query.1 query.2.1 query.2.2.1 query.2.2.2)
    body := Vector.ofFn (fun index =>
      let query := (finProdFinEquiv : Fin (bound+1) × Fin (bound+1) ≃ Fin ((bound+1)*(bound+1))).symm index
      bodyNumberingMeaning query.1 query.2) }
  refine ⟨code,?_,?_⟩
  · intro order point mask slot
    simp only [FixedOrderNumberingCode.primaryLookup,code,Vector.get_ofFn,Equiv.symm_apply_apply]
  · intro order slot
    simp only [FixedOrderNumberingCode.bodyLookup,code,Vector.get_ofFn,Equiv.symm_apply_apply]

/-- Old primary coordinates use their original index plus four in the
stored query, and are not confused with newly introduced outputs. -/
theorem pendingNumberingMeaning_old {bound : ℕ} (order point : Fin (bound+1)) (hp : point.val<order.val)
    (mask : Fin 16) (old : {other : Fin order.val // other≠⟨point.val,hp⟩}) :
    pendingNumberingMeaning order point mask ⟨old.val.val+4,by omega⟩=
      (Fintype.equivFin (pendingMask mask ⊕ {other : Fin order.val // other≠⟨point.val,hp⟩}) (Sum.inr old)).val := by
  simp only [pendingNumberingMeaning,dif_pos hp]
  simp only [show ¬old.val.val+4<4 by omega,dite_false,Nat.add_sub_cancel]
  simp only [dif_pos old.val.isLt,dif_pos old.property]

/-- The new-output query is simply its original four-slot index. -/
theorem pendingNumberingMeaning_new {bound : ℕ} (order point : Fin (bound+1)) (hp : point.val<order.val)
    (mask : Fin 16) (new : pendingMask mask) :
    pendingNumberingMeaning order point mask ⟨new.val.val,by omega⟩=
      (Fintype.equivFin (pendingMask mask ⊕ {other : Fin order.val // other≠⟨point.val,hp⟩}) (Sum.inl new)).val := by
  simp only [pendingNumberingMeaning,dif_pos hp,dif_pos new.val.isLt,dif_pos new.property]

theorem bodyNumberingMeaning_exact {bound : ℕ} (order : Fin (bound+1)) (slot : Fin order.val) :
    bodyNumberingMeaning order ⟨slot.val,by omega⟩=(Fintype.equivFin (Fin order.val) slot).val := by
  simp only [bodyNumberingMeaning,dif_pos slot.isLt]

/-- Instantiation with the original pending operator: the runtime lookup
reproduces its exact old-coordinate embedding, not an arbitrary substitute
permutation. All model parameters occur only in the theorem's semantic side. -/
theorem FixedOrderNumberingCode.pendingHigherOldEmbedding {bound : ℕ}
    (code : FixedOrderNumberingCode bound)
    (hcode : ∀ order point mask slot,code.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → V7Calibration.PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (horder : seed.primaryOrder ≤ bound)
    (point : Fin seed.primaryOrder) (mask : Fin 16)
    (old : {other : Fin seed.primaryOrder // other≠point}) :
    code.primaryLookup ⟨seed.primaryOrder,by omega⟩ ⟨point.val,by omega⟩ mask ⟨old.val.val+4,by omega⟩=
      (V7Calibration.pendingHigherOldEmbedding C n beta operator charts seed point (pendingMask mask) old).val := by
  rw [hcode]
  exact pendingNumberingMeaning_old ⟨seed.primaryOrder,by omega⟩ ⟨point.val,by omega⟩ point.isLt mask old

/-- The stored tables have constant finite size for each fixed order. -/
theorem FixedOrderNumberingCode.storage {bound : ℕ} (code : FixedOrderNumberingCode bound) :
    code.primary.toList.length+code.body.toList.length=(bound+1)^2*(16*(bound+4)+1) := by
  simp only [Vector.length_toList]
  ring

end
end AFT.RationalNumerics

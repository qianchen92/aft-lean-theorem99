import AFT.PhysicalChartLinear

/-! # An explicit integer basis in the actual V7 dimension -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {R : Type*} [CommRing R]

/-- Relabeling preserves the literal zero-sum submodule. -/
def coordinateZeroSumCongr {First Second : Type*} [Fintype First] [Fintype Second]
    (equiv : First ≃ Second) : coordinateZeroSum First R ≃ₗ[R] coordinateZeroSum Second R where
  toFun word := ⟨fun index => word.val (equiv.symm index),by
    change (∑ index,word.val (equiv.symm index))=0
    rw [equiv.symm.sum_comp]
    exact word.property⟩
  invFun word := ⟨fun index => word.val (equiv index),by
    change (∑ index,word.val (equiv index))=0
    rw [equiv.sum_comp]
    exact word.property⟩
  left_inv := by intro word; apply Subtype.ext; funext index; simp
  right_inv := by intro word; apply Subtype.ext; funext index; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The body path basis is transported to the actual public block indices. -/
def actualBodyRootBasis (n : ℕ) :
    (Fin (Parameters.bodies n-1) → ℤ) ≃ₗ[ℤ] coordinateZeroSum (blockIndex n) ℤ := by
  let e : Fin (Parameters.bodies n-1+1) ≃ blockIndex n :=
    (finCongr (Nat.sub_add_cancel (Parameters.bodies_positive n))).trans (actualRootIndex n).symm
  let path : (Fin (Parameters.bodies n-1) → ℤ) ≃ₗ[ℤ]
      coordinateZeroSum (Fin (Parameters.bodies n-1+1)) ℤ := pathBasis (Parameters.bodies n-1)
  exact path.trans (coordinateZeroSumCongr e)

abbrev PhysicalEdgeIndex (n : ℕ) :=
  (Fin (Parameters.legs n) × Fin 2) ⊕ Fin (Parameters.bodies n-1)

theorem physicalEdgeIndex_card (n : ℕ) : Fintype.card (PhysicalEdgeIndex n)=Parameters.dimension n-1 := by
  have hb := Parameters.bodies_positive n
  have hd := Parameters.population_identity n
  simp only [PhysicalEdgeIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

def physicalEdgeIndexEquiv (n : ℕ) : PhysicalEdgeIndex n ≃ Fin (Parameters.dimension n-1) :=
  (blockEdgeNumbering (Parameters.legs n) (Parameters.bodies n-1)).trans (finCongr (by
    have hb := Parameters.bodies_positive n
    have hd := Parameters.population_identity n
    omega))

/-- The two dependent slot families have identical branches; this equivalence
keeps those branches explicit rather than casting the whole function type. -/
def physicalVertexSlotEquiv (n : ℕ) : Sigma (blockSlots n) ≃
    (Sigma (blockSlotsProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n))) where
  toFun point := match point with
    | ⟨.inl leg,slot⟩ => ⟨.inl leg,slot⟩
    | ⟨.inr body,slot⟩ => ⟨.inr body,slot⟩
  invFun point := match point with
    | ⟨.inl leg,slot⟩ => ⟨.inl leg,slot⟩
    | ⟨.inr body,slot⟩ => ⟨.inr body,slot⟩
  left_inv point := by rcases point with ⟨leg|body,slot⟩ <;> rfl
  right_inv point := by rcases point with ⟨leg|body,slot⟩ <;> rfl

def physicalVertexEquiv (n : ℕ) : Sigma (blockSlots n) ≃ Fin (Parameters.dimension n-1+1) :=
  (physicalVertexSlotEquiv n).trans
    ((blockVertexNumbering (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)).trans (finCongr (show Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1 from by
      have hl := Parameters.legs_le_half_bodies n
      have hb := Parameters.bodies_positive n
      have hd := Parameters.population_identity n
      omega)))

/-- Two scalar edge coordinates per leg, with a completely explicit inverse. -/
def physicalEdgePairEquiv (n : ℕ) :
    ((Fin (Parameters.legs n) × Fin 2) → R) ≃ₗ[R] (Fin (Parameters.legs n) → R × R) where
  toFun word leg := (word (leg,0),word (leg,1))
  invFun word index := ![(word index.1).1,(word index.1).2] index.2
  left_inv := by
    intro word
    funext index
    rcases index with ⟨leg,slot⟩
    fin_cases slot <;> rfl
  right_inv := by intro word; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def physicalEdgeCoordinates (n : ℕ) :
    (Fin (Parameters.dimension n-1) → R) ≃ₗ[R]
      ((Fin (Parameters.legs n) → R × R) × (Fin (Parameters.bodies n-1) → R)) :=
  (LinearEquiv.funCongrLeft R R (physicalEdgeIndexEquiv n)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (Parameters.legs n) × Fin 2)
      (Fin (Parameters.bodies n-1)) R R).trans
      (LinearEquiv.prodCongr (physicalEdgePairEquiv n) (LinearEquiv.refl _ _)))

/-- This is a proved integer basis for the actual physical loads. It is
constructed from the body path and the explicit two-edge leg incidence. -/
def actualPhysicalIncidenceBasis (n : ℕ) :
    (Fin (Parameters.dimension n-1) → ℤ) ≃ₗ[ℤ] zeroSumLattice (Parameters.dimension n-1) :=
  (physicalEdgeCoordinates n).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl _ _) (actualBodyRootBasis n)).trans
      ((physicalBlockIncidenceEquiv n).trans (coordinateZeroSumCongr (physicalVertexEquiv n))))

/-- The basis's output is the literal block incidence, in the fixed vertex
numbering used for rounding transport. -/
theorem actualPhysicalIncidenceBasis_apply (n : ℕ) (input : Fin (Parameters.dimension n-1) → ℤ)
    (coordinate : Sigma (blockSlots n)) :
    (actualPhysicalIncidenceBasis n input).val (physicalVertexEquiv n coordinate)=
      physicalBlockIncidence n (physicalEdgeCoordinates n input).1
        (actualBodyRootBasis n (physicalEdgeCoordinates n input).2) coordinate.1 coordinate.2 := by
  change physicalBlockIncidence n (physicalEdgeCoordinates n input).1
    (actualBodyRootBasis n (physicalEdgeCoordinates n input).2)
    ((physicalVertexEquiv n).symm (physicalVertexEquiv n coordinate)).1
    ((physicalVertexEquiv n).symm (physicalVertexEquiv n coordinate)).2=_
  rw [Equiv.symm_apply_apply]

end
end AFT.V7Calibration

import AFT.ActualIntegerBlockLoad
import AFT.Algebra

/-! # An explicit integral basis for the actual physical block coordinates -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Zero-sum vectors over any coefficient ring. The same formulas work over
integers and after reduction, so their inverses are not merely rational. -/
def coordinateZeroSum (Index R : Type*) [Fintype Index] [CommRing R] : Submodule R (Index → R) where
  carrier := {word | ∑ index,word index=0}
  zero_mem' := by simp
  add_mem' := by
    intro first second hf hs
    change ∑ index,first index=0 at hf
    change ∑ index,second index=0 at hs
    change (∑ index,(first index+second index))=0
    rw [Finset.sum_add_distrib,hf,hs,add_zero]
  smul_mem' := by
    intro scalar word hw
    change ∑ index,word index=0 at hw
    change (∑ index,scalar*word index)=0
    rw [← Finset.mul_sum,hw,mul_zero]

variable {R : Type*} [CommRing R]

/-- The two leg edges have loads x,-x-y,y at the tip, middle and body.
Their attached root shares precisely that body coordinate. -/
def physicalBlockIncidence (n : ℕ) (edge : Fin (Parameters.legs n) → R × R)
    (root : blockIndex n → R) : (index : blockIndex n) → blockSlots n index → R
  | .inl leg => ![(edge leg).1,-(edge leg).1-(edge leg).2,root (.inl leg)+(edge leg).2]
  | .inr body => ![root (.inr body)]

def physicalBlockRoot (n : ℕ) (load : Sigma (blockSlots n) → R) : blockIndex n → R :=
  fun index => ∑ slot,load ⟨index,slot⟩

def physicalBlockEdges (n : ℕ) (load : Sigma (blockSlots n) → R) : Fin (Parameters.legs n) → R × R :=
  fun leg => (load ⟨.inl leg,0⟩,-load ⟨.inl leg,0⟩-load ⟨.inl leg,1⟩)

theorem physicalBlockIncidence_root (n : ℕ) (edge : Fin (Parameters.legs n) → R × R)
    (root : blockIndex n → R) :
    physicalBlockRoot n (fun coordinate => physicalBlockIncidence n edge root coordinate.1 coordinate.2)=root := by
  funext index
  cases index with
  | inl leg => simp [physicalBlockRoot,physicalBlockIncidence,Fin.sum_univ_three]; ring
  | inr body => simp [physicalBlockRoot,physicalBlockIncidence]

theorem physicalBlockIncidence_sum (n : ℕ) (edge : Fin (Parameters.legs n) → R × R)
    (root : blockIndex n → R) :
    (∑ coordinate : Sigma (blockSlots n),physicalBlockIncidence n edge root coordinate.1 coordinate.2)=∑ index,root index := by
  rw [Fintype.sum_sigma]
  exact congrArg (fun word : blockIndex n → R => ∑ index,word index) (physicalBlockIncidence_root n edge root)

theorem physicalBlockIncidence_edges (n : ℕ) (edge : Fin (Parameters.legs n) → R × R)
    (root : blockIndex n → R) :
    physicalBlockEdges n (fun coordinate => physicalBlockIncidence n edge root coordinate.1 coordinate.2)=edge := by
  funext leg
  apply Prod.ext <;> simp [physicalBlockEdges,physicalBlockIncidence]

theorem physicalBlockIncidence_reconstruct (n : ℕ) (load : Sigma (blockSlots n) → R) :
    (fun coordinate : Sigma (blockSlots n) =>
      physicalBlockIncidence n (physicalBlockEdges n load) (physicalBlockRoot n load) coordinate.1 coordinate.2)=load := by
  funext coordinate
  rcases coordinate with ⟨index,slot⟩
  cases index with
  | inl leg =>
    change Fin 3 at slot
    fin_cases slot <;> simp [physicalBlockIncidence,physicalBlockEdges,physicalBlockRoot,Fin.sum_univ_three]
    all_goals ring
  | inr body =>
    change Fin 1 at slot
    fin_cases slot
    simp [physicalBlockIncidence,physicalBlockRoot]

/-- The actual physical block layout has an explicit integral incidence
basis. Its inverse sums a block and reads its two leg edges. -/
def physicalBlockIncidenceEquiv (n : ℕ) :
    ((Fin (Parameters.legs n) → R × R) × coordinateZeroSum (blockIndex n) R) ≃ₗ[R]
      coordinateZeroSum (Sigma (blockSlots n)) R where
  toFun point := ⟨fun coordinate => physicalBlockIncidence n point.1 point.2 coordinate.1 coordinate.2,
    (physicalBlockIncidence_sum n point.1 point.2).trans point.2.property⟩
  invFun load := (physicalBlockEdges n load,⟨physicalBlockRoot n load,by
    change (∑ index,∑ slot,load.val ⟨index,slot⟩)=0
    rw [← Fintype.sum_sigma]
    exact load.property⟩)
  left_inv := by
    intro point
    apply Prod.ext
    · exact physicalBlockIncidence_edges n point.1 point.2
    · apply Subtype.ext
      exact physicalBlockIncidence_root n point.1 point.2
  right_inv := by
    intro load
    apply Subtype.ext
    exact physicalBlockIncidence_reconstruct n load.val
  map_add' := by
    intro first second
    apply Subtype.ext
    funext coordinate
    rcases coordinate with ⟨index,slot⟩
    cases index with
    | inl leg =>
      change Fin 3 at slot
      fin_cases slot <;> simp [physicalBlockIncidence] <;> ring
    | inr body =>
      change Fin 1 at slot
      fin_cases slot
      rfl
  map_smul' := by
    intro scalar point
    apply Subtype.ext
    funext coordinate
    rcases coordinate with ⟨index,slot⟩
    cases index with
    | inl leg =>
      change Fin 3 at slot
      fin_cases slot <;> simp [physicalBlockIncidence,smul_eq_mul] <;> ring
    | inr body =>
      change Fin 1 at slot
      fin_cases slot
      rfl

end
end AFT.V7Calibration

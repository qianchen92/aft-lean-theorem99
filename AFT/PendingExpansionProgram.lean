import AFT.PendingKernelSyntax
import AFT.OrderedSeedExpansion

/-! # An executable pending expansion for the actual nonlinear numerator -/
namespace AFT.RationalNumerics

/-- The eleven output masks of degree at least two, in numeric order. -/
def pendingHigherMasks : List (Fin 16) :=
  (List.finRange 16).filter (fun mask => 2≤(pendingMask mask).card)

theorem pendingHigherMasks_length : pendingHigherMasks.length=11 := by decide

theorem pendingHigherMasks_nodup : pendingHigherMasks.Nodup := by decide

theorem pendingHigherMasks_selected_nodup : (pendingHigherMasks.map pendingMask).Nodup := by decide

theorem pendingHigherMasks_selected_set :
    (pendingHigherMasks.map pendingMask).toFinset=(Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card) := by decide

structure PendingProgramState (Leaf : Type*) where
  kernel : PendingKernelCode Leaf
  pending : Finset ℕ

def initialPendingProgramState {Leaf : Type*} (leafShape : Leaf → KernelShape) (code : PendingKernelCode Leaf) :
    PendingProgramState Leaf := ⟨code,Finset.range (code.shape leafShape).primary⟩

def pendingProgramLinear {Leaf : Type*} (state : PendingProgramState Leaf) : PendingProgramState Leaf :=
  if h : state.pending.Nonempty then ⟨state.kernel,state.pending.erase (state.pending.min' h)⟩ else state

def pendingProgramChoices {Leaf : Type*} (state : PendingProgramState Leaf) : List (Fin 16) :=
  if state.pending.Nonempty then pendingHigherMasks else []

def pendingProgramHigher {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (state : PendingProgramState Leaf) (mask : Fin 16) : PendingProgramState Leaf :=
  if h : state.pending.Nonempty then
    let point := state.pending.min' h
    let old := state.kernel.shape leafShape
    if hb : old.primary≤bound ∧ point<old.primary then
      ⟨.higher state.kernel point mask,(state.pending.erase point).image (fun other =>
        if ho : other<old.primary then numbering.primaryLookup
          ⟨old.primary,by omega⟩ ⟨point,by omega⟩ mask ⟨other+4,by omega⟩ else 0)⟩
    else state
  else state

def independentNumeratorFactors {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (code : PendingKernelCode Leaf) : OrderedSeedTable (PendingKernelCode Leaf) :=
  orderedSeedExpansion PendingProgramState.kernel pendingProgramLinear pendingProgramChoices
    (pendingProgramHigher numbering leafShape) (code.shape leafShape).primary (initialPendingProgramState leafShape code)

theorem independentNumeratorFactors_length {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (code : PendingKernelCode Leaf) :
    (independentNumeratorFactors numbering leafShape code).length≤12^(code.shape leafShape).primary := by
  apply orderedSeedExpansion_length _ _ _ _ 11
  intro state
  unfold pendingProgramChoices
  split_ifs <;> simp only [pendingHigherMasks_length,List.length_nil,le_refl,Nat.zero_le]

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance pendingExpansionProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Semantic restriction of the stored natural indices to the true seed.
Every executable index is validated separately by the finite invariant. -/
def PendingProgramState.denote {Leaf : Type*} (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (state : PendingProgramState Leaf) :
    PendingInput (Fin (Parameters.modulus n)) where
  seed := state.kernel.denote C n beta operator charts decode
  pending := Finset.univ.filter (fun point => point.val∈state.pending)

/-- The potential also reserves the three possible extra primary slots
created by each remaining old primary; it is constant for fixed order. -/
def PendingProgramState.Valid {Leaf : Type*} (bound : ℕ) (leafShape : Leaf → KernelShape)
    (state : PendingProgramState Leaf) : Prop :=
  state.kernel.Valid bound leafShape ∧
    (∀ point∈state.pending,point<(state.kernel.shape leafShape).primary) ∧
    (state.kernel.shape leafShape).primary+3*state.pending.card≤bound

theorem initialPendingProgramState_valid {Leaf : Type*} {bound : ℕ} (leafShape : Leaf → KernelShape)
    (code : PendingKernelCode Leaf) (hc : code.Valid bound leafShape)
    (hbound : 4*(code.shape leafShape).primary≤bound) :
    (initialPendingProgramState leafShape code).Valid bound leafShape := by
  refine ⟨hc,?_,?_⟩
  · intro point hp
    exact Finset.mem_range.mp hp
  · simpa only [initialPendingProgramState,Finset.card_range,show ∀ a : ℕ,a+3*a=4*a by intro a;omega] using hbound

end
end AFT.RationalNumerics

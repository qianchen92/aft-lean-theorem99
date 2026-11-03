import AFT.StoredPendingHigher

/-! # Finite syntax for the literal independent nonlinear kernel replacements -/
namespace AFT.RationalNumerics

structure KernelShape where
  primary : ℕ
  body : ℕ
  deriving DecidableEq

inductive PendingKernelCode (Leaf : Type*) where
  | leaf : Leaf → PendingKernelCode Leaf
  | higher : PendingKernelCode Leaf → ℕ → Fin 16 → PendingKernelCode Leaf

def PendingKernelCode.shape {Leaf : Type*} (leafShape : Leaf → KernelShape) : PendingKernelCode Leaf → KernelShape
  | .leaf label => leafShape label
  | .higher previous point mask =>
      let old := previous.shape leafShape
      if point<old.primary then ⟨(pendingMask mask).card+(old.primary-1),old.body⟩ else old

def PendingKernelCode.depth {Leaf : Type*} : PendingKernelCode Leaf → ℕ
  | .leaf _ => 0
  | .higher previous _ _ => previous.depth+1

def extendKernelWord {colors order : ℕ} (fallback : Fin colors) (word : Fin order → Fin colors) : ℕ → Fin colors :=
  fun index => if h : index<order then word ⟨index,h⟩ else fallback

/-- The only iteration depending on the palette is a finite sum in the
already proved local column program. The recursion depth is the syntax depth. -/
def PendingKernelCode.run {Leaf : Type*} {bound colors : ℕ} (numbering : FixedOrderNumberingCode bound)
    (constant n : ℕ) (beta : ℚ) (fallback : Fin colors)
    (leafShape : Leaf → KernelShape) (leafValue : Leaf → (ℕ → Fin colors) → ℚ) :
    PendingKernelCode Leaf → (ℕ → Fin colors) → ℚ
  | .leaf label,word => leafValue label word
  | .higher previous point mask,word =>
      let old := previous.shape leafShape
      if h : old.primary≤bound ∧ old.body≤bound ∧ point<old.primary then
        pendingHigherProgram numbering constant n beta old.primary old.body h.1 h.2.1 ⟨point,h.2.2⟩ mask
          (fun oldWord => previous.run numbering constant n beta fallback leafShape leafValue
            (extendKernelWord fallback oldWord)) word
      else previous.run numbering constant n beta fallback leafShape leafValue word

/-- The fixed-order validity condition is a finite syntactic predicate. -/
def PendingKernelCode.Valid {Leaf : Type*} (bound : ℕ) (leafShape : Leaf → KernelShape) : PendingKernelCode Leaf → Prop
  | .leaf label => (leafShape label).primary≤bound ∧ (leafShape label).body≤bound
  | .higher previous point mask => previous.Valid bound leafShape ∧
      point<(previous.shape leafShape).primary ∧
      (pendingMask mask).card+((previous.shape leafShape).primary-1)≤bound

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance pendingKernelSyntaxFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def PendingKernelCode.denote {Leaf : Type*} (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) :
    PendingKernelCode Leaf → InputSeed (Fin (Parameters.modulus n))
  | .leaf label => decode label
  | .higher previous point mask =>
      let old := previous.denote C n beta operator charts decode
      if h : point<old.primaryOrder then pendingPrimaryHigherSeed C n beta operator charts old ⟨point,h⟩ (pendingMask mask)
      else old

theorem pendingPrimaryHigherSeed_shape (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (point : Fin seed.primaryOrder) (selected : Finset (Fin 4)) :
    (pendingPrimaryHigherSeed C n beta operator charts seed point selected).primaryOrder=selected.card+(seed.primaryOrder-1) ∧
      (pendingPrimaryHigherSeed C n beta operator charts seed point selected).bodyOrder=seed.bodyOrder := by
  have hh := Fintype.card_congr (primarySplitEquiv point)
  simp only [Fintype.card_sum,Fintype.card_unique,Fintype.card_fin] at hh
  constructor
  · change Fintype.card (selected ⊕ {other : Fin seed.primaryOrder // other≠point})=selected.card+(seed.primaryOrder-1)
    simp only [Fintype.card_sum,Fintype.card_coe]
    omega
  · exact Fintype.card_fin seed.bodyOrder

theorem PendingKernelCode.denote_shape {Leaf : Type*} (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)
    (code : PendingKernelCode Leaf) :
    (code.denote C n beta operator charts decode).primaryOrder=(code.shape leafShape).primary ∧
      (code.denote C n beta operator charts decode).bodyOrder=(code.shape leafShape).body := by
  induction code with
  | leaf leaf => exact hshape leaf
  | higher previous point mask ih =>
    dsimp only [denote,shape]
    by_cases hp : point<(previous.denote C n beta operator charts decode).primaryOrder
    · have hp' : point<(previous.shape leafShape).primary := by simpa only [ih.1] using hp
      simp only [dif_pos hp,if_pos hp']
      have hh := pendingPrimaryHigherSeed_shape C n beta operator charts
        (previous.denote C n beta operator charts decode) ⟨point,hp⟩ (pendingMask mask)
      exact ⟨hh.1.trans (congrArg (fun order => (pendingMask mask).card+(order-1)) ih.1),hh.2.trans ih.2⟩
    · have hp' : ¬point<(previous.shape leafShape).primary := by simpa only [ih.1] using hp
      simp only [dif_neg hp,if_neg hp']
      exact ih

theorem PendingKernelCode.Valid.shape_bound {Leaf : Type*} {bound : ℕ} {leafShape : Leaf → KernelShape}
    {code : PendingKernelCode Leaf} (hcode : code.Valid bound leafShape) :
    (code.shape leafShape).primary≤bound ∧ (code.shape leafShape).body≤bound := by
  induction code with
  | leaf leaf => exact hcode
  | higher previous point mask ih =>
    have hp := hcode.2.1
    simp only [shape,if_pos hp]
    exact ⟨hcode.2.2,(ih hcode.1).2⟩

end
end AFT.RationalNumerics

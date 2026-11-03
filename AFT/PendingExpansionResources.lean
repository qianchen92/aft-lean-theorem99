import AFT.PendingSubsetProgram
import AFT.OrderedIndependentColumn

/-! # Every emitted pending code has fixed depth and valid finite indices -/
namespace AFT.RationalNumerics

theorem orderedSeedExpansion_member_invariant {State Branch Code : Type*}
    (base : State → Code) (linear : State → State) (choices : State → List Branch) (higher : State → Branch → State)
    (valid : State → Prop) (measure : State → ℕ)
    (hlinear : ∀ state,valid state → valid (linear state) ∧ measure (linear state) ≤ measure state+1)
    (hhigher : ∀ state,valid state → ∀ branch∈choices state,
      valid (higher state branch) ∧ measure (higher state branch) ≤ measure state+1)
    (steps : ℕ) (state : State) (hs : valid state)
    (term : OrderedSeedTerm Code) (ht : term∈orderedSeedExpansion base linear choices higher steps state) :
    ∃ finalState,valid finalState ∧ term=⟨1,[base finalState]⟩ ∧ measure finalState ≤ measure state+steps := by
  induction steps generalizing state with
  | zero =>
    simp only [orderedSeedExpansion,List.mem_cons,List.not_mem_nil,or_false] at ht
    subst term
    exact ⟨state,hs,rfl,by omega⟩
  | succ steps ih =>
    simp only [orderedSeedExpansion,List.mem_append,List.mem_flatMap] at ht
    rcases ht with ht|⟨branch,hbranch,ht⟩
    · obtain ⟨result,hresult,heq,hmeasure⟩ := ih (linear state) (hlinear state hs).1 ht
      exact ⟨result,hresult,heq,by have hh := (hlinear state hs).2;omega⟩
    · obtain ⟨result,hresult,heq,hmeasure⟩ := ih (higher state branch) (hhigher state hs branch hbranch).1 ht
      exact ⟨result,hresult,heq,by have hh := (hhigher state hs branch hbranch).2;omega⟩

theorem pendingProgramLinear_depth {Leaf : Type*} (state : PendingProgramState Leaf) :
    (pendingProgramLinear state).kernel.depth=state.kernel.depth := by
  unfold pendingProgramLinear
  split <;> rfl

theorem pendingProgramHigher_depth {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (shape : Leaf → KernelShape) (state : PendingProgramState Leaf) (mask : Fin 16) :
    (pendingProgramHigher numbering shape state mask).kernel.depth ≤ state.kernel.depth+1 := by
  unfold pendingProgramHigher
  split
  · dsimp only
    split
    · exact le_refl _
    · exact Nat.le_succ _
  · exact Nat.le_succ _

noncomputable section
open scoped BigOperators Classical
open V7Calibration
set_option backward.isDefEq.respectTransparency false
variable {Leaf : Type*} {bound : ℕ}

theorem pendingExpansion_valid_depth (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (shape : Leaf → KernelShape) (state : PendingProgramState Leaf) (hs : state.Valid bound shape)
    (steps : ℕ) (term : OrderedSeedTerm (PendingKernelCode Leaf))
    (ht : term∈orderedSeedExpansion PendingProgramState.kernel pendingProgramLinear pendingProgramChoices
      (pendingProgramHigher numbering shape) steps state) :
    ∃ code,term=⟨1,[code]⟩ ∧ code.Valid bound shape ∧ code.depth ≤ state.kernel.depth+steps := by
  obtain ⟨finalState,hvalid,heq,hdepth⟩ := orderedSeedExpansion_member_invariant
    PendingProgramState.kernel pendingProgramLinear pendingProgramChoices (pendingProgramHigher numbering shape)
    (PendingProgramState.Valid bound shape) (fun item => item.kernel.depth)
    (fun item hi => ⟨pendingProgramLinear_valid hi,(pendingProgramLinear_depth item).le.trans (Nat.le_succ _)⟩)
    (fun item hi mask _ => ⟨pendingProgramHigher_valid numbering hnumbering hi mask,pendingProgramHigher_depth numbering shape item mask⟩)
    steps state hs term ht
  exact ⟨finalState.kernel,heq,hvalid.1,hdepth⟩

theorem independentNumeratorFactors_valid_depth (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (shape : Leaf → KernelShape) (initial : PendingKernelCode Leaf) (hi : initial.Valid bound shape)
    (hp : 4*(initial.shape shape).primary ≤ bound)
    (term : OrderedSeedTerm (PendingKernelCode Leaf)) (ht : term∈independentNumeratorFactors numbering shape initial) :
    ∃ code,term=⟨1,[code]⟩ ∧ code.Valid bound shape ∧ code.depth ≤ initial.depth+(initial.shape shape).primary := by
  exact pendingExpansion_valid_depth numbering hnumbering shape (initialPendingProgramState shape initial)
    (initialPendingProgramState_valid shape initial hi hp) _ term ht

/-- For a fixed input order, the complete literal quotient has a fixed
finite number of terms, independently of the public modulus and kernels. -/
theorem independentQuotientFactors_length (numbering : FixedOrderNumberingCode bound)
    (shape : Leaf → KernelShape) (code : PendingKernelCode Leaf) (depth : ℕ) :
    (independentQuotientFactors numbering shape code depth).length ≤
      12^(code.shape shape).primary *
        (∑ count∈Finset.range (depth+1),15^count)^(code.shape shape).primary *
          (depth+1)^(code.shape shape).body := by
  simp only [independentQuotientFactors,OrderedSeedTable.multiply_length,OrderedSeedTable.power_length,
    OrderedSeedTable.relabel_length,actualPairedReciprocalFactors_length,actualBodyReciprocalFactors,
    List.length_map,List.length_range]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (independentNumeratorFactors_length numbering shape code))

theorem orderedIndependentColumnFactors_length (numbering : FixedOrderNumberingCode bound)
    (shape : Leaf → KernelShape) (factors : List Leaf) (depth : ℕ) :
    (orderedIndependentColumnFactors numbering shape factors depth).length ≤
      12^(orderedJointShape shape factors).primary *
        (∑ count∈Finset.range (depth+1),15^count)^(orderedJointShape shape factors).primary *
          (depth+1)^(orderedJointShape shape factors).body+1 := by
  simp only [orderedIndependentColumnFactors,List.length_append,List.length_cons,List.length_nil]
  exact Nat.add_le_add_right (independentQuotientFactors_length numbering (orderedJointShape shape) (.leaf factors) depth) 1

end
end AFT.RationalNumerics

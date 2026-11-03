import AFT.CountedGaussianArithmetic
import AFT.PendingKernelSyntax
import AFT.KernelPolynomialMonomial

/-! # Executable concatenation of ordered joint input factors

Only finite sums of sizes and explicit `Fin` sum equivalences occur in the
runtime coordinate map. No enumeration of real-valued seed labels is used.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

def KernelShape.join (first second : KernelShape) : KernelShape :=
  ⟨first.primary+second.primary,first.body+second.body⟩

def joinedKernelIndex (first second : KernelShape) :
    Fin (first.primary+first.body) ⊕ Fin (second.primary+second.body) ≃
      Fin ((first.join second).primary+(first.join second).body) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    ((Equiv.sumSumSumComm (Fin first.primary) (Fin first.body) (Fin second.primary) (Fin second.body)).trans
      ((Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv))

def orderedJointShape {Leaf : Type*} (shape : Leaf → KernelShape) : List Leaf → KernelShape
  | [] => ⟨0,0⟩
  | label::rest => (shape label).join (orderedJointShape shape rest)

def orderedJointKernel {Leaf Color Value : Type*} [One Value] [Mul Value]
    (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → Value) :
    (factors : List Leaf) → (Fin ((orderedJointShape shape factors).primary+(orderedJointShape shape factors).body) → Color) → Value
  | [],_ => 1
  | label::rest,word =>
      value label (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inl slot)))*
      orderedJointKernel shape value rest (fun slot => word
        (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inr slot)))

def orderedJointNaturalValue {Leaf Color Value : Type*} [One Value] [Mul Value]
    (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → Value)
    (factors : List Leaf) (word : ℕ → Color) : Value :=
  orderedJointKernel shape value factors (fun slot => word slot.val)

def countedOrderedJointKernel {Leaf Color : Type*} (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → GaussianArithmetic) :
    (factors : List Leaf) → (Fin ((orderedJointShape shape factors).primary+(orderedJointShape shape factors).body) → Color) → GaussianArithmetic
  | [],_ => .literal 1
  | label::rest,word =>
      (value label (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inl slot)))).mul
      (countedOrderedJointKernel shape value rest (fun slot => word
        (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inr slot))))

theorem countedOrderedJointKernel_value {Leaf Color : Type*} (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → GaussianArithmetic)
    (factors : List Leaf) (word) :
    (countedOrderedJointKernel shape value factors word).value=
      orderedJointKernel shape (fun label word => (value label word).value) factors word := by
  induction factors with
  | nil => rfl
  | cons label rest ih => simp only [countedOrderedJointKernel,GaussianArithmetic.mul,orderedJointKernel,ih]

theorem countedOrderedJointKernel_work {Leaf Color : Type*} (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → GaussianArithmetic)
    (factors : List Leaf) (work : ℕ)
    (hv : ∀ label∈factors,∀ word,(value label word).work≤work) (word) :
    (countedOrderedJointKernel shape value factors word).work≤factors.length*(work+1) := by
  induction factors with
  | nil => simp [countedOrderedJointKernel,GaussianArithmetic.literal]
  | cons label rest ih =>
    simp only [countedOrderedJointKernel,GaussianArithmetic.mul,List.length_cons]
    have hh := hv label (List.mem_cons_self ..) (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inl slot)))
    have ht := ih (fun other ho => hv other (List.mem_cons_of_mem _ ho))
      (fun slot => word (joinedKernelIndex (shape label) (orderedJointShape shape rest) (Sum.inr slot)))
    nlinarith

open RepresentedPolynomial
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Color Output Leaf : Type*} [Fintype Color]

def shapeSeed (shape : KernelShape) (kernel : (Fin (shape.primary+shape.body) → Color) → ℝ) : InputSeed Color :=
  ⟨shape.primary,shape.body,kernel⟩

def orderedJointSeed (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (factors : List Leaf) : InputSeed Color :=
  shapeSeed (orderedJointShape shape factors) (orderedJointKernel shape value factors)

omit [Fintype Color] in
theorem joinedKernelIndex_forms (first second : KernelShape) (primary body : Color → Table Output) :
    (fun slot => Fin.addCases (fun _ : Fin (first.primary+second.primary) => primary)
      (fun _ : Fin (first.body+second.body) => body) (joinedKernelIndex first second slot))=
    Sum.elim (Fin.addCases (fun _ : Fin first.primary => primary) (fun _ : Fin first.body => body))
      (Fin.addCases (fun _ : Fin second.primary => primary) (fun _ : Fin second.body => body)) := by
  funext slot
  rcases slot with slot|slot
  · cases slot using Fin.addCases <;> simp [joinedKernelIndex,Equiv.sumSumSumComm,KernelShape.join]
  · cases slot using Fin.addCases <;> simp [joinedKernelIndex,Equiv.sumSumSumComm,KernelShape.join]

theorem orderedJointSeed_polynomial (shape : Leaf → KernelShape)
    (value : (label : Leaf) → (Fin ((shape label).primary+(shape label).body) → Color) → ℝ)
    (primary body : Color → Table Output) (factors : List Leaf) :
    inputKernelPolynomial primary body (orderedJointSeed shape value factors)=
      (factors.map (fun label => inputKernelPolynomial primary body (shapeSeed (shape label) (value label)))).prod := by
  induction factors with
  | nil => simp [orderedJointSeed,shapeSeed,orderedJointShape,orderedJointKernel,inputKernelPolynomial,kernelPolynomial]
  | cons label rest ih =>
    let first := shape label
    let second := orderedJointShape shape rest
    let kernel := MixedKernel.tensor (value label) (orderedJointKernel shape value rest)
    have he := kernelPolynomial_equiv (joinedKernelIndex first second).symm
      (Fin.addCases (fun _ : Fin (first.primary+second.primary) => primary)
        (fun _ : Fin (first.body+second.body) => body))
      (fun word => kernel (word ∘ joinedKernelIndex first second))
    have hk : (fun word => kernel ((word ∘ (joinedKernelIndex first second).symm) ∘ joinedKernelIndex first second))=kernel := by
      funext word
      congr 1
      funext slot
      exact congrArg word ((joinedKernelIndex first second).symm_apply_apply slot)
    simp only [Equiv.symm_symm,joinedKernelIndex_forms,hk] at he
    have hleft : inputKernelPolynomial primary body (orderedJointSeed shape value (label::rest))=
      kernelPolynomial
        (Fin.addCases (fun _ : Fin (first.primary+second.primary) => primary)
          (fun _ : Fin (first.body+second.body) => body))
        (fun word => kernel (word ∘ joinedKernelIndex first second)) := by
      unfold inputKernelPolynomial kernelPolynomial
      apply Finset.sum_congr (by ext word;simp)
      intro word _
      rfl
    rw [hleft,←he,kernelPolynomial_tensor]
    have hfirst : kernelPolynomial (Fin.addCases (fun _ : Fin first.primary => primary) (fun _ : Fin first.body => body))
        (value label)=inputKernelPolynomial primary body (shapeSeed (shape label) (value label)) := by
      unfold inputKernelPolynomial shapeSeed kernelPolynomial
      apply Finset.sum_congr (by ext word;simp)
      intro word _
      rfl
    have hsecond : kernelPolynomial (Fin.addCases (fun _ : Fin second.primary => primary) (fun _ : Fin second.body => body))
        (orderedJointKernel shape value rest)=inputKernelPolynomial primary body (orderedJointSeed shape value rest) := by
      unfold inputKernelPolynomial orderedJointSeed shapeSeed kernelPolynomial
      apply Finset.sum_congr (by ext word;simp)
      intro word _
      rfl
    rw [hfirst,hsecond,ih]
    rfl

end
end AFT.RationalNumerics

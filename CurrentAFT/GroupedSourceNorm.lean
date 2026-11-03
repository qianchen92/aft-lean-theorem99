import AFT.DependentTensorChannel
import AFT.PlacedFibers

/-!
# Exact regrouping of joint root and control inputs

The root density and the public control kernel remain joint functions.
Grouping each physical channel's roots with its one control is an exact
Hilbert isometry, including channels with two roots or no control.
-/
namespace CurrentAFT.GroupedSourceNorm
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Root : Type*} [Fintype Group] [Fintype Root]
  (RootSlots ControlInput : Group → Type*)
  [∀ group, Fintype (RootSlots group)] [∀ group, Fintype (ControlInput group)]

abbrev GroupWord := (group : Group) → ((RootSlots group → Root) × ControlInput group)
abbrev GlobalWord := (Sigma RootSlots → Root) × ((group : Group) → ControlInput group)

def wordEquiv : GlobalWord (Root := Root) RootSlots ControlInput ≃
    GroupWord (Root := Root) RootSlots ControlInput where
  toFun word group := (fun slot => word.1 ⟨group, slot⟩, word.2 group)
  invFun word := (fun slot => (word slot.fst).1 slot.snd, fun group => (word group).2)
  left_inv word := by cases word; rfl
  right_inv _ := rfl

def groupReference (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (group : Group) : FiniteDist ((RootSlots group → Root) × ControlInput group) :=
  (FiniteDist.independent (fun _ : RootSlots group => root)).prod (control group)

def globalReference (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group)) :
    FiniteDist (GlobalWord (Root := Root) RootSlots ControlInput) :=
  (FiniteDist.independent (fun _ : Sigma RootSlots => root)).prod (FiniteDist.dependentIndependent control)

/-- Fubini and coordinate regrouping preserve the entire squared norm. -/
theorem group_energy (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (input : GlobalWord (Root := Root) RootSlots ControlInput → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (input ∘ (wordEquiv RootSlots ControlInput).symm) =
        (globalReference RootSlots ControlInput root control).l2Sq input := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (wordEquiv RootSlots ControlInput).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Function.comp_apply, FiniteDist.dependentIndependent_weight,
    groupReference, globalReference, FiniteDist.prod_weight, FiniteDist.independent,
    wordEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Fintype.prod_sigma, Finset.prod_mul_distrib]

/-- Independence is used only between the whole root word and the whole
control word. Neither of their densities is required to factor. -/
theorem product_input_energy (root : FiniteDist Root)
    (control : (group : Group) → FiniteDist (ControlInput group))
    (rootDensity : (Sigma RootSlots → Root) → ℝ)
    (controlKernel : ((group : Group) → ControlInput group) → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (fun word => rootDensity (fun slot => (word slot.fst).1 slot.snd) * controlKernel (fun group => (word group).2)) =
      (FiniteDist.independent (fun _ : Sigma RootSlots => root)).l2Sq rootDensity *
        (FiniteDist.dependentIndependent control).l2Sq controlKernel := by
  change (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
    ((fun word : GlobalWord (Root := Root) RootSlots ControlInput => rootDensity word.1 * controlKernel word.2) ∘
      (wordEquiv RootSlots ControlInput).symm) = _
  rw [group_energy]
  simp only [globalReference, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.prod_weight,
    Fintype.sum_prod_type, mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro roots _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro controls _
  ring

/-- Unused independent root coordinates are integrated exactly. This
allows a selected group to retain both root slots even when just one is
tagged, with the original joint selected-root norm unchanged. -/
theorem embedded_product_input_energy {RootLabel : Type*} [Fintype RootLabel]
    (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (labels : RootLabel ↪ Sigma RootSlots) (rootDensity : (RootLabel → Root) → ℝ)
    (controlKernel : ((group : Group) → ControlInput group) → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (fun word => rootDensity (fun label => (word (labels label).fst).1 (labels label).snd) *
        controlKernel (fun group => (word group).2)) =
      (FiniteDist.independent (fun _ : RootLabel => root)).l2Sq rootDensity *
        (FiniteDist.dependentIndependent control).l2Sq controlKernel := by
  have h := product_input_energy RootSlots ControlInput root control
    (fun roots => rootDensity (roots ∘ labels)) controlKernel
  dsimp only [Function.comp_def] at h
  rw [h]
  apply congrArg (fun value => value * (FiniteDist.dependentIndependent control).l2Sq controlKernel)
  exact CanonicalMoments.independent_embedding_expectation root labels (fun roots => rootDensity roots ^ 2)

end
end CurrentAFT.GroupedSourceNorm

import CurrentAFT.GroupedSourceNorm

/-! # Exact coordinate updates before and after root/control grouping -/
namespace CurrentAFT.GroupedRootUpdates
open AFT GroupedSourceNorm
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Fiber : Index → Type*} :
    DecidableEq (Sigma Fiber) := Classical.decEq _

variable {Group Root : Type*} [DecidableEq Group] (Slots Control : Group → Type*)
  [∀ group, DecidableEq (Slots group)]

def roots (word : (group : Group) → (Slots group → Root) × Control group) : Sigma Slots → Root :=
  fun slot => (word slot.fst).1 slot.snd

def controls (word : (group : Group) → (Slots group → Root) × Control group) : (group : Group) → Control group :=
  fun group => (word group).2

def updateRoot (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :=
  Function.update word group (Function.update (word group).1 slot value, (word group).2)

theorem roots_updateRoot (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    roots Slots Control (updateRoot Slots Control word group slot value) =
      Function.update (roots Slots Control word) ⟨group, slot⟩ value := by
  funext point
  rcases point with ⟨other, point⟩
  by_cases hequal : other = group
  · subst other
    by_cases hslot : point = slot
    · subst point
      simp [roots, updateRoot]
    · simp [roots, updateRoot, hslot]
  · simp [roots, updateRoot, hequal]

theorem controls_updateRoot (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    controls Slots Control (updateRoot Slots Control word group slot value) = controls Slots Control word := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp [controls, updateRoot]
  · simp [controls, updateRoot, hequal]

theorem updateRoot_updated_group (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (sample : (Slots group → Root) × Control group) (slot : Slots group) (value : Root) :
    updateRoot Slots Control (Function.update word group sample) group slot value =
      Function.update word group (Function.update sample.1 slot value, sample.2) := by
  simp only [updateRoot, Function.update_self, Function.update_idem]

end
end CurrentAFT.GroupedRootUpdates

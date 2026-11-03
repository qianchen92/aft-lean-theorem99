import CurrentAFT.BinaryRootSignedMassResources
import CurrentAFT.RationalPackedRootProgram

/-! Stored role/root-slot metadata and executed accesses to one whole joint
base-q source word. No joint root/control input is factored. -/
namespace CurrentAFT.BinaryPackedRootMetadata
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open RationalRootGroupProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Color (security : ℕ) := Fin (PublicParameterProgram.modulus security).count

structure Data (r s kept tags : ℕ) where
  roles : Vector LocalRole ((r+s)+kept)
  tagged : Vector (Fin ((r+s)+kept) × Fin 2) tags


def Data.metadata {r s kept tags : ℕ} (data : Data r s kept tags) : RationalPackedRootProgram.Metadata r s kept tags :=
  ⟨data.roles.get,data.tagged.get⟩


def firstColor (security : ℕ) : Color security :=
  ⟨0, by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.pos⟩

def word {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) : Fin groups → Fin 3 → ℕ :=
  fun group slot => (source.get (finProdFinEquiv (group,slot))).val


def sourceEntry {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3))
    (group : Fin groups) (slot : Fin 3) : CountedValue (Color security) :=
  let base := multiplyCounter group.val 3
  let position := addCounter base.count slot.val
  let result := readVector (firstColor security) source ⟨position.count, by
    rw [addCounter_value,multiplyCounter_value];have := group.isLt;have := slot.isLt;omega⟩
  ⟨result.value,base.work+position.work+result.work+3⟩

 theorem sourceEntry_value {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3))
    (group : Fin groups) (slot : Fin 3) :
    (sourceEntry security source group slot).value = source.get (finProdFinEquiv (group,slot)) := by
  simp only [sourceEntry,readVector_value]
  apply congrArg source.get
  apply Fin.ext
  simp only [addCounter_value,multiplyCounter_value,finProdFinEquiv_apply_val]
  omega

 theorem sourceEntry_work {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3))
    (group : Fin groups) (slot : Fin 3) : (sourceEntry security source group slot).work ≤ 30*groups+20 := by
  have hb := multiplyCounter_work group.val 3
  have hp : (addCounter (multiplyCounter group.val 3).count slot.val).work = 6*group.val+1 := by
    rw [addCounter_work,multiplyCounter_value]
    omega
  have hr := readVector_work (firstColor security) source (⟨(addCounter (multiplyCounter group.val 3).count slot.val).count, by
    rw [addCounter_value,multiplyCounter_value];have := group.isLt;have := slot.isLt;omega⟩ : Fin (groups*3))
  have hg := group.isLt
  have hs := slot.isLt
  simp only [sourceEntry]
  omega


def taggedDefault {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (index : Fin tags) : Fin groups × Fin 2 :=
  (⟨0, by have := (positions.get index).1.isLt;omega⟩,0)


def absent {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (group : Fin groups) (slot : Fin 2) : CountedValue Bool :=
  BinaryProposalGuard.allFin tags (fun index =>
    let position := readVector (taggedDefault positions index) positions index
    let sameGroup := equalCounter position.value.1.val group.val
    let sameSlot := equalCounter position.value.2.val slot.val
    ⟨!(sameGroup.value && sameSlot.value),position.work+sameGroup.work+sameSlot.work+3⟩)

 theorem absent_value {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (group : Fin groups) (slot : Fin 2) :
    (absent positions group slot).value = true ↔ ¬∃ index, positions.get index = (group,slot) := by
  simp only [absent,BinaryProposalGuard.allFin_value,readVector_value,Bool.not_eq_true']
  constructor
  · intro h ⟨index,he⟩
    have hg := congrArg (fun pair : Fin groups × Fin 2 => pair.1.val) he
    have hs := congrArg (fun pair : Fin groups × Fin 2 => pair.2.val) he
    apply (Bool.eq_false_iff.mp (h index))
    simp only [Bool.and_eq_true]
    exact ⟨(equalCounter_value _ _).mpr hg,(equalCounter_value _ _).mpr hs⟩
  · intro h index
    apply Bool.eq_false_iff.mpr
    intro he
    have he' : (equalCounter (positions.get index).1.val group.val).value = true ∧
        (equalCounter (positions.get index).2.val slot.val).value = true := by
      simpa only [Bool.and_eq_true] using he
    apply h
    exact ⟨index,Prod.ext (Fin.ext ((equalCounter_value _ _).mp he'.1)) (Fin.ext ((equalCounter_value _ _).mp he'.2))⟩

 theorem absent_work {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (group : Fin groups) (slot : Fin 2) :
    (absent positions group slot).work ≤ tags*(3*tags+6*groups+34)+1 := by
  apply BinaryProposalGuard.allFin_work tags (3*tags+6*groups+32)
  intro index
  have hr := readVector_work (taggedDefault positions index) positions index
  have hg := equalCounter_work (readVector (taggedDefault positions index) positions index).value.1.val group.val
  have hs := equalCounter_work (readVector (taggedDefault positions index) positions index).value.2.val slot.val
  have h1 := (readVector (taggedDefault positions index) positions index).value.1.isLt
  have h2 := (readVector (taggedDefault positions index) positions index).value.2.isLt
  have h3 := group.isLt
  have h4 := slot.isLt
  change _+_+_+3 ≤ _
  omega


def active {r s kept tags : ℕ} (data : Data r s kept tags) (group : Fin ((r+s)+kept)) (slot : Fin 2) : CountedValue Bool :=
  let role := readVector LocalRole.primary data.roles group
  let first := equalCounter slot.val 0
  let missing := absent data.tagged group slot
  let isActive := match role.value with | .primary => true | _ => first.value
  ⟨isActive && missing.value,role.work+first.work+missing.work+3⟩

 theorem active_value {r s kept tags : ℕ} (data : Data r s kept tags) (group : Fin ((r+s)+kept)) (slot : Fin 2) :
    (active data group slot).value = true ↔
      RationalPackedRootProgram.rootActive (data.metadata.roles group) slot ∧ ¬∃ tag, data.metadata.taggedSlots tag = (group,slot) := by
  simp only [active,Bool.and_eq_true,readVector_value,absent_value,Data.metadata,RationalPackedRootProgram.rootActive]
  cases data.roles.get group <;> simp [equalCounter_value]

 theorem active_work {r s kept tags : ℕ} (data : Data r s kept tags) (group : Fin ((r+s)+kept)) (slot : Fin 2) :
    (active data group slot).work ≤ 3*((r+s)+kept)+tags*(3*tags+6*((r+s)+kept)+34)+20 := by
  have hr := readVector_work LocalRole.primary data.roles group
  have he := equalCounter_work slot.val 0
  have ha := absent_work data.tagged group slot
  have hs := slot.isLt
  change _+_+_+3 ≤ _
  omega

end CurrentAFT.BinaryPackedRootMetadata

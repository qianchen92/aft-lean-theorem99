import CurrentAFT.BinaryTouchedCycleBuffer

/-! The current/predecessor rank pair is materialized for every selected root
using the executed touched-edge lookup, before any Gaussian word is visited. -/
namespace CurrentAFT.BinaryTouchedCycleRanks
open AFT BinaryArithmetic RationalRejectionProgram BinaryTouchedCycle BinaryTouchedCycleBuffer
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def prepareWork (body count : ℕ) : ℕ :=
  count*(3*count+7*body+19)+3 + (2*count)*(2*count*(6*body+4)+3)+3

def bufferWork (body count : ℕ) : ℕ := prepareWork body count + (2*count)*(4*count+5)+4

 theorem buffer_work {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (buffer hb sites).work ≤ bufferWork body count := by
  have hp := prepare_work hb sites
  have hm := prepare_length hb sites
  have ha := storeData_work (prepare hb sites).value.length (2*(prepare hb sites).value.length+3)
    (fun index =>
      let selected := readList (prepare hb sites).value index.val
      (⟨selected.data.getD ⟨0,hb⟩,selected.work+2⟩ : CountedValue (Fin body))) (by
        intro index
        exact Nat.add_le_add_right (readList_work _ index.val) 2)
  have hbound : (prepare hb sites).value.length*(2*(prepare hb sites).value.length+3+2) ≤ (2*count)*(4*count+5) := by
    norm_num only [Nat.add_assoc]
    exact Nat.mul_le_mul hm (by omega)
  change (prepare hb sites).work+(storeData _ _).work+2 ≤ _
  unfold bufferWork prepareWork
  omega


def positions {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    CountedValue (Vector (Fin (prepare hb sites).value.length × Fin (prepare hb sites).value.length) count) :=
  let vertices := buffer hb sites
  let result := storeData count (fun slot =>
    let point := readVector ⟨0,hb⟩ sites slot
    let before := previous body hb point.value
    have hp : point.value ∈ vertices.value.toList := by
      rw [buffer_mem,readVector_value]
      exact (CyclePatternProgram.currentEdge sites.get slot).property
    have hb' : before.value ∈ vertices.value.toList := by
      rw [buffer_mem,previous_value,readVector_value]
      exact (CyclePatternProgram.previousEdge sites.get slot).property
    let first := lookup vertices.value (buffer_injective hb sites) point.value hp
    let second := lookup vertices.value (buffer_injective hb sites) before.value hb'
    ⟨(first.value,second.value),point.work+before.work+first.work+second.work+5⟩)
  ⟨result.value,vertices.work+result.work+2⟩

 theorem positions_value {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) (slot : Fin count) :
    (buffer hb sites).value.get ((positions hb sites).value.get slot).1 = sites.get slot ∧
    (buffer hb sites).value.get ((positions hb sites).value.get slot).2 = (finRotate body).symm (sites.get slot) := by
  simp only [positions,storeData_get,lookup_value,readVector_value,previous_value,and_self]


def positionsWork (body count : ℕ) : ℕ :=
  bufferWork body count + count*(3*count+7*body+2*((2*count)*(6*count+6*body+8)+3)+20)+4

 theorem positions_work {body count : ℕ} (hb : 0 < body) (sites : Vector (Fin body) count) :
    (positions hb sites).work ≤ positionsWork body count := by
  have hb' := buffer_work hb sites
  have hm := prepare_length hb sites
  have hlookup : (prepare hb sites).value.length*(3*(prepare hb sites).value.length+6*body+8)+3 ≤
      (2*count)*(6*count+6*body+8)+3 := by
    exact Nat.add_le_add_right (Nat.mul_le_mul hm (by omega)) 3
  let result := storeData count (fun slot =>
    let point := readVector (⟨0,hb⟩ : Fin body) sites slot
    let before := previous body hb point.value
    have hp : point.value ∈ (buffer hb sites).value.toList := by
      rw [buffer_mem,readVector_value]
      exact (CyclePatternProgram.currentEdge sites.get slot).property
    have hprev : before.value ∈ (buffer hb sites).value.toList := by
      rw [buffer_mem,previous_value,readVector_value]
      exact (CyclePatternProgram.previousEdge sites.get slot).property
    let first := lookup (buffer hb sites).value (buffer_injective hb sites) point.value hp
    let second := lookup (buffer hb sites).value (buffer_injective hb sites) before.value hprev
    (⟨(first.value,second.value),point.work+before.work+first.work+second.work+5⟩ : CountedValue _))
  have hr : result.work ≤ count*(3*count+7*body+2*((2*count)*(6*count+6*body+8)+3)+20)+2 := by
    apply storeData_work
    intro slot
    have hs := readVector_work (⟨0,hb⟩ : Fin body) sites slot
    have hp := previous_work body hb (readVector (⟨0,hb⟩ : Fin body) sites slot).value
    have hfirst := lookup_work (buffer hb sites).value (buffer_injective hb sites)
      (readVector (⟨0,hb⟩ : Fin body) sites slot).value (by
        rw [buffer_mem,readVector_value]
        exact (CyclePatternProgram.currentEdge sites.get slot).property)
    have hsecond := lookup_work (buffer hb sites).value (buffer_injective hb sites)
      (previous body hb (readVector (⟨0,hb⟩ : Fin body) sites slot).value).value (by
        rw [buffer_mem,previous_value,readVector_value]
        exact (CyclePatternProgram.previousEdge sites.get slot).property)
    change (readVector _ sites slot).work+(previous _ _ _).work+(lookup _ _ _ _).work+(lookup _ _ _ _).work+5 ≤ _
    omega
  change (buffer hb sites).work+result.work+2 ≤ _
  unfold positionsWork
  omega

end CurrentAFT.BinaryTouchedCycleRanks

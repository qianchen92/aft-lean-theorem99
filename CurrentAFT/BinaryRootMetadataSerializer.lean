import CurrentAFT.BinaryPackedRootMetadata
import CurrentAFT.RationalFullResponseProgram
import AFT.BinaryDataArrays
import AFT.BinaryLegalChart

/-! Bounded serialization of selected controls and sorted root tags.
The executed filter visits only the supplied tags; candidate root lookup
visits two slots per selected or retained group. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic RationalRejectionProgram RationalRootGroupProgram
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev population (legs ordinary queues : ℕ) := legs+(legs+ordinary)+queues

def primaryMissing {legs ordinary queues r : ℕ} (primary : Vector (Fin legs) r)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  BinaryProposalGuard.allFin r (fun index =>
    let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    let companion := addCounter legs found.value.val
    let legEqual := equalCounter block.val found.value.val
    let companionEqual := equalCounter block.val companion.count
    ⟨!(legEqual.value || companionEqual.value),found.work+companion.work+legEqual.work+companionEqual.work+4⟩)

def ordinaryMissing {legs ordinary queues s : ℕ} (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  BinaryProposalGuard.allFin s (fun index =>
    let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
    let twice := addCounter legs legs
    let position := addCounter twice.count found.value.val
    let same := equalCounter block.val position.count
    ⟨!same.value,found.work+twice.work+position.work+same.work+4⟩)

def isKept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) : CountedValue Bool :=
  let first := primaryMissing primary block
  let second := ordinaryMissing body block
  ⟨first.value && second.value,first.work+second.work+2⟩

theorem primaryMissing_value {legs ordinary queues r : ℕ} (primary : Vector (Fin legs) r)
    (block : Fin (population legs ordinary queues)) :
    (primaryMissing primary block).value=true ↔
      ∀ index,block.val≠(primary.get index).val ∧ block.val≠legs+(primary.get index).val := by
  simp only [primaryMissing,BinaryProposalGuard.allFin_value,readVector_value,addCounter_value,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Bool.or_eq_true,equalCounter_value,not_or]

theorem ordinaryMissing_value {legs ordinary queues s : ℕ} (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) :
    (ordinaryMissing body block).value=true ↔ ∀ index,block.val≠legs+legs+(body.get index).val := by
  simp only [ordinaryMissing,BinaryProposalGuard.allFin_value,readVector_value,addCounter_value,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equalCounter_value]

theorem isKept_value {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) :
    (isKept primary body block).value=true ↔
      (∀ index,block.val≠(primary.get index).val ∧ block.val≠legs+(primary.get index).val) ∧
        ∀ index,block.val≠legs+legs+(body.get index).val := by
  simp only [isKept,Bool.and_eq_true,primaryMissing_value,ordinaryMissing_value]

def filter {α : Type*} (test : α → CountedValue Bool) : List α → CountedValue (List α)
  | [] => ⟨[],1⟩
  | head::tail =>
    let checked := test head
    let rest := filter test tail
    ⟨if checked.value then head::rest.value else rest.value,checked.work+rest.work+3⟩

theorem filter_value {α : Type*} (test : α → CountedValue Bool) (items : List α) :
    (filter test items).value=items.filter (fun item => (test item).value) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [filter,List.filter_cons,ih]

theorem filter_work {α : Type*} (test : α → CountedValue Bool) (items : List α) (bound : ℕ)
    (h : ∀ item∈items,(test item).work ≤ bound) :
    (filter test items).work ≤ items.length*(bound+3)+1 := by
  induction items with
  | nil => simp only [filter,List.length_nil,Nat.zero_mul,Nat.zero_add];omega
  | cons head tail ih =>
    have ht := ih (fun item hi => h item (List.mem_cons_of_mem head hi))
    have hh := h head (List.mem_cons_self)
    simp only [filter,List.length_cons]
    nlinarith

def kept {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : CountedValue (List (Fin (population legs ordinary queues))) :=
  let computed := filter (isKept primary body) tagged.toList
  ⟨computed.value,computed.work+tags+1⟩

theorem kept_value {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    (kept primary body tagged).value=tagged.toList.filter (fun block => (isKept primary body block).value) := by
  exact filter_value _ _

theorem kept_length_le {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : (kept primary body tagged).value.length ≤ tags := by
  rw [kept_value]
  simpa only [Vector.length_toList] using List.length_filter_le (fun block => (isKept primary body block).value) tagged.toList

def groupCount {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) := (r+s)+(kept primary body tagged).value.length

theorem groupCount_pos {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) : 0<groupCount primary body tagged := by
  by_cases hrs : r+s=0
  · have hr : r=0 := by omega
    have hs : s=0 := by omega
    have hall : ∀ block : Fin (population legs ordinary queues),(isKept primary body block).value=true := by
      intro block
      apply (isKept_value primary body block).mpr
      constructor
      · intro i;have := i.isLt;omega
      · intro i;have := i.isLt;omega
    have hk : (kept primary body tagged).value=tagged.toList := by
      rw [kept_value]
      exact List.filter_eq_self.mpr (fun block _ => hall block)
    simp only [groupCount,hk,Vector.length_toList]
    have := index.isLt
    omega
  · unfold groupCount
    omega

def candidate {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) : CountedValue (Option ℕ) :=
  let first := lessCounter group.val r
  let second := lessCounter group.val (r+s)
  let zero := equalCounter slot.val 0
  if hp : first.value=true then
    let index : Fin r := ⟨group.val,(lessCounter_value _ _).mp hp⟩
    let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    let companion := addCounter legs found.value.val
    ⟨some (if zero.value then companion.count else found.value.val),first.work+second.work+zero.work+found.work+companion.work+5⟩
  else if hb : second.value=true then
    let position := differenceCounter group.val r
    let index : Fin s := ⟨position.count,by
      rw [differenceCounter_value]
      have ht := (lessCounter_value _ _).mp hb
      have hf : ¬group.val<r := fun h => hp ((lessCounter_value _ _).mpr h)
      omega⟩
    let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
    let twice := addCounter legs legs
    let value := addCounter twice.count found.value.val
    ⟨if zero.value then some value.count else none,
      first.work+second.work+zero.work+position.work+found.work+twice.work+value.work+7⟩
  else
    let position := differenceCounter group.val (r+s)
    let found := readList retained position.count
    ⟨if zero.value then found.data.map Fin.val else none,first.work+second.work+zero.work+position.work+found.work+5⟩

def role {legs ordinary queues r s : ℕ} (_primary : Vector (Fin legs) r) (_body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length)) : CountedValue LocalRole :=
  let first := lessCounter group.val r
  let second := lessCounter group.val (r+s)
  if first.value then ⟨.primary,first.work+second.work+2⟩ else
  if second.value then ⟨.ordinary,first.work+second.work+3⟩ else
    let position := differenceCounter group.val (r+s)
    let found := readList retained position.count
    let value := (found.data.map Fin.val).getD 0
    let leg := lessCounter value legs
    let centers := addCounter legs ordinary
    let boundary := addCounter legs centers.count
    let center := lessCounter value boundary.count
    ⟨if leg.value then .leg else if center.value then .center else .queue,
      first.work+second.work+position.work+found.work+leg.work+centers.work+boundary.work+center.work+9⟩

def find {α : Type*} (test : α → CountedValue Bool) : List α → CountedValue (Option α)
  | [] => ⟨none,1⟩
  | head::tail =>
    let checked := test head
    if checked.value then ⟨some head,checked.work+2⟩ else
      let rest := find test tail
      ⟨rest.value,checked.work+rest.work+3⟩

theorem find_value {α : Type*} (test : α → CountedValue Bool) (items : List α) :
    (find test items).value=items.find? (fun item => (test item).value) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases h : (test head).value <;> simp only [find,List.find?_cons,h,ih,Bool.false_eq_true,ite_false,ite_true]

theorem find_work {α : Type*} (test : α → CountedValue Bool) (items : List α) (bound : ℕ)
    (h : ∀ item∈items,(test item).work ≤ bound) :
    (find test items).work ≤ items.length*(bound+3)+1 := by
  induction items with
  | nil => simp only [find,List.length_nil,Nat.zero_mul,Nat.zero_add];omega
  | cons head tail ih =>
    have ht := ih (fun item hi => h item (List.mem_cons_of_mem head hi))
    have hh := h head List.mem_cons_self
    simp only [find,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

def splitIndex {groups : ℕ} (index : Fin (groups*2)) : CountedValue (Fin groups × Fin 2) :=
  let division := divideCounter index.val 2
  ⟨(⟨division.quotient,by
      rw [(divideCounter_value index.val 2 (by omega)).1]
      exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using index.isLt)⟩,
    ⟨division.remainder,by rw [(divideCounter_value index.val 2 (by omega)).2];omega⟩),division.work+2⟩

theorem splitIndex_value {groups : ℕ} (index : Fin (groups*2)) :
    (splitIndex index).value=finProdFinEquiv.symm index := by
  apply Prod.ext <;> apply Fin.ext
  · exact (divideCounter_value index.val 2 (by omega)).1
  · exact (divideCounter_value index.val 2 (by omega)).2

def matchesBlock {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (index : Fin (((r+s)+retained.length)*2)) : CountedValue Bool :=
  let pair := splitIndex index
  let value := candidate primary body retained pair.value.1 pair.value.2
  match value.value with
  | none => ⟨false,pair.work+value.work+2⟩
  | some number =>
    let checked := equalCounter number block.val
    ⟨checked.value,pair.work+value.work+checked.work+2⟩

def position {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues)) :
    CountedValue (Option (Fin (((r+s)+retained.length)*2))) :=
  let count := (r+s)+retained.length
  let result := find (matchesBlock primary body retained block) (List.ofFn (id : Fin (count*2) → Fin (count*2)))
  ⟨result.value,result.work+count*2+2⟩

def tagSlot {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) :
    CountedValue (Fin (groupCount primary body tagged) × Fin 2) :=
  let block := readVector (⟨0,by have := (tagged.get index).isLt;omega⟩ : Fin (population legs ordinary queues)) tagged index
  let found := position primary body (kept primary body tagged).value block.value
  let zero : Fin ((groupCount primary body tagged)*2) := ⟨0,by have := groupCount_pos primary body tagged index;omega⟩
  let pair := splitIndex (found.value.getD zero)
  ⟨pair.value,(kept primary body tagged).work+block.work+found.work+pair.work+3⟩

structure Result (r s tags : ℕ) where
  kept : ℕ
  data : BinaryPackedRootMetadata.Data r s kept tags
  work : ℕ

def current {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : Result r s tags :=
  let retained := kept primary body tagged
  let roles := storeData ((r+s)+retained.value.length) (role primary body retained.value)
  let positions := storeData tags (tagSlot primary body tagged)
  ⟨retained.value.length,⟨roles.value,positions.value⟩,retained.work+roles.work+positions.work+4⟩

theorem current_kept_le {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) : (current primary body tagged).kept ≤ tags :=
  kept_length_le primary body tagged

theorem current_role {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin (groupCount primary body tagged)) :
    (current primary body tagged).data.roles.get index=(role primary body (kept primary body tagged).value index).value :=
  storeData_get _ _ _

theorem current_tagSlot {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) :
    (current primary body tagged).data.tagged.get index=(tagSlot primary body tagged index).value :=
  storeData_get _ _ _

theorem candidate_primary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hg : group.val<r) :
    (candidate primary body retained group slot).value=
      some (if slot.val=0 then legs+(primary.get ⟨group.val,hg⟩).val else (primary.get ⟨group.val,hg⟩).val) := by
  have hp := (lessCounter_value group.val r).mpr hg
  simp only [candidate,dif_pos hp,readVector_value,addCounter_value,equalCounter_value]

theorem candidate_ordinary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hp : ¬group.val<r) (hg : group.val<r+s) :
    (candidate primary body retained group slot).value=
      if slot.val=0 then some (legs+legs+(body.get ⟨group.val-r,by omega⟩).val) else none := by
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond := (lessCounter_value group.val (r+s)).mpr hg
  simp only [candidate,dif_neg hfirst,dif_pos hsecond,readVector_value,addCounter_value,
    differenceCounter_value,equalCounter_value]

theorem candidate_kept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (slot : Fin 2) (hg : ¬group.val<r+s) :
    (candidate primary body retained group slot).value=
      if slot.val=0 then some (retained.get ⟨group.val-(r+s),by have := group.isLt;omega⟩).val else none := by
  have hp : ¬group.val<r := by omega
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond : ¬(lessCounter group.val (r+s)).value=true := by simpa only [lessCounter_value] using hg
  simp only [candidate,dif_neg hfirst,dif_neg hsecond,readList_value,differenceCounter_value,equalCounter_value]
  rw [List.getElem?_eq_getElem (by have := group.isLt;omega)]
  rfl

theorem role_primary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hg : group.val<r) : (role primary body retained group).value=.primary := by
  have hp := (lessCounter_value group.val r).mpr hg
  simp only [role,hp,ite_true]

theorem role_ordinary {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hp : ¬group.val<r) (hg : group.val<r+s) : (role primary body retained group).value=.ordinary := by
  have hfirst : ¬(lessCounter group.val r).value=true := by simpa only [lessCounter_value] using hp
  have hsecond := (lessCounter_value group.val (r+s)).mpr hg
  simp only [role,if_neg hfirst,if_pos hsecond]

theorem role_kept {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length))
    (hg : ¬group.val<r+s) :
    (role primary body retained group).value=
      let value := (retained.get ⟨group.val-(r+s),by have := group.isLt;omega⟩).val
      if value<legs then .leg else if value<legs+(legs+ordinary) then .center else .queue := by
  have hp : ¬group.val<r := by omega
  simp only [role,lessCounter_value,if_neg hp,if_neg hg,readList_value,differenceCounter_value,addCounter_value]
  rw [List.getElem?_eq_getElem (by have := group.isLt;omega)]
  rfl

theorem matchesBlock_value {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (index : Fin (((r+s)+retained.length)*2)) :
    (matchesBlock primary body retained block index).value=
      ((candidate primary body retained (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value).any
        (fun number => decide (number=block.val)) := by
  simp only [matchesBlock,splitIndex_value]
  cases h : (candidate primary body retained (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value with
  | none => rfl
  | some number =>
    simp only [Option.any_some]
    exact Bool.eq_iff_iff.mpr (by simp only [equalCounter_value,decide_eq_true_eq])

theorem position_value {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues)) :
    (position primary body retained block).value=
      (List.ofFn (id : Fin (((r+s)+retained.length)*2) → Fin (((r+s)+retained.length)*2))).find?
        (fun index => ((candidate primary body retained (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value).any
          (fun number => decide (number=block.val))) := by
  simp only [position,find_value,matchesBlock_value]

theorem position_of_unique {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (target : Fin (((r+s)+retained.length)*2))
    (h : ∀ index,(matchesBlock primary body retained block index).value=true ↔ index=target) :
    (position primary body retained block).value=some target := by
  change (find (matchesBlock primary body retained block) (List.ofFn id)).value=some target
  rw [find_value]
  apply (List.find?_ofFn_eq_some_of_injective (f := id) Function.injective_id).mpr
  constructor
  · exact (h target).mpr rfl
  · intro earlier he hmatch
    have hh := (h earlier).mp hmatch
    subst earlier
    exact lt_irrefl _ he

end CurrentAFT.BinaryRootMetadataSerializer

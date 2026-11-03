import CurrentAFT.BinaryRootMetadataSerializer
import CurrentAFT.BinaryFullResponseCounts

/-! Actual operation counts for the bounded metadata serializer. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def missingWork (size count : ℕ) := count*(3*count+20*size+34)+1

theorem primaryMissing_work {legs ordinary queues r : ℕ} (primary : Vector (Fin legs) r)
    (block : Fin (population legs ordinary queues)) :
    (primaryMissing primary block).work ≤ missingWork (population legs ordinary queues) r := by
  apply BinaryProposalGuard.allFin_work r (3*r+20*(population legs ordinary queues)+32)
  intro index
  let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
  have hr := readVector_work (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
  have ha := addCounter_work legs found.value.val
  have hf := found.value.isLt
  have he := equalCounter_work block.val found.value.val
  have hc := equalCounter_work block.val (addCounter legs found.value.val).count
  rw [addCounter_value] at hc
  have hb := block.isLt
  change found.work+(addCounter legs found.value.val).work+(equalCounter block.val found.value.val).work+
    (equalCounter block.val (addCounter legs found.value.val).count).work+4 ≤ _
  change found.work ≤ 3*r+3 at hr
  simp only [addCounter_value] at *
  unfold population at *
  omega

theorem ordinaryMissing_work {legs ordinary queues s : ℕ} (body : Vector (Fin ordinary) s)
    (block : Fin (population legs ordinary queues)) :
    (ordinaryMissing body block).work ≤ missingWork (population legs ordinary queues) s := by
  apply BinaryProposalGuard.allFin_work s (3*s+20*(population legs ordinary queues)+32)
  intro index
  let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
  have hr := readVector_work (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
  have ha := addCounter_work legs legs
  have hp := addCounter_work (addCounter legs legs).count found.value.val
  rw [addCounter_value] at hp
  have hf := found.value.isLt
  have he := equalCounter_work block.val (addCounter (addCounter legs legs).count found.value.val).count
  rw [addCounter_value,addCounter_value] at he
  have hb := block.isLt
  change found.work+(addCounter legs legs).work+(addCounter (addCounter legs legs).count found.value.val).work+
    (equalCounter block.val (addCounter (addCounter legs legs).count found.value.val).count).work+4 ≤ _
  change found.work ≤ 3*s+3 at hr
  simp only [addCounter_value] at *
  unfold population at *
  omega

def keptWork (size r s tags : ℕ) := tags*(missingWork size r+missingWork size s+5)+tags+2

theorem kept_work {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    (kept primary body tagged).work ≤ keptWork (population legs ordinary queues) r s tags := by
  have h := filter_work (isKept primary body) tagged.toList
    (missingWork (population legs ordinary queues) r+missingWork (population legs ordinary queues) s+2) (by
      intro block _
      have hp := primaryMissing_work primary block
      have hb := ordinaryMissing_work body block
      change _+_+2 ≤ _
      omega)
  simp only [Vector.length_toList] at h
  change _+tags+1 ≤ _
  unfold keptWork
  ring_nf at h ⊢
  omega

def localWork (size r s retained : ℕ) := 100*(size+r+s+retained+1)

theorem candidate_work {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length)) (slot : Fin 2) :
    (candidate primary body retained group slot).work ≤ localWork (population legs ordinary queues) r s retained.length := by
  have wf := lessCounter_work_right group.val r
  have ws := lessCounter_work_right group.val (r+s)
  have wz := equalCounter_work slot.val 0
  have hz := slot.isLt
  have hg := group.isLt
  by_cases hp : (lessCounter group.val r).value=true
  · rw [candidate,dif_pos hp]
    let index : Fin r := ⟨group.val,(lessCounter_value _ _).mp hp⟩
    let found := readVector (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    have wr := readVector_work (⟨0,by have := (primary.get index).isLt;omega⟩ : Fin legs) primary index
    have wa := addCounter_work legs found.value.val
    change found.work ≤ 3*r+3 at wr
    change (lessCounter group.val r).work+(lessCounter group.val (r+s)).work+(equalCounter slot.val 0).work+
      found.work+(addCounter legs found.value.val).work+5 ≤ _
    unfold localWork population
    omega
  · by_cases hb : (lessCounter group.val (r+s)).value=true
    · rw [candidate,dif_neg hp,dif_pos hb]
      let index : Fin s := ⟨(differenceCounter group.val r).count,by
        rw [differenceCounter_value]
        have ht := (lessCounter_value _ _).mp hb
        have hf : ¬group.val<r := fun h => hp ((lessCounter_value _ _).mpr h)
        omega⟩
      let found := readVector (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
      have wd := differenceCounter_work group.val r
      have wr := readVector_work (⟨0,by have := (body.get index).isLt;omega⟩ : Fin ordinary) body index
      have wa := addCounter_work legs legs
      have wb := addCounter_work (addCounter legs legs).count found.value.val
      change found.work ≤ 3*s+3 at wr
      change (lessCounter group.val r).work+(lessCounter group.val (r+s)).work+(equalCounter slot.val 0).work+
        (differenceCounter group.val r).work+found.work+(addCounter legs legs).work+
        (addCounter (addCounter legs legs).count found.value.val).work+7 ≤ _
      simp only [addCounter_value] at *
      unfold localWork population
      omega
    · rw [candidate,dif_neg hp,dif_neg hb]
      have wd := differenceCounter_work group.val (r+s)
      have wr := readList_work retained (differenceCounter group.val (r+s)).count
      change _+_+_+_+_+5 ≤ _
      unfold localWork population
      omega

theorem role_work {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length)) :
    (role primary body retained group).work ≤ localWork (population legs ordinary queues) r s retained.length := by
  have wf := lessCounter_work_right group.val r
  have ws := lessCounter_work_right group.val (r+s)
  have hg := group.isLt
  by_cases hp : (lessCounter group.val r).value=true
  · simp only [role,if_pos hp]
    unfold localWork;omega
  · by_cases hb : (lessCounter group.val (r+s)).value=true
    · simp only [role,if_neg hp,if_pos hb]
      unfold localWork;omega
    · simp only [role,if_neg hp,if_neg hb]
      have wd := differenceCounter_work group.val (r+s)
      have wr := readList_work retained (differenceCounter group.val (r+s)).count
      have wl := lessCounter_work_right (((readList retained (differenceCounter group.val (r+s)).count).data.map Fin.val).getD 0) legs
      have wa := addCounter_work legs ordinary
      have wb := addCounter_work legs (addCounter legs ordinary).count
      have wc := lessCounter_work_right (((readList retained (differenceCounter group.val (r+s)).count).data.map Fin.val).getD 0)
        (addCounter legs (addCounter legs ordinary).count).count
      change _+_+_+_+_+_+_+_+9 ≤ _
      simp only [addCounter_value] at *
      unfold localWork population
      omega

theorem candidate_lt {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (group : Fin ((r+s)+retained.length)) (slot : Fin 2)
    (number : ℕ) (h : (candidate primary body retained group slot).value=some number) : number<population legs ordinary queues := by
  by_cases hp : group.val<r
  · rw [candidate_primary primary body retained group slot hp] at h
    have he := Option.some.inj h
    split_ifs at he with hz
    · have ht := (primary.get ⟨group.val,hp⟩).isLt
      unfold population;omega
    · have ht := (primary.get ⟨group.val,hp⟩).isLt
      unfold population;omega
  · by_cases hb : group.val<r+s
    · rw [candidate_ordinary primary body retained group slot hp hb] at h
      split_ifs at h with hz
      · have he := Option.some.inj h
        have ht := (body.get (⟨group.val-r,by omega⟩ : Fin s)).isLt
        unfold population;omega
    · rw [candidate_kept primary body retained group slot hb] at h
      split_ifs at h with hz
      · have he := Option.some.inj h
        have ht := (retained.get (⟨group.val-(r+s),by have := group.isLt;omega⟩ : Fin retained.length)).isLt
        omega

def splitWork (groups : ℕ) := 500*(2*groups+4)^2+2

theorem splitIndex_work {groups : ℕ} (index : Fin (groups*2)) : (splitIndex index).work ≤ splitWork groups := by
  have h := divideCounter_work index.val 2 (by omega)
  have hi := index.isLt
  change _+2 ≤ _
  unfold splitWork
  have hs : index.val+2+2 ≤ 2*groups+4 := by omega
  have hp := Nat.pow_le_pow_left hs 2
  omega

def matchWork (size r s retained : ℕ) := splitWork (r+s+retained)+localWork size r s retained+6*size+4

theorem matchesBlock_work {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues))
    (index : Fin (((r+s)+retained.length)*2)) :
    (matchesBlock primary body retained block index).work ≤ matchWork (population legs ordinary queues) r s retained.length := by
  let pair := splitIndex index
  let value := candidate primary body retained pair.value.1 pair.value.2
  have hs := splitIndex_work index
  change pair.work ≤ _ at hs
  have hc := candidate_work primary body retained pair.value.1 pair.value.2
  change value.work ≤ _ at hc
  unfold matchesBlock
  change (match value.value with
    | none => ⟨false,pair.work+value.work+2⟩
    | some number => ⟨(equalCounter number block.val).value,pair.work+value.work+(equalCounter number block.val).work+2⟩ : CountedValue Bool).work ≤ _
  cases h : value.value with
  | none =>
    change pair.work+value.work+2 ≤ _
    unfold matchWork;omega
  | some number =>
    have hn := candidate_lt primary body retained pair.value.1 pair.value.2 number h
    have he := equalCounter_work number block.val
    have hb := block.isLt
    change pair.work+value.work+(equalCounter number block.val).work+2 ≤ _
    unfold matchWork
    omega

def positionWork (size r s retained : ℕ) :=
  ((r+s+retained)*2)*(matchWork size r s retained+3)+1+(r+s+retained)*2+2

theorem position_work {legs ordinary queues r s : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (retained : List (Fin (population legs ordinary queues))) (block : Fin (population legs ordinary queues)) :
    (position primary body retained block).work ≤ positionWork (population legs ordinary queues) r s retained.length := by
  have h := find_work (matchesBlock primary body retained block)
    (List.ofFn (id : Fin (((r+s)+retained.length)*2) → Fin (((r+s)+retained.length)*2)))
    (matchWork (population legs ordinary queues) r s retained.length) (fun index _ => matchesBlock_work primary body retained block index)
  simp only [List.length_ofFn] at h
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

def tagWork (size r s tags : ℕ) := keptWork size r s tags+3*tags+3+positionWork size r s tags+splitWork (r+s+tags)+3

theorem tagSlot_work {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (index : Fin tags) :
    (tagSlot primary body tagged index).work ≤ tagWork (population legs ordinary queues) r s tags := by
  let retained := kept primary body tagged
  let block := readVector (⟨0,by have := (tagged.get index).isLt;omega⟩ : Fin (population legs ordinary queues)) tagged index
  let found := position primary body retained.value block.value
  let zero : Fin ((groupCount primary body tagged)*2) := ⟨0,by have := groupCount_pos primary body tagged index;omega⟩
  have hk := kept_work primary body tagged
  have hl := kept_length_le primary body tagged
  have hr := readVector_work (⟨0,by have := (tagged.get index).isLt;omega⟩ : Fin (population legs ordinary queues)) tagged index
  have hp := position_work primary body retained.value block.value
  have hs := splitIndex_work (found.value.getD zero)
  change retained.work ≤ _ at hk
  change retained.value.length ≤ tags at hl
  change block.work ≤ 3*tags+3 at hr
  change found.work ≤ _ at hp
  have hposition : positionWork (population legs ordinary queues) r s retained.value.length ≤ positionWork (population legs ordinary queues) r s tags := by
    unfold positionWork matchWork splitWork localWork
    gcongr
  have hsplit : splitWork (r+s+retained.value.length) ≤ splitWork (r+s+tags) := by unfold splitWork;gcongr
  change retained.work+block.work+found.work+(splitIndex (found.value.getD zero)).work+3 ≤ _
  unfold tagWork
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hk hr) (hp.trans hposition)) (hs.trans hsplit)) _

def workBound (size r s tags : ℕ) := keptWork size r s tags+(r+s+tags)*(localWork size r s tags+2)+2+
  tags*(tagWork size r s tags+2)+2+4

theorem current_work {legs ordinary queues r s tags : ℕ} (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) :
    (current primary body tagged).work ≤ workBound (population legs ordinary queues) r s tags := by
  let retained := kept primary body tagged
  have hk := kept_work primary body tagged
  change retained.work ≤ _ at hk
  have hl := kept_length_le primary body tagged
  change retained.value.length ≤ tags at hl
  have hr := storeData_work ((r+s)+retained.value.length)
    (localWork (population legs ordinary queues) r s retained.value.length) (role primary body retained.value)
    (fun group => role_work primary body retained.value group)
  have ht := storeData_work tags (tagWork (population legs ordinary queues) r s tags)
    (tagSlot primary body tagged) (tagSlot_work primary body tagged)
  have hm : ((r+s)+retained.value.length)*(localWork (population legs ordinary queues) r s retained.value.length+2)+2 ≤
      (r+s+tags)*(localWork (population legs ordinary queues) r s tags+2)+2 := by unfold localWork;gcongr
  change retained.work+(storeData ((r+s)+retained.value.length) (role primary body retained.value)).work+
    (storeData tags (tagSlot primary body tagged)).work+4 ≤ _
  unfold workBound
  omega

theorem workBound_mono {size size' r r' s s' tags tags' : ℕ} (hsize : size ≤ size')
    (hr : r ≤ r') (hs : s ≤ s') (ht : tags ≤ tags') : workBound size r s tags ≤ workBound size' r' s' tags' := by
  unfold workBound tagWork positionWork matchWork splitWork localWork keptWork missingWork
  gcongr

noncomputable def workPolynomial (order : ℕ) : Polynomial ℕ :=
  let size := BinaryProposalMetadata.sizePolynomial
  let degree := Polynomial.C order
  let missing := degree*(3*degree+20*size+34)+1
  let retained := degree*(missing+missing+5)+degree+2
  let localCost := 100*(size+degree+degree+degree+1)
  let split := 500*(2*(degree+degree+degree)+4)^2+2
  let matchCost := split+localCost+6*size+4
  let position := ((degree+degree+degree)*2)*(matchCost+3)+1+(degree+degree+degree)*2+2
  let tag := retained+3*degree+3+position+split+3
  retained+(degree+degree+degree)*(localCost+2)+2+degree*(tag+2)+2+4

theorem workPolynomial_eval (order security : ℕ) :
    (workPolynomial order).eval security=workBound (BinaryProposalMetadata.sizeBound security) order order order := by
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,BinaryProposalMetadata.sizePolynomial_eval,
    workBound,tagWork,positionWork,matchWork,splitWork,localWork,keptWork,missingWork]

theorem current_work_fixed_order {legs ordinary queues r s tags : ℕ} (order : ℕ)
    (primary : Vector (Fin legs) r) (body : Vector (Fin ordinary) s)
    (tagged : Vector (Fin (population legs ordinary queues)) tags) (hr : r+s ≤ order) (ht : tags ≤ order) :
    (current primary body tagged).work ≤ workBound (population legs ordinary queues) order order order := by
  exact (current_work primary body tagged).trans (workBound_mono le_rfl (by omega) (by omega) ht)

theorem current_polynomial_work (security order : ℕ) {r s tags : ℕ}
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (tagged : Vector (Fin (population (BinaryFullResponseCounts.current security).leg
      (BinaryFullResponseCounts.current security).ordinary (BinaryFullResponseCounts.current security).queue)) tags)
    (hr : r+s ≤ order) (ht : tags ≤ order) :
    (current primary body tagged).work ≤ (workPolynomial order).eval security := by
  have hsize : population (BinaryFullResponseCounts.current security).leg
      (BinaryFullResponseCounts.current security).ordinary (BinaryFullResponseCounts.current security).queue ≤
      BinaryProposalMetadata.sizeBound security := by
    change _+(_+_)+_ ≤ _
    rw [BinaryFullResponseCounts.body_decomposition]
    exact (BinaryFullResponseCounts.current_sizes security).2.2.2
  rw [workPolynomial_eval]
  exact (current_work_fixed_order order primary body tagged hr ht).trans (workBound_mono hsize le_rfl le_rfl le_rfl)

end CurrentAFT.BinaryRootMetadataSerializer

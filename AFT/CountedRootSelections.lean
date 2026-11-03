import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! # Fixed-order root-set enumeration, without an exponential powerset

The include/exclude recursion stops as soon as the requested cardinality
is zero. Its stored work and output lengths have polynomial bounds for
fixed order. The actual response uses orders at most twice its cutoff.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

structure CountedSubsequences (α : Type*) where
  value : List (List α)
  work : ℕ

/-- Both recursive lists are materialized once; the counter includes the
append traversal and allocation of the new leading elements. -/
def countedSubsequences {α : Type*} : ℕ → List α → CountedSubsequences α
  | 0,_ => ⟨[[]],1⟩
  | _+1,[] => ⟨[],1⟩
  | order+1,head::tail =>
      let without := countedSubsequences (order+1) tail
      let withHead := countedSubsequences order tail
      ⟨without.value++withHead.value.map (head::·),
        without.work+withHead.work+without.value.length+2*withHead.value.length+4⟩

theorem countedSubsequences_value {α : Type*} (order : ℕ) (source : List α) :
    (countedSubsequences order source).value=source.sublistsLen order := by
  induction source generalizing order with
  | nil => cases order <;> simp [countedSubsequences]
  | cons head tail ih =>
    cases order with
    | zero => simp [countedSubsequences]
    | succ order => simp only [countedSubsequences,ih,List.sublistsLen_succ_cons]

theorem countedSubsequences_length {α : Type*} (order : ℕ) (source : List α) :
    (countedSubsequences order source).value.length=source.length.choose order := by
  rw [countedSubsequences_value,List.length_sublistsLen]

theorem countedSubsequences_work {α : Type*} (order : ℕ) (source : List α) :
    (countedSubsequences order source).work≤10*(order+1)*(source.length+1)^(order+2) := by
  induction source generalizing order with
  | nil =>
    cases order with
    | zero => norm_num [countedSubsequences]
    | succ order => simp [countedSubsequences]; omega
  | cons head tail ih =>
    cases order with
    | zero =>
      simp only [countedSubsequences,List.length_cons,Nat.zero_add]
      have hp : 1≤(tail.length+1+1)^2 := Nat.one_le_pow _ _ (by omega)
      omega
    | succ order =>
      let x := tail.length+1
      have hx : 1≤x := by dsimp [x];omega
      have hwithout := ih (order+1)
      have hwith := ih order
      have hfirst : tail.length.choose (order+1)≤x^(order+2) :=
        (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by dsimp [x];omega) _).trans
          (Nat.pow_le_pow_right hx (by omega)))
      have hsecond : tail.length.choose order≤x^(order+2) :=
        (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by dsimp [x];omega) _).trans
          (Nat.pow_le_pow_right hx (by omega)))
      have hone : 1≤x^(order+2) := Nat.one_le_pow _ _ hx
      have hstep : x^(order+3)+x^(order+2)≤(x+1)^(order+3) := by
        calc
          _ = (x+1)*x^(order+2) := by rw [show order+3=(order+2)+1 by omega,pow_succ];ring
          _ ≤ (x+1)*(x+1)^(order+2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
          _ = _ := by rw [show order+3=(order+2)+1 by omega,pow_succ];ring
      simp only [countedSubsequences,countedSubsequences_length,List.length_cons]
      change _≤10*(order+2)*(x+1)^(order+3)
      change (countedSubsequences (order+1) tail).work≤10*(order+2)*x^(order+3) at hwithout
      change (countedSubsequences order tail).work≤10*(order+1)*x^(order+2) at hwith
      nlinarith [Nat.mul_le_mul_left (10*(order+2)) hstep]

/-- Each small root set is generated from a bounded-cardinality sublist. -/
def boundedRootList (population bound : ℕ) : List (Finset (Fin population)) :=
  (List.range (bound+1)).flatMap (fun order =>
    ((countedSubsequences order (List.finRange population)).value).map List.toFinset)

def boundedRootSelections (population cutoff : ℕ) : Finset (Finset (Fin population)) :=
  (boundedRootList population (2*cutoff)).toFinset.filter (fun selected => 2≤selected.card)

theorem mem_boundedRootList (population bound : ℕ) (selected : Finset (Fin population)) :
    selected∈boundedRootList population bound ↔ selected.card≤bound := by
  simp only [boundedRootList,List.mem_flatMap,List.mem_range,List.mem_map,countedSubsequences_value]
  constructor
  · rintro ⟨order,horder,word,hword,rfl⟩
    obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hword
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange population)),hlen]
    omega
  · intro hcard
    let word := (List.finRange population).filter (fun point => decide (point∈selected))
    have hset : word.toFinset=selected := by
      ext point
      simp [word]
    have hlen : word.length=selected.card := by
      rw [←hset,List.toFinset_card_of_nodup]
      exact List.Nodup.filter _ (List.nodup_finRange population)
    refine ⟨selected.card,by omega,word,List.mem_sublistsLen.mpr ⟨List.filter_sublist,hlen⟩,hset⟩

theorem boundedRootSelections_exact (population cutoff : ℕ) :
    boundedRootSelections population cutoff=
      (Finset.univ : Finset (Finset (Fin population))).filter (fun selected =>
        2≤selected.card ∧ selected.card≤2*cutoff) := by
  ext selected
  simp only [boundedRootSelections,Finset.mem_filter,List.mem_toFinset,mem_boundedRootList,Finset.mem_univ,true_and]
  exact and_comm

theorem boundedRootList_length (population bound : ℕ) :
    (boundedRootList population bound).length≤(bound+1)*(population+1)^bound := by
  unfold boundedRootList
  rw [List.length_flatMap]
  simp only [List.length_map,countedSubsequences_length,List.length_finRange]
  have hh : ∀ order∈List.range (bound+1),population.choose order≤(population+1)^bound := by
    intro order ho
    have hk := List.mem_range.mp ho
    exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  calc
    _ ≤ ((List.range (bound+1)).map (fun _ => (population+1)^bound)).sum := List.sum_le_sum hh
    _ = _ := by simp

theorem boundedRootSelections_card (population cutoff : ℕ) :
    (boundedRootSelections population cutoff).card≤(2*cutoff+1)*(population+1)^(2*cutoff) := by
  exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (boundedRootList_length _ _))

/-- The ordered sublists already distinguish the root sets. No duplicate
removal is needed by a summation evaluator. -/
theorem boundedRootList_nodup (population bound : ℕ) :
    (boundedRootList population bound).Nodup := by
  unfold boundedRootList
  simp only [countedSubsequences_value]
  apply List.nodup_flatMap.mpr
  constructor
  · intro order _
    apply List.Nodup.map_on _ (List.nodup_sublistsLen order (List.nodup_finRange population))
    intro first hf second hs he
    have hf' := (List.mem_sublistsLen.mp hf).1
    have hs' := (List.mem_sublistsLen.mp hs).1
    have hm : ∀ point,point∈first ↔ point∈second := by
      intro point
      simpa only [List.mem_toFinset] using (Iff.of_eq (congrArg (fun s : Finset (Fin population) => point∈s) he))
    exact List.Subset.antisymm_of_pairwise
      ((List.sortedLT_finRange population).pairwise.sublist hf')
      ((List.sortedLT_finRange population).pairwise.sublist hs')
      (fun point hp => (hm point).mp hp) (fun point hp => (hm point).mpr hp)
  · apply (List.nodup_range (n := bound+1)).imp
    intro first second hne selected hf hs
    obtain ⟨left,hl,rfl⟩ := List.mem_map.mp hf
    obtain ⟨right,hr,he⟩ := List.mem_map.mp hs
    have hl' := List.mem_sublistsLen.mp hl
    have hr' := List.mem_sublistsLen.mp hr
    have hc := congrArg Finset.card he
    rw [List.toFinset_card_of_nodup (hr'.1.nodup (List.nodup_finRange population)),
      List.toFinset_card_of_nodup (hl'.1.nodup (List.nodup_finRange population)),hr'.2,hl'.2] at hc
    exact hne hc.symm

/-- Runtime list used by the connected response. It has no powerset or
deduplication stage, and each legal nonempty root set occurs exactly once. -/
def rootSelectionList (population cutoff : ℕ) : List (Finset (Fin population)) :=
  (boundedRootList population (2*cutoff)).filter (fun selected => decide (2≤selected.card))

theorem rootSelectionList_nodup (population cutoff : ℕ) :
    (rootSelectionList population cutoff).Nodup :=
  (boundedRootList_nodup _ _).filter _

theorem rootSelectionList_toFinset (population cutoff : ℕ) :
    (rootSelectionList population cutoff).toFinset=boundedRootSelections population cutoff := by
  ext selected
  simp [rootSelectionList,boundedRootSelections]

theorem rootSelectionList_sum {M : Type*} [AddCommMonoid M]
    (population cutoff : ℕ) (value : Finset (Fin population) → M) :
    ((rootSelectionList population cutoff).map value).sum=
      ∑ selected∈(Finset.univ : Finset (Finset (Fin population))).filter
        (fun selected => 2≤selected.card ∧ selected.card≤2*cutoff),value selected := by
  rw [←boundedRootSelections_exact,←rootSelectionList_toFinset]
  exact (List.sum_toFinset _ (rootSelectionList_nodup _ _)).symm

/-- Generation counts all include/exclude traversals; conversion of an
ordered list to a finite set and the length test are charged quadratically
in the fixed order. The top-level list is traversed only once. -/
def rootSelectionWork (population cutoff : ℕ) : ℕ :=
  ((List.range (2*cutoff+1)).map (fun order =>
    (countedSubsequences order (List.finRange population)).work+
      (order+1)^2*(countedSubsequences order (List.finRange population)).value.length+1)).sum

theorem rootSelectionWork_le (population cutoff : ℕ) :
    rootSelectionWork population cutoff≤
      (2*cutoff+1)*(10*(2*cutoff+1)+(2*cutoff+1)^2+1)*(population+1)^(2*cutoff+2) := by
  let bound := 2*cutoff
  have hh : ∀ order∈List.range (bound+1),
      (countedSubsequences order (List.finRange population)).work+
        (order+1)^2*(countedSubsequences order (List.finRange population)).value.length+1≤
      (10*(bound+1)+(bound+1)^2+1)*(population+1)^(bound+2) := by
    intro order ho
    have hk : order≤bound := by have := List.mem_range.mp ho;omega
    have hwork := countedSubsequences_work order (List.finRange population)
    simp only [List.length_finRange] at hwork
    have hpow := Nat.pow_le_pow_right (by omega : 1≤population+1) (by omega : order+2≤bound+2)
    have hlength : (countedSubsequences order (List.finRange population)).value.length≤(population+1)^(bound+2) := by
      rw [countedSubsequences_length,List.length_finRange]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by omega) _).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have h1 : 1≤(population+1)^(bound+2) := Nat.one_le_pow _ _ (by omega)
    have hw : (countedSubsequences order (List.finRange population)).work≤
        10*(bound+1)*(population+1)^(bound+2) := hwork.trans (by gcongr)
    have hl : (order+1)^2*(countedSubsequences order (List.finRange population)).value.length≤
        (bound+1)^2*(population+1)^(bound+2) := by gcongr
    nlinarith
  unfold rootSelectionWork
  calc
    _ ≤ ((List.range (bound+1)).map (fun _ =>
      (10*(bound+1)+(bound+1)^2+1)*(population+1)^(bound+2))).sum := List.sum_le_sum hh
    _ = _ := by simp [bound];ring

end AFT.RationalNumerics

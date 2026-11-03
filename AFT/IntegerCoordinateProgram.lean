import AFT.Algebra

/-! # Executable integral path and rounding-coordinate inverses

The runtime uses integer addition and division on materialized vectors.
The inverse is proved equal to the abstract integral coordinate isomorphism.
-/
namespace AFT
open scoped BigOperators

theorem vectorGet_ofFn {α : Type*} {count : ℕ} (f : Fin count → α) :
    (Vector.ofFn f).get=f := by
  funext index
  exact Vector.get_ofFn f index

structure IntegerVectorRun (count : ℕ) where
  value : Vector ℤ count
  work : ℕ

/-- Eliminate the first path vertex, materializing the remaining load once. -/
def pathInverseProgram : (count : ℕ) → Vector ℤ (count+1) → IntegerVectorRun count
  | 0,_ => ⟨Vector.ofFn (fun index => Fin.elim0 index),0⟩
  | count+1,load =>
    let first := load.get 0
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then first else 0)
    let remaining := pathInverseProgram count tail
    ⟨Vector.ofFn (Fin.cons first remaining.value.get),remaining.work+4*(count+1)+2⟩

 theorem pathInverseProgram_load (count : ℕ) (load : Vector ℤ (count+1))
    (hload : totalCharge load.get=0) : pathLoad count (pathInverseProgram count load).value.get=load.get := by
  induction count with
  | zero =>
    funext index
    have hi : index=0 := Fin.ext (by omega)
    subst index
    simpa [totalCharge,pathLoad] using hload.symm
  | succ count ih =>
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0)
    have ht : totalCharge tail.get=0 := by
      have hsum : load.get 0+(∑ index : Fin (count+1),load.get index.succ)=0 := by
        simpa only [totalCharge,Fin.sum_univ_succ] using hload
      simpa [tail,totalCharge,Finset.sum_add_distrib,add_comm] using hsum
    have hh := ih tail ht
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp only [pathInverseProgram,Vector.get_ofFn,pathLoad,Fin.cons_zero]
    · simp only [pathInverseProgram,vectorGet_ofFn,pathLoad,Fin.cons_succ,Fin.tail_cons]
      change pathLoad count (pathInverseProgram count tail).value.get rest -
        (if rest=0 then load.get 0 else 0)=load.get rest.succ
      rw [hh]
      simp [tail]

 theorem pathInverseProgram_work (count : ℕ) (load : Vector ℤ (count+1)) :
    (pathInverseProgram count load).work≤4*(count+1)^2 := by
  induction count with
  | zero => simp [pathInverseProgram]
  | succ count ih =>
    have hh := ih (Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0))
    simp only [pathInverseProgram]
    nlinarith

 theorem pathInverseProgram_bound (count bound : ℕ) (load : Vector ℤ (count+1))
    (hload : ∀ index,(load.get index).natAbs≤bound) (index : Fin count) :
    ((pathInverseProgram count load).value.get index).natAbs≤2^count*bound := by
  induction count generalizing bound with
  | zero => exact Fin.elim0 index
  | succ count ih =>
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0)
    have ht (slot : Fin (count+1)) : (tail.get slot).natAbs≤2*bound := by
      simp only [tail,Vector.get_ofFn]
      apply (Int.natAbs_add_le _ _).trans
      have hh : (if slot=0 then load.get 0 else 0).natAbs≤bound := by
        split_ifs
        · exact hload 0
        · simp
      have hs := hload slot.succ
      omega
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp only [pathInverseProgram,Vector.get_ofFn,Fin.cons_zero]
      exact (hload 0).trans (Nat.le_mul_of_pos_left bound (by positivity))
    · have hh := ih (2*bound) tail ht rest
      simp only [pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
      change _≤2^(count+1)*bound
      convert hh using 1
      rw [pow_succ]
      ring

structure IntegerLoadRun (count : ℕ) where
  value : Vector ℤ (count+1)
  work : ℕ

/-- Materialized forward path incidence, with each tail computed once. -/
def pathForwardProgram : (count : ℕ) → Vector ℤ count → IntegerLoadRun count
  | 0,_ => ⟨Vector.ofFn (fun _ => 0),0⟩
  | count+1,edges =>
    let first := edges.get 0
    let remaining := pathForwardProgram count (Vector.ofFn (fun index => edges.get index.succ))
    ⟨Vector.ofFn (Fin.cons first (fun index => remaining.value.get index-if index=0 then first else 0)),
      remaining.work+4*(count+1)+2⟩

 theorem pathForwardProgram_value (count : ℕ) (edges : Vector ℤ count) :
    (pathForwardProgram count edges).value.get=pathLoad count edges.get := by
  induction count with
  | zero => funext index;simp [pathForwardProgram,pathLoad]
  | succ count ih =>
    simp only [pathForwardProgram,vectorGet_ofFn,ih,pathLoad]
    rfl

 theorem pathForwardProgram_work (count : ℕ) (edges : Vector ℤ count) :
    (pathForwardProgram count edges).work≤4*(count+1)^2 := by
  induction count with
  | zero => simp [pathForwardProgram]
  | succ count ih =>
    have hh := ih (Vector.ofFn (fun index => edges.get index.succ))
    simp only [pathForwardProgram]
    nlinarith

 theorem pathLoad_bound (count bound : ℕ) (edges : Fin count → ℤ)
    (hedges : ∀ index,(edges index).natAbs≤bound) (vertex : Fin (count+1)) :
    (pathLoad count edges vertex).natAbs≤2^count*bound := by
  induction count with
  | zero => simp [pathLoad]
  | succ count ih =>
    refine Fin.cases ?_ (fun rest => ?_) vertex
    · simp only [pathLoad,Fin.cons_zero]
      exact (hedges 0).trans (Nat.le_mul_of_pos_left _ (by positivity))
    · have hh := ih (Fin.tail edges) (fun index => hedges index.succ) rest
      simp only [pathLoad,Fin.cons_succ]
      apply (Int.natAbs_sub_le _ _).trans
      have hs : (if rest=0 then edges 0 else 0).natAbs≤bound := by
        split_ifs
        · exact hedges 0
        · simp
      have hb : bound≤2^count*bound := Nat.le_mul_of_pos_left _ (by positivity)
      rw [pow_succ]
      nlinarith

noncomputable section
 theorem pathInverseProgram_eq (count : ℕ) (load : zeroSumLattice count) :
    (pathInverseProgram count (Vector.ofFn load.val)).value.get=(pathBasis count).symm load := by
  apply pathLoad_injective count
  rw [pathInverseProgram_load]
  · rw [vectorGet_ofFn]
    exact (congrArg Subtype.val ((pathBasis count).apply_symm_apply load)).symm
  · simpa only [vectorGet_ofFn] using load.property
end

structure IntegerCoordinateRun (count : ℕ) where
  value : Vector ℤ count × ℤ
  work : ℕ

/-- The injection coordinate is the exact total charge divided by q. -/
def roundingInverseProgram (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1)) :
    IntegerCoordinateRun count :=
  let charge := (∑ index,load.get index)/modulus
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  let edges := pathInverseProgram count shifted
  ⟨(edges.value,charge),edges.work+4*(count+1)+3⟩

 theorem roundingInverseProgram_load (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1))
    (hinjection : totalCharge injection.get=modulus) (hload : modulus ∣ totalCharge load.get) :
    roundingLoad count injection.get
      ((roundingInverseProgram count modulus injection load).value.1.get,
        (roundingInverseProgram count modulus injection load).value.2)=load.get := by
  let charge := totalCharge load.get/modulus
  have hcharge : charge*modulus=totalCharge load.get := Int.ediv_mul_cancel hload
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  have hshift : totalCharge shifted.get=0 := by
    rw [vectorGet_ofFn]
    change totalCharge (load.get-charge • injection.get)=0
    rw [totalCharge_sub,totalCharge_smul,hinjection,hcharge,sub_self]
  have hh := pathInverseProgram_load count shifted hshift
  change pathLoad count (pathInverseProgram count shifted).value.get+charge • injection.get=load.get
  rw [hh]
  funext index
  simp only [shifted,Vector.get_ofFn,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

 theorem roundingInverseProgram_work (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1)) :
    (roundingInverseProgram count modulus injection load).work≤20*(count+1)^2 := by
  have hh := pathInverseProgram_work count (Vector.ofFn (fun index =>
    load.get index-((∑ point,load.get point)/modulus)*injection.get index))
  simp only [roundingInverseProgram]
  nlinarith

theorem integerSum_bound {Index : Type*} [Fintype Index] (value : Index → ℤ)
    (bound : ℕ) (hvalue : ∀ index,(value index).natAbs≤bound) :
    (∑ index,value index).natAbs≤Fintype.card Index*bound := by
  classical
  have hs (set : Finset Index) : (∑ index∈set,value index).natAbs≤set.card*bound := by
    induction set using Finset.induction_on with
    | empty => simp
    | @insert index set hi ih =>
      rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi]
      exact (Int.natAbs_add_le _ _).trans (by have hh:=hvalue index;nlinarith)
  simpa using hs Finset.univ

/-- Binary lengths are bounded even though the coarse magnitude bound is exponential. -/
theorem roundingInverseProgram_bound (count modulusBound loadBound : ℕ) (modulus : ℤ)
    (injection load : Vector ℤ (count+1))
    (hinjection : ∀ index,(injection.get index).natAbs≤ modulusBound)
    (hload : ∀ index,(load.get index).natAbs≤loadBound) :
    ((roundingInverseProgram count modulus injection load).value.2).natAbs≤(count+1)*loadBound ∧
      ∀ index,((roundingInverseProgram count modulus injection load).value.1.get index).natAbs≤
        2^count*(loadBound+(count+1)*loadBound*modulusBound) := by
  let charge := (∑ index,load.get index)/modulus
  have hc : charge.natAbs≤(count+1)*loadBound :=
    (Int.natAbs_ediv_le_natAbs _ _).trans (by simpa using integerSum_bound load.get loadBound hload)
  refine ⟨hc,?_⟩
  intro index
  apply pathInverseProgram_bound count (loadBound+(count+1)*loadBound*modulusBound)
  intro vertex
  simp only [Vector.get_ofFn]
  exact (Int.natAbs_sub_le _ _).trans (by
    rw [Int.natAbs_mul]
    exact Nat.add_le_add (hload vertex) (Nat.mul_le_mul hc (hinjection vertex)))

noncomputable section
 theorem roundingInverseProgram_eq (count : ℕ) (modulus : ℤ) (hq : modulus≠0)
    (injection : Vector ℤ (count+1)) (hinjection : totalCharge injection.get=modulus)
    (load : chargeLattice count modulus) :
    ((roundingInverseProgram count modulus injection (Vector.ofFn load.val)).value.1.get,
      (roundingInverseProgram count modulus injection (Vector.ofFn load.val)).value.2)=
        (roundingCoordinates count modulus hq injection.get hinjection).symm load := by
  apply roundingLoad_injective count modulus hq injection.get hinjection
  rw [roundingInverseProgram_load]
  · rw [vectorGet_ofFn]
    exact (congrArg Subtype.val ((roundingCoordinates count modulus hq injection.get hinjection).apply_symm_apply load)).symm
  · exact hinjection
  · simpa only [vectorGet_ofFn] using load.property
end

end AFT

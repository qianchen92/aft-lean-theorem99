import CurrentAFT.BinaryRectangleDecode

namespace CurrentAFT.BinaryRectangleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
open WeightCoordinates
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem joint_decode (base r s code : ℕ) (hb : 0<base) (hc : code<base^(r+s)) :
    jointCode base r s
      (fun index => (tupleDecode base hb r (code/base^s) index).val)
      (fun index => (tupleDecode base hb s (code%base^s) index).val)=code := by
  have hp : 0<base^s := pow_pos hb _
  have hr : code/base^s<base^r := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    simpa only [pow_add] using hc
  unfold jointCode
  rw [tupleCode_decode base r hb _ hr,tupleCode_decode base s hb _ (Nat.mod_lt _ hp)]
  exact Nat.div_add_mod code (base^s)

theorem current_sound (base order margin : ℕ) (hb : 0<base)
    (row : Fin ((order+1)^2)) (column : Fin (base^order)) (data : Data base order margin)
    (h : (current base order margin hb row column).value=some data) :
    RectanglePointIndex.encode base order hb (fun color => margin≤color.val ∧ color.val+margin<base) data.point=(row,column) := by
  unfold current at h
  dsimp only at h
  split_ifs at h with hv hw hs
  · cases Option.some.inj h
    apply Prod.ext
    · apply Fin.ext
      simp only [RectanglePointIndex.encode,Data.point,arityIndex,arityCode,
        (divideCounter_value row.val (order+1) (by omega)).1,(divideCounter_value row.val (order+1) (by omega)).2]
      simpa only [Nat.mul_comm] using Nat.div_add_mod row.val (order+1)
    · apply Fin.ext
      simp only [RectanglePointIndex.encode,Data.point,wordIndex,BinaryCounterTupleDecode.current_get,powerCounter_value,
        (divideCounter_value column.val (base^(divideCounter row.val (order+1)).remainder)) (by positivity)]
      apply joint_decode
      have hh := (lessCounter_value _ _).mp hw
      simpa only [powerCounter_value,addCounter_value] using hh


theorem arity_quotient (order : ℕ) (r s : Fin (order+1)) :
    (divideCounter (arityIndex order r s).val (order+1)).quotient=r.val := by
  rw [(divideCounter_value _ _ (by omega)).1]
  change (r.val*(order+1)+s.val)/(order+1)=r.val
  rw [Nat.mul_comm r.val (order+1),Nat.mul_add_div (by omega),Nat.div_eq_of_lt s.isLt,Nat.add_zero]

theorem arity_remainder (order : ℕ) (r s : Fin (order+1)) :
    (divideCounter (arityIndex order r s).val (order+1)).remainder=s.val := by
  rw [(divideCounter_value _ _ (by omega)).2]
  change (r.val*(order+1)+s.val)%(order+1)=s.val
  rw [Nat.mul_comm r.val (order+1),Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt s.isLt]

theorem current_complete (base order margin : ℕ) (hb : 0<base)
    (point : RectanglePointIndex.Point base order (fun color => margin≤color.val ∧ color.val+margin<base)) :
    (current base order margin hb
      (RectanglePointIndex.encode base order hb _ point).1 (RectanglePointIndex.encode base order hb _ point).2).value.isSome=true := by
  have hr := arity_quotient order point.1.val.1 point.1.val.2
  have hs := arity_remainder order point.1.val.1 point.1.val.2
  have hdegree := point.1.property
  have hwithin := jointCode_lt base point.1.val.1.val point.1.val.2.val hb (fun index => (point.2.1 index).val)
    (fun index => (point.2.2 index).val.val) (fun index => (point.2.1 index).isLt) (fun index => (point.2.2 index).val.isLt)
  have hbody (index : Fin point.1.val.2.val) :
      (BinaryCounterTupleDecode.current base hb point.1.val.2.val
        (divideCounter (RectanglePointIndex.encode base order hb _ point).2.val (powerCounter base point.1.val.2.val).count).remainder).value.get index =
      (point.2.2 index).val := by
    rw [BinaryCounterTupleDecode.current_get]
    rw [(divideCounter_value _ _ (by rw [powerCounter_value]; exact pow_pos hb _)).2,powerCounter_value]
    change tupleDecode base hb point.1.val.2.val
      (jointCode base point.1.val.1.val point.1.val.2.val (fun i => (point.2.1 i).val) (fun i => (point.2.2 i).val.val)%base^point.1.val.2.val) index = _
    rw [jointCode_mod base _ _ hb,tupleDecode_code]
  unfold current
  dsimp only
  split_ifs with hv hw ht
  · rfl
  · exfalso
    apply ht
    have hs' : (divideCounter (RectanglePointIndex.encode base order hb _ point).1.val (order+1)).remainder=point.1.val.2.val := hs
    rw [hs']
    apply (safeWord_value _ _ _ _ _).mpr
    intro index
    rw [hbody]
    exact (point.2.2 index).property
  · exfalso
    apply hw
    apply (lessCounter_value _ _).mpr
    simp only [powerCounter_value,addCounter_value]
    simpa only [RectanglePointIndex.encode,wordIndex,hr,hs] using hwithin
  · exfalso
    apply hv
    apply (lessCounter_value _ _).mpr
    simp only [addCounter_value]
    change (divideCounter (arityIndex order point.1.val.1 point.1.val.2).val (order+1)).quotient+
      (divideCounter (arityIndex order point.1.val.1 point.1.val.2).val (order+1)).remainder<order+1
    rw [hr,hs]
    omega


theorem current_value (base order margin : ℕ) (hb : 0<base)
    (row : Fin ((order+1)^2)) (column : Fin (base^order)) :
    (current base order margin hb row column).value.map Data.point=
      RectanglePointIndex.decode base order hb (fun color => margin≤color.val ∧ color.val+margin<base) (row,column) := by
  cases hc : (current base order margin hb row column).value with
  | none =>
    cases hd : RectanglePointIndex.decode base order hb (fun color => margin≤color.val ∧ color.val+margin<base) (row,column) with
    | none => rfl
    | some point =>
      have hi := (RectanglePointIndex.decode_eq_some base order hb _ (row,column) point).mp hd
      have hr := congrArg Prod.fst hi
      have hw := congrArg Prod.snd hi
      dsimp only at hr hw
      have hp := current_complete base order margin hb point
      rw [hr,hw] at hc
      rw [hc] at hp
      cases hp
  | some data =>
    simp only [Option.map_some]
    symm
    apply (RectanglePointIndex.decode_eq_some base order hb _ (row,column) data.point).mpr
    exact (current_sound base order margin hb row column data hc).symm

end CurrentAFT.BinaryRectangleDecode

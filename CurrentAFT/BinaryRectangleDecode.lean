import CurrentAFT.BinaryCounterTupleDecode
import CurrentAFT.BinaryProposalGuard
import CurrentAFT.CurrentRectangleIndex

/-! Polynomially bounded rectangular addresses are decoded using executed
counter division, radix buffers, and safe-body comparisons. -/
namespace CurrentAFT.BinaryRectangleDecode
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Data (base order margin : ℕ) where
  arity : TruncatedArity order
  primary : Vector (Fin base) arity.val.1.val
  body : Vector (Fin base) arity.val.2.val
  safe : ∀ index, margin≤(body.get index).val ∧ (body.get index).val+margin<base

def Data.point {base order margin : ℕ} (data : Data base order margin) :
    RectanglePointIndex.Point base order (fun color => margin≤color.val ∧ color.val+margin<base) :=
  ⟨data.arity,data.primary.get,fun index => ⟨data.body.get index,data.safe index⟩⟩

def safe (base margin color : ℕ) : CountedValue Bool :=
  let lower := lessCounter color margin
  let shifted := addCounter color margin
  let upper := lessCounter shifted.count base
  ⟨!lower.value && upper.value,lower.work+shifted.work+upper.work+3⟩

theorem safe_value (base margin color : ℕ) : (safe base margin color).value=true ↔ margin≤color ∧ color+margin<base := by
  simp only [safe,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,lessCounter_value,addCounter_value]
  constructor
  · rintro ⟨hl,hu⟩
    refine ⟨?_,hu⟩
    by_contra h
    exact hl ((lessCounter_value color margin).mpr (by omega))
  · rintro ⟨hl,hu⟩
    exact ⟨fun h => by have hh := (lessCounter_value color margin).mp h; omega,hu⟩

theorem safe_work (base margin color : ℕ) (hc : color<base) : (safe base margin color).work≤8*base+3*margin+8 := by
  have hl := lessCounter_work color margin
  have ha := addCounter_work color margin
  have hu := lessCounter_work_right (addCounter color margin).count base
  change _+_+_+3 ≤ _
  omega

def safeWord (base margin count : ℕ) (hb : 0<base) (word : Vector (Fin base) count) : CountedValue Bool :=
  BinaryProposalGuard.allFin count (fun index =>
    let color := readVector ⟨0,hb⟩ word index
    let check := safe base margin color.value.val
    ⟨check.value,color.work+check.work+1⟩)

theorem safeWord_value (base margin count : ℕ) (hb : 0<base) (word : Vector (Fin base) count) :
    (safeWord base margin count hb word).value=true ↔ ∀ index, margin≤(word.get index).val ∧ (word.get index).val+margin<base := by
  simp only [safeWord,BinaryProposalGuard.allFin_value,safe_value,readVector_value]

theorem safeWord_work (base margin count : ℕ) (hb : 0<base) (word : Vector (Fin base) count) :
    (safeWord base margin count hb word).work ≤ count*(3*count+8*base+3*margin+14)+1 := by
  apply BinaryProposalGuard.allFin_work
  intro index
  have hr := readVector_work (⟨0,hb⟩:Fin base) word index
  have hs := safe_work base margin (readVector ⟨0,hb⟩ word index).value.val (readVector ⟨0,hb⟩ word index).value.isLt
  change _+_+1≤_
  omega

def current (base order margin : ℕ) (hb : 0<base) (row : Fin ((order+1)^2)) (column : Fin (base^order)) :
    CountedValue (Option (Data base order margin)) :=
  let shape := divideCounter row.val (order+1)
  let r : Fin (order+1) := ⟨shape.quotient, by
    rw [(divideCounter_value row.val (order+1) (by omega)).1]
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [pow_two] using row.isLt⟩
  let s : Fin (order+1) := ⟨shape.remainder, by
    rw [(divideCounter_value row.val (order+1) (by omega)).2]
    exact Nat.mod_lt _ (by omega)⟩
  let degree := addCounter r.val s.val
  let valid := lessCounter degree.count (order+1)
  if hv : valid.value=true then
    let arity : TruncatedArity order := ⟨(r,s),by
      have h := (lessCounter_value _ _).mp hv
      change (addCounter r.val s.val).count<order+1 at h
      rw [addCounter_value] at h
      change r.val+s.val≤order
      omega⟩
    let capacity := powerCounter base degree.count
    let within := lessCounter column.val capacity.count
    if hw : within.value=true then
      let split := powerCounter base s.val
      let divided := divideCounter column.val split.count
      let primary := BinaryCounterTupleDecode.current base hb r.val divided.quotient
      let body := BinaryCounterTupleDecode.current base hb s.val divided.remainder
      let safe := safeWord base margin s.val hb body.value
      if hs : safe.value=true then
        ⟨some ⟨arity,primary.value,body.value,(safeWord_value base margin s.val hb body.value).mp hs⟩,
          shape.work+degree.work+valid.work+capacity.work+within.work+split.work+divided.work+primary.work+body.work+safe.work+12⟩
      else ⟨none,shape.work+degree.work+valid.work+capacity.work+within.work+split.work+divided.work+primary.work+body.work+safe.work+12⟩
    else ⟨none,shape.work+degree.work+valid.work+capacity.work+within.work+7⟩
  else ⟨none,shape.work+degree.work+valid.work+4⟩

end CurrentAFT.BinaryRectangleDecode

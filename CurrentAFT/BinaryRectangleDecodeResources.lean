import CurrentAFT.BinaryRectangleDecode

/-! Resource bounds for executed rectangular address decoding. Every long
division, power counter, radix buffer and safe-body scan is included. -/
namespace CurrentAFT.BinaryRectangleDecodeResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram GradedControlAlgebra
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def headerWork (order : ℕ) : ℕ :=
  500*((order+1)^2+(order+1)+2)^2+(2*order+1)+(3*(order+1)+2)

def safeWork (base order margin : ℕ) : ℕ :=
  order*(3*order+8*base+3*margin+14)+1

def divisionWork (base order : ℕ) : ℕ := 500*(2*base^order+2)^2


def workBound (base order margin : ℕ) : ℕ :=
  headerWork order+2*powerCounterWork base order+(3*base^order+2)+divisionWork base order+
    2*BinaryCounterTupleDecode.workBound base (base^order) order order+safeWork base order margin+12

 theorem powerCounterWork_exponent_mono (base : ℕ) {first second : ℕ} (h : first ≤ second) :
    powerCounterWork base first ≤ powerCounterWork base second := by
  unfold powerCounterWork
  exact Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.add_le_add_right
    (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right h 2))) 4)

 theorem current_work (base order margin : ℕ) (hb : 0<base) (row : Fin ((order+1)^2)) (column : Fin (base^order)) :
    (BinaryRectangleDecode.current base order margin hb row column).work ≤ workBound base order margin := by
  let shape := divideCounter row.val (order+1)
  let r := shape.quotient
  let s := shape.remainder
  let degree := addCounter r s
  let valid := lessCounter degree.count (order+1)
  let capacity := powerCounter base degree.count
  let within := lessCounter column.val capacity.count
  let split := powerCounter base s
  let divided := divideCounter column.val split.count
  let primary := BinaryCounterTupleDecode.current base hb r divided.quotient
  let body := BinaryCounterTupleDecode.current base hb s divided.remainder
  let safe := BinaryRectangleDecode.safeWord base margin s hb body.value
  have hr : r ≤ order := by
    have hquot := (divideCounter_value row.val (order+1) (by omega)).1
    have hlt : row.val/(order+1)<order+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa only [pow_two] using row.isLt)
    dsimp only [r,shape]
    omega
  have hs : s ≤ order := by
    dsimp only [s,shape]
    rw [(divideCounter_value row.val (order+1) (by omega)).2]
    have h := Nat.mod_lt row.val (show 0<order+1 by omega)
    omega
  have hsplit : split.count=base^s := powerCounter_value base s
  have hsplit_pos : 0<split.count := by rw [hsplit];exact pow_pos hb _
  have hsplit_le : split.count ≤ base^order := by rw [hsplit];exact Nat.pow_le_pow_right hb hs
  have hprimary_code : divided.quotient ≤ base^order := by
    dsimp only [divided]
    rw [(divideCounter_value column.val split.count hsplit_pos).1]
    exact (Nat.div_le_self _ _).trans column.isLt.le
  have hbody_code : divided.remainder ≤ base^order := by
    dsimp only [divided]
    rw [(divideCounter_value column.val split.count hsplit_pos).2]
    exact (Nat.mod_lt _ hsplit_pos).le.trans hsplit_le
  have wshape : shape.work ≤ 500*((order+1)^2+(order+1)+2)^2 := by
    exact (divideCounter_work row.val (order+1) (by omega)).trans (by gcongr;exact row.isLt.le)
  have wdegree : degree.work ≤ 2*order+1 := by
    dsimp only [degree]
    rw [addCounter_work]
    omega
  have wvalid : valid.work ≤ 3*(order+1)+2 := lessCounter_work_right degree.count (order+1)
  have wwithin : within.work ≤ 3*base^order+2 :=
    (lessCounter_work_left column.val capacity.count).trans (by omega)
  have wsplit : split.work ≤ powerCounterWork base order :=
    (powerCounter_work base s).trans (powerCounterWork_exponent_mono base hs)
  have wdivision : divided.work ≤ divisionWork base order := by
    apply (divideCounter_work column.val split.count hsplit_pos).trans
    unfold divisionWork
    exact Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2)
  have wprimary : primary.work ≤ BinaryCounterTupleDecode.workBound base (base^order) order order := by
    apply (BinaryCounterTupleDecode.current_work base hb r divided.quotient (base^order) order hprimary_code hr).trans
    unfold BinaryCounterTupleDecode.workBound
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1)
  have wbody : body.work ≤ BinaryCounterTupleDecode.workBound base (base^order) order order := by
    apply (BinaryCounterTupleDecode.current_work base hb s divided.remainder (base^order) order hbody_code hs).trans
    unfold BinaryCounterTupleDecode.workBound
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hs 1)
  have wsafe : safe.work ≤ safeWork base order margin := by
    apply (BinaryRectangleDecode.safeWord_work base margin s hb body.value).trans
    unfold safeWork
    exact Nat.add_le_add_right (Nat.mul_le_mul hs (by omega)) 1
  have wcapacity (hv : valid.value=true) : capacity.work ≤ powerCounterWork base order := by
    have hdegree := (lessCounter_value degree.count (order+1)).mp hv
    apply (powerCounter_work base degree.count).trans
    exact powerCounterWork_exponent_mono base (by omega)
  have wfull (hv : valid.value=true) :
      shape.work+degree.work+valid.work+capacity.work+within.work+split.work+divided.work+primary.work+body.work+safe.work+12 ≤
        workBound base order margin := by
    have wc := wcapacity hv
    unfold workBound headerWork
    omega
  have wmiddle (hv : valid.value=true) :
      shape.work+degree.work+valid.work+capacity.work+within.work+7 ≤ workBound base order margin := by
    have wc := wcapacity hv
    unfold workBound headerWork
    omega
  have wshort : shape.work+degree.work+valid.work+4 ≤ workBound base order margin := by
    unfold workBound headerWork
    omega
  unfold BinaryRectangleDecode.current
  dsimp only
  split_ifs with hv hw ht
  · exact wfull hv
  · exact wfull hv
  · exact wmiddle hv
  · exact wshort

noncomputable section


def workPolynomial (order : ℕ) (base margin : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (headerWork order)+2*Polynomial.C (order+1)*(6*(base+1)^(order+2)+4)+
    (3*base^order+2)+500*(2*base^order+2)^2+
    2*Polynomial.C (order+1)*(500*(base^order+base+2)^2+Polynomial.C ((order+1)*(3*order+5))+5)+
    Polynomial.C order*(Polynomial.C (3*order)+8*base+3*margin+14)+1+12

 theorem workPolynomial_eval (order security : ℕ) (base margin : Polynomial ℕ) :
    (workPolynomial order base margin).eval security = workBound (base.eval security) order (margin.eval security) := by
  simp only [workPolynomial,workBound,divisionWork,safeWork,powerCounterWork,BinaryCounterTupleDecode.workBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  ring

 theorem workBound_mono {base larger margin largerMargin order : ℕ} (hb : base≤larger) (hm : margin≤largerMargin) :
    workBound base order margin ≤ workBound larger order largerMargin := by
  unfold workBound headerWork divisionWork safeWork powerCounterWork BinaryCounterTupleDecode.workBound
  gcongr

 theorem current_polynomial_work (security base order margin : ℕ) (hb : 0<base)
    (row : Fin ((order+1)^2)) (column : Fin (base^order)) (baseBound marginBound : Polynomial ℕ)
    (hbase : base ≤ baseBound.eval security) (hmargin : margin ≤ marginBound.eval security) :
    (BinaryRectangleDecode.current base order margin hb row column).work ≤
      (workPolynomial order baseBound marginBound).eval security := by
  rw [workPolynomial_eval]
  exact (current_work base order margin hb row column).trans (workBound_mono hbase hmargin)

end
end CurrentAFT.BinaryRectangleDecodeResources

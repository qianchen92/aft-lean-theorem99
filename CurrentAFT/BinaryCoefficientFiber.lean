import CurrentAFT.BinaryFirstFamily

/-! # A counted exact-arity guard for concrete local coefficient kernels -/
namespace CurrentAFT.BinaryCoefficientFiber
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter addCounter PublicParameterProgram.modulus

def equal (count target : ℕ) : CountedValue Bool :=
  let next := addCounter target 1
  let below := lessCounter count next.count
  let lower := lessCounter count target
  ⟨below.value && !lower.value,next.work+below.work+lower.work+4⟩

theorem equal_value (count target : ℕ) : (equal count target).value=true ↔ count=target := by
  let below := lessCounter count (addCounter target 1).count
  let lower := lessCounter count target
  have hu : below.value=true ↔ count<target+1 :=
    (lessCounter_value count (addCounter target 1).count).trans (by rw [addCounter_value])
  have hl : lower.value=true ↔ count<target := lessCounter_value count target
  change (below.value && !lower.value)=true ↔ _
  constructor
  · intro h
    have hp : below.value=true ∧ (!lower.value)=true := by simpa only [Bool.and_eq_true] using h
    have hb := hu.mp hp.1
    have hn : ¬count<target := by
      intro hlt
      have hv := hl.mpr hlt
      have hx := hp.2
      simp only [hv,Bool.not_true] at hx
      contradiction
    omega
  · intro h
    have hb := hu.mpr (show count<target+1 by omega)
    have hn : lower.value=false := by
      cases hv : lower.value
      · rfl
      · have hx := hl.mp hv
        omega
    simp only [hb,hn,Bool.not_false,Bool.and_self]

theorem equal_work (count target : ℕ) : (equal count target).work≤6*count+8*target+12 := by
  have hn := addCounter_work target 1
  have hu : (lessCounter count (addCounter target 1).count).work≤3*(count+(target+1))+2 :=
    (lessCounter_work count (addCounter target 1).count).trans_eq (by rw [addCounter_value])
  have hl := lessCounter_work count target
  change _+_+_+4≤_
  omega

def shape (r s primaryDegree bodyDegree : ℕ) : CountedValue Bool :=
  let primary := equal r primaryDegree
  let body := equal s bodyDegree
  ⟨primary.value && body.value,primary.work+body.work+3⟩

theorem shape_value (r s primaryDegree bodyDegree : ℕ) :
    (shape r s primaryDegree bodyDegree).value=true ↔ r=primaryDegree ∧ s=bodyDegree := by
  simp only [shape,Bool.and_eq_true,equal_value]

theorem shape_work (r s primaryDegree bodyDegree : ℕ) :
    (shape r s primaryDegree bodyDegree).work≤6*(r+s)+8*(primaryDegree+bodyDegree)+27 := by
  have hp := equal_work r primaryDegree
  have hb := equal_work s bodyDegree
  change _+_+3≤_
  omega

def current (security r s primaryDegree bodyDegree : ℕ)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) r)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) s)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) primaryDegree→
      Vector (Fin (BinaryFirstInverseProgram.colors security)) bodyDegree→RationalResult) : RationalResult :=
  let test := shape r s primaryDegree bodyDegree
  if h : test.value=true then
    let sizes := (shape_value r s primaryDegree bodyDegree).mp h
    let result := kernel (Vector.cast sizes.1 inputs) (Vector.cast sizes.2 centers)
    ⟨result.data,test.work+result.work+3⟩
  else ⟨zero,test.work+2⟩

theorem current_value (security r s primaryDegree bodyDegree : ℕ)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) r)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) s)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) primaryDegree→
      Vector (Fin (BinaryFirstInverseProgram.colors security)) bodyDegree→RationalResult) :
    (current security r s primaryDegree bodyDegree inputs centers kernel).data.decode=
      if h : r=primaryDegree ∧ s=bodyDegree then
        (kernel (Vector.cast h.1 inputs) (Vector.cast h.2 centers)).data.decode else 0 := by
  by_cases h : (shape r s primaryDegree bodyDegree).value=true
  · simp only [current,dif_pos h,dif_pos ((shape_value _ _ _ _).mp h)]
  · have hn : ¬(r=primaryDegree ∧ s=bodyDegree) := fun hs => h ((shape_value _ _ _ _).mpr hs)
    simp only [current,dif_neg h,dif_neg hn,zero_value]

theorem current_bounds (security r s primaryDegree bodyDegree : ℕ)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) r)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) s)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) primaryDegree→
      Vector (Fin (BinaryFirstInverseProgram.colors security)) bodyDegree→RationalResult)
    (bits budget : ℕ)
    (hh : ∀ inputs centers, HeightBound (kernel inputs centers).data.decode bits)
    (hw : ∀ inputs centers, (kernel inputs centers).work≤budget) :
    HeightBound (current security r s primaryDegree bodyDegree inputs centers kernel).data.decode bits ∧
      (current security r s primaryDegree bodyDegree inputs centers kernel).work≤
        6*(r+s)+8*(primaryDegree+bodyDegree)+budget+30 := by
  have ws := shape_work r s primaryDegree bodyDegree
  by_cases h : (shape r s primaryDegree bodyDegree).value=true
  · have hs := (shape_value _ _ _ _).mp h
    have hk := hh (Vector.cast hs.1 inputs) (Vector.cast hs.2 centers)
    have wk := hw (Vector.cast hs.1 inputs) (Vector.cast hs.2 centers)
    constructor
    · simpa only [current,dif_pos h] using hk
    · rw [current,dif_pos h]
      change (shape r s primaryDegree bodyDegree).work+_+3≤_
      omega
  · constructor
    · simp only [current,dif_neg h,zero_value]
      exact HeightBound.zero.mono (Nat.zero_le _)
    · rw [current,dif_neg h]
      change (shape r s primaryDegree bodyDegree).work+2≤_
      omega

end CurrentAFT.BinaryCoefficientFiber

import AFT.BinaryProtectedWeight
import AFT.BinaryPositiveFinDraw

/-! The protected chart sampler, evaluated by actual binary arithmetic. -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration

def binaryProtectedChartDraw (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    CountedValue (Fin (modulus*(modulus*modulus))) :=
  let raw := protectedChartWeight cutoff modulus boundarySign baselineSign boundary baseline mark steps
  let selected := binaryPositiveFinDraw raw.data bits word
  ⟨⟨selected.value,binaryPositiveFinDraw_lt raw.data bits word⟩,raw.work+selected.work+2⟩

theorem binaryProtectedChartDraw_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    (binaryProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).value=
      finiteAffineChartDraw cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) mark steps bits word := by
  apply Fin.ext
  exact binaryPositiveFinDraw_marked_value _ _ _ _ _ _ _ _ _ _ _ _
    (protectedChartWeight_value cutoff modulus boundarySign baselineSign boundary baseline mark steps) word

def binaryProtectedChartDrawWork (cutoff modulus boundaryBits baselineBits steps bits : ℕ) : ℕ :=
  protectedChartWeightWork cutoff modulus boundaryBits baselineBits steps+
    binaryPositiveDrawWork (modulus*(modulus*modulus)) (protectedChartWeightHeight cutoff modulus steps) bits+2

theorem binaryProtectedChartDraw_work (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    (binaryProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).work ≤
      binaryProtectedChartDrawWork cutoff modulus boundary.length baseline.length steps bits := by
  have hw := protectedChartWeight_work cutoff modulus boundarySign baselineSign boundary baseline mark steps
  have hd := binaryPositiveFinDraw_work
    (protectedChartWeight cutoff modulus boundarySign baselineSign boundary baseline mark steps).data
    (protectedChartWeightHeight cutoff modulus steps) bits
    (protectedChartWeight_height cutoff modulus boundarySign baselineSign boundary baseline mark steps) word
  unfold binaryProtectedChartDraw binaryProtectedChartDrawWork
  dsimp only
  omega

end AFT.BinaryArithmetic

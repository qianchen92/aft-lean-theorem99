import AFT.BinaryProtectedChartDraw
import AFT.BinaryLegalChart

/-! The full support-preserving protected sampler, with real legal-mask scans. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration

def binarySafeProtectedChartDraw (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    CountedValue (Fin (modulus*(modulus*modulus))) :=
  let raw := binaryProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word
  let metadata := protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark
  let selected := binaryLegalChartIndex metadata.value.legal raw.value
  ⟨selected.value,raw.work+metadata.work+selected.work+3⟩

theorem binarySafeProtectedChartDraw_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    (binarySafeProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).value=
      safeFiniteAffineChartDraw cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) mark steps bits word := by
  unfold binarySafeProtectedChartDraw
  dsimp only
  rw [binaryLegalChartIndex_value _ _ (finiteAffineLegalSet cutoff modulus
    (signedValue boundarySign boundary) (signedValue baselineSign baseline) mark)]
  · rw [binaryProtectedChartDraw_value]
    rfl
  · intro point
    rw [protectedMetadata_legal]
    simp only [Bool.or_eq_true,finiteAffineLegalSet,Finset.mem_union]
    rw [protectedMetadata_safe,protectedMetadata_fiber]

def binarySafeProtectedChartWork (cutoff modulus boundaryBits baselineBits steps bits : ℕ) : ℕ :=
  binaryProtectedChartDrawWork cutoff modulus boundaryBits baselineBits steps bits+
    protectedMetadataWork cutoff modulus boundaryBits baselineBits+7*(modulus*(modulus*modulus))+11

theorem binarySafeProtectedChartDraw_work (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool)
    (mark : Fin modulus) (steps bits : ℕ)
    (word : Fin (bits+modulus*(modulus*modulus)+1) → Fin 2) :
    (binarySafeProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).work ≤
      binarySafeProtectedChartWork cutoff modulus boundary.length baseline.length steps bits := by
  have hd := binaryProtectedChartDraw_work cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word
  have hm := protectedMetadata_work cutoff modulus boundarySign baselineSign boundary baseline mark
  have hs := binaryLegalChartIndex_work
    (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.legal
    (binaryProtectedChartDraw cutoff modulus boundarySign baselineSign boundary baseline mark steps bits word).value
  unfold binarySafeProtectedChartDraw binarySafeProtectedChartWork
  dsimp only
  omega

end AFT.BinaryArithmetic

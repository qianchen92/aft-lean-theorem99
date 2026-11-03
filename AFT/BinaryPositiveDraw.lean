import AFT.BinaryFiniteDraw
import AFT.BinaryPositiveNormalize
import AFT.BinaryLoopControl

/-! # Positive finite sampling, including guard-counter construction -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics BetaReference RationalBits
open scoped BigOperators

def binaryPositiveDraw {count : ℕ} (raw : Vector RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) : CountedNatural :=
  let normalized := binaryPositiveNormalize raw
  let guard := addCounter bits (count+1)
  let shiftedWord : Fin (guard.count+1) → Fin 2 :=
    fun index => word (Fin.cast (by rw [addCounter_value]) index)
  let selected := binaryRationalDraw normalized.data guard.count.succ shiftedWord
  ⟨selected.value,normalized.work+guard.work+selected.work+3⟩

theorem binaryPositiveDraw_value {count : ℕ} (raw : Vector RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    (binaryPositiveDraw raw bits word).value=
      (positiveNormalizeDraw (fun index => (raw.get index).decode) bits word).val := by
  have hv : (fun index => ((binaryPositiveNormalize raw).data.get index).decode)=
      positiveWeightProgram (fun index => (raw.get index).decode) :=
    funext (binaryPositiveNormalize_value raw)
  have hn : ∀ index,0≤ ((binaryPositiveNormalize raw).data.get index).decode := by
    intro index
    rw [binaryPositiveNormalize_value]
    exact positiveWeightProgram_nonneg _ index
  have hs : ∑ index,((binaryPositiveNormalize raw).data.get index).decode=1 := by
    simpa only [binaryPositiveNormalize_value] using positiveWeightProgram_sum (fun index => (raw.get index).decode)
  change (binaryRationalDraw _ _ _).value=_
  rw [binaryRationalDraw_cast]
  rw [binaryRationalDraw_value _ hn hs]
  unfold positiveNormalizeDraw
  simp only [RationalFiniteQuantization.draw,FiniteTicketSampler.drawBitTable,
    FiniteTicketSampler.drawFin,Fin.val_cast]
  rw [hv]

def binaryPositiveDrawWork (count height bits : ℕ) : ℕ :=
  binaryPositiveNormalizeWork count height+2*bits+
    binaryRationalDrawWork count (height+count*(height+1)) (bits+count+1)+4

theorem binaryPositiveDraw_work {count : ℕ} (raw : Vector RationalBits (count+1)) (height bits : ℕ)
    (hh : ∀ index,HeightBound (raw.get index).decode height)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    (binaryPositiveDraw raw bits word).work≤ binaryPositiveDrawWork (count+1) height bits := by
  have wn := binaryPositiveNormalize_work raw height hh
  have hn := binaryPositiveNormalize_height raw height hh
  have ws := binaryRationalDraw_work (binaryPositiveNormalize raw).data
    (height+(count+1)*(height+1)) (bits+(count+1)+1) hn word
  unfold binaryPositiveDraw
  dsimp only
  rw [binaryRationalDraw_cast,addCounter_work]
  unfold binaryPositiveDrawWork
  omega

end AFT.BinaryArithmetic

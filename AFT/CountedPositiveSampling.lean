import AFT.RationalPositiveNormalizeHeight
import AFT.PermutationProgramCost

/-! # Materialized positive normalization and dyadic ticket sampling

Every rational weight and floor count is stored once. The counter counts
rational arithmetic, floor divisions, integer arithmetic and comparisons;
binary operand lengths are supplied separately by the height bounds.
-/
namespace AFT.RationalNumerics
open BetaReference PermutationProgram
open scoped BigOperators

structure NormalizedRationalArray (count : ℕ) where
  value : Vector ℚ (count+1)
  work : ℕ

def countedPositiveNormalize {count : ℕ} (raw : Vector ℚ (count+1)) : NormalizedRationalArray count :=
  let positive := Vector.ofFn (fun index => max 0 (raw.get index))
  let total := ∑ index,positive.get index
  let weights := if total=0 then Vector.ofFn (fun index => if index=0 then 1 else 0)
    else Vector.ofFn (fun index => positive.get index/total)
  ⟨weights,3*(count+1)+1⟩

 theorem countedPositiveNormalize_value {count : ℕ} (raw : Vector ℚ (count+1)) (index : Fin (count+1)) :
    (countedPositiveNormalize raw).value.get index=positiveWeightProgram raw.get index := by
  simp only [countedPositiveNormalize,Vector.get_ofFn,positiveWeightProgram,positiveNormalizerProgram,positivePartProgram]
  split_ifs <;> simp_all [Vector.get_ofFn]

@[simp] theorem countedPositiveNormalize_work {count : ℕ} (raw : Vector ℚ (count+1)) :
    (countedPositiveNormalize raw).work=3*(count+1)+1 := rfl

/-- No call to real floor occurs. All floor operands are explicit rationals. -/
def countedRationalDraw {count : ℕ} (weights : Vector ℚ (count+1)) (bits : ℕ)
    (word : Fin bits → Fin 2) : CountedNatural :=
  let tickets := powerTwo bits
  let floored := Vector.ofFn (fun index => ⌊(tickets.value : ℚ)*weights.get index⌋₊)
  let deficit := tickets.value-(∑ index,floored.get index)
  let counts := List.ofFn (fun index => floored.get index+if index=0 then deficit else 0)
  let ticket := bitValue bits word
  let selected := countedBucket counts ticket.value
  ⟨selected.value,tickets.work+5*(count+1)+1+ticket.work+selected.work⟩

 theorem countedRationalDraw_value {count : ℕ} (weights : Vector ℚ (count+1))
    (hnonneg : ∀ index,0≤weights.get index) (hsum : ∑ index,weights.get index=1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    (countedRationalDraw weights bits word).value=(RationalFiniteQuantization.draw weights.get hnonneg hsum bits word).val := by
  simp only [countedRationalDraw,powerTwo_value,Vector.get_ofFn,bitValue_value,countedBucket_value,
    RationalFiniteQuantization.draw,FiniteTicketSampler.drawBitTable,FiniteTicketSampler.drawFin,Fin.val_cast]
  rfl

 theorem countedRationalDraw_work {count : ℕ} (weights : Vector ℚ (count+1))
    (bits : ℕ) (word : Fin bits → Fin 2) :
    (countedRationalDraw weights bits word).work≤3*bits+8*(count+1)+1 := by
  have hh := countedBucket_work
    (List.ofFn (fun index : Fin (count+1) => ⌊((2^bits : ℕ) : ℚ)*weights.get index⌋₊+
      if index=0 then 2^bits-(∑i,⌊((2^bits : ℕ) : ℚ)*weights.get i⌋₊) else 0)) (bitValue bits word).value
  simp only [List.length_ofFn] at hh
  simp only [countedRationalDraw,powerTwo_value,powerTwo_work,Vector.get_ofFn,bitValue_work]
  omega

 def countedPositiveDraw {count : ℕ} (raw : Vector ℚ (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) : CountedNatural :=
  let normalized := countedPositiveNormalize raw
  let selected := countedRationalDraw normalized.value (bits+(count+1)+1) word
  ⟨selected.value,normalized.work+selected.work⟩

 theorem countedPositiveDraw_value {count : ℕ} (raw : Vector ℚ (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    (countedPositiveDraw raw bits word).value=(positiveNormalizeDraw raw.get bits word).val := by
  have hv : (countedPositiveNormalize raw).value.get=positiveWeightProgram raw.get :=
    funext (countedPositiveNormalize_value raw)
  have hh := countedRationalDraw_value (countedPositiveNormalize raw).value
    (by rw [hv];exact positiveWeightProgram_nonneg raw.get)
    (by rw [hv];exact positiveWeightProgram_sum raw.get) (bits+(count+1)+1) word
  change (countedRationalDraw (countedPositiveNormalize raw).value (bits+(count+1)+1) word).value=_
  rw [hh]
  unfold positiveNormalizeDraw
  congr 2

 theorem countedPositiveDraw_work {count : ℕ} (raw : Vector ℚ (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    (countedPositiveDraw raw bits word).work≤3*bits+14*(count+1)+5 := by
  have hh := countedRationalDraw_work (countedPositiveNormalize raw).value (bits+(count+1)+1) word
  simp only [countedPositiveDraw,countedPositiveNormalize_work]
  omega

end AFT.RationalNumerics

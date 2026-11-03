import AFT.BinaryUniformDraw
import AFT.PermutationProgram

/-! The actual finite-bit choice used at a permutation insertion stage. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics RationalBits
open scoped BigOperators

def binaryPermutationChoice (size bits : ℕ) (word : Fin bits → Fin 2) : CountedValue (Fin (size+1)) :=
  let encoded := ofCounter size.succ
  let probability := inverse encoded.data
  let weights := Vector.replicate size.succ probability.data
  let selected := binaryRationalDraw weights bits word
  have hv : (fun index => (weights.get index).decode)=PermutationProgram.choiceWeight size := by
    funext index
    simp only [weights,probability,encoded,Vector.get_replicate,inverse_value,ofCounter_value,
      PermutationProgram.choiceWeight,Nat.succ_eq_add_one]
  have hn : ∀ index,0 ≤ (weights.get index).decode := by
    intro index
    change 0 ≤ (fun index => (weights.get index).decode) index
    rw [hv]
    exact PermutationProgram.choiceWeight_nonneg size index
  have hs : (∑ index,(weights.get index).decode)=1 := by
    rw [hv];exact PermutationProgram.choiceWeight_sum size
  have hlt : selected.value < size+1 := by
    rw [binaryRationalDraw_value weights hn hs bits word]
    exact Fin.isLt _
  ⟨⟨selected.value,hlt⟩,encoded.work+probability.work+size.succ+selected.work+4⟩

theorem binaryPermutationChoice_value (size bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryPermutationChoice size bits word).value=PermutationProgram.choiceDraw size bits word := by
  let weights := Vector.replicate size.succ (inverse (ofCounter size.succ).data).data
  have hv : (fun index => (weights.get index).decode)=PermutationProgram.choiceWeight size := by
    funext index
    simp only [weights,Vector.get_replicate,inverse_value,ofCounter_value,
      PermutationProgram.choiceWeight,Nat.succ_eq_add_one]
  have hn : ∀ index,0 ≤ (weights.get index).decode := by
    intro index
    change 0 ≤ (fun index => (weights.get index).decode) index
    rw [hv]
    exact PermutationProgram.choiceWeight_nonneg size index
  have hs : (∑ index,(weights.get index).decode)=1 := by
    rw [hv];exact PermutationProgram.choiceWeight_sum size
  apply Fin.ext
  change (binaryRationalDraw weights bits word).value=_
  rw [binaryRationalDraw_value weights hn hs bits word]
  simp only [hv,PermutationProgram.choiceDraw]

def binaryPermutationChoiceWork (size bits : ℕ) : ℕ :=
  60*(size+2)^2+primitiveWorkBound (size+1)+(size+1)+binaryRationalDrawWork (size+1) (size+1) bits+4

theorem binaryPermutationChoice_work (size bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryPermutationChoice size bits word).work ≤ binaryPermutationChoiceWork size bits := by
  have he := ofCounter_work size.succ
  have hi := inverse_work (ofCounter size.succ).data size.succ
  have hh : HeightBound (inverse (ofCounter size.succ).data).data.decode size.succ := by
    rw [inverse_value,ofCounter_value]
    exact (HeightBound.nat_coarse _).inv
  have hd := binaryRationalDraw_work (Vector.replicate size.succ (inverse (ofCounter size.succ).data).data)
    size.succ bits (by intro index;simpa only [Vector.get_replicate] using hh) word
  unfold binaryPermutationChoice binaryPermutationChoiceWork
  dsimp only
  simp only [Nat.succ_eq_add_one,Nat.add_assoc,show 1+1=2 by rfl] at he hi hd ⊢
  omega

theorem binaryPermutationChoiceWork_mono {s t b e : ℕ} (hs : s ≤ t) (hb : b ≤ e) :
    binaryPermutationChoiceWork s b ≤ binaryPermutationChoiceWork t e := by
  have hd := binaryRationalDrawWork_mono (Nat.add_le_add_right hs 1) (Nat.add_le_add_right hs 1) hb
  unfold binaryPermutationChoiceWork primitiveWorkBound
  gcongr

end AFT.BinaryArithmetic

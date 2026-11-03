import AFT.BinaryTicketTable
import AFT.BinaryChartArray
import AFT.RationalFiniteQuantization

/-! # Finite rational sampling by actual binary operations

The stored probability array is rounded once, the leftover tickets are assigned
to its first entry, and bucket selection reads the supplied fair-bit tape.
Even an exponentially large ticket stays a list of bits throughout execution.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics BetaReference
open scoped BigOperators

private theorem supplementFirst_ofFn {count : ℕ} (weights : Fin (count+1) → ℕ) (extra : ℕ) :
    supplementFirst extra (List.ofFn weights)=
      List.ofFn (fun index => weights index+if index=0 then extra else 0) := by
  rw [List.ofFn_succ,List.ofFn_succ]
  simp only [supplementFirst,ite_true,Fin.succ_ne_zero,ite_false,Nat.add_zero]

theorem ticketTable_ofFn_counts {count : ℕ} (weights : Vector RationalBits (count+1))
    (hnonneg : ∀ index,0≤ (weights.get index).decode)
    (hsum : ∑ index,(weights.get index).decode=1) (bits : ℕ) :
    (ticketTable (List.ofFn weights.get) bits).data.map value=
      List.ofFn (RationalFiniteQuantization.counts (fun index => (weights.get index).decode) (2^bits)) := by
  have hb := RationalFiniteQuantization.floorTotal_le (fun index => (weights.get index).decode)
    hnonneg hsum (2^bits)
  simp only [RationalFiniteQuantization.floorTotal,RationalFiniteQuantization.floorCount,
    Nat.cast_pow,Nat.cast_ofNat] at hb
  rw [ticketTable_value _ bits (by simpa only [List.map_ofFn,List.sum_ofFn] using hb)]
  simp only [List.map_ofFn]
  rw [supplementFirst_ofFn]
  apply congrArg List.ofFn
  funext index
  simp only [RationalFiniteQuantization.counts,RationalFiniteQuantization.floorCount,
    RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,
    Function.comp_apply,Nat.cast_pow,Nat.cast_ofNat,List.sum_ofFn]

/-- Array materialization, all binary arithmetic, and all tape reads are charged. -/
def binaryRationalDraw {count : ℕ} (weights : Vector RationalBits (count+1))
    (bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let table := ticketTable (List.ofFn weights.get) bits
  let ticket := readBitTape bits word
  let selected := binaryBucket table.data ticket.digits
  ⟨selected.value,table.work+ticket.work+selected.work+2*(count+1)+2⟩

theorem binaryRationalDraw_cast {count : ℕ} (weights : Vector RationalBits (count+1))
    (bits other : ℕ) (heq : bits=other) (word : Fin other → Fin 2) :
    binaryRationalDraw weights bits (fun index => word (Fin.cast heq index))=
      binaryRationalDraw weights other word := by
  subst other
  rfl

theorem binaryRationalDraw_value {count : ℕ} (weights : Vector RationalBits (count+1))
    (hnonneg : ∀ index,0≤ (weights.get index).decode)
    (hsum : ∑ index,(weights.get index).decode=1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryRationalDraw weights bits word).value=
      (RationalFiniteQuantization.draw (fun index => (weights.get index).decode)
        hnonneg hsum bits word).val := by
  have hb := RationalFiniteQuantization.floorTotal_le (fun index => (weights.get index).decode)
    hnonneg hsum (2^bits)
  simp only [RationalFiniteQuantization.floorTotal,RationalFiniteQuantization.floorCount,
    Nat.cast_pow,Nat.cast_ofNat] at hb
  have ht := ticketTable_value (List.ofFn weights.get) bits (by
    simpa only [List.map_ofFn,List.sum_ofFn] using hb)
  simp only [List.map_ofFn] at ht
  rw [supplementFirst_ofFn] at ht
  simp only [binaryRationalDraw,binaryBucket_value,readBitTape_value,ht,
    RationalFiniteQuantization.draw,FiniteTicketSampler.drawBitTable,FiniteTicketSampler.drawFin,
    Fin.val_cast,RationalFiniteQuantization.counts,RationalFiniteQuantization.floorCount,
    RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,
    List.sum_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext index
  simp only [RationalFiniteQuantization.counts,RationalFiniteQuantization.floorCount,
    RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,
    Function.comp_apply,Nat.cast_pow,Nat.cast_ofNat]

def binaryRationalDrawWork (count height bits : ℕ) : ℕ :=
  ticketTableWork count height bits+3*bits+
    count*(10*ticketTableDigitBound count height bits+5)+2*count+6

theorem binaryRationalDraw_work {count : ℕ} (weights : Vector RationalBits (count+1))
    (height bits : ℕ) (hh : ∀ index,HeightBound (weights.get index).decode height)
    (word : Fin bits → Fin 2) :
    (binaryRationalDraw weights bits word).work≤ binaryRationalDrawWork (count+1) height bits := by
  have hi : ∀ input∈List.ofFn weights.get,HeightBound input.decode height := by
    intro input hin
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hin
    exact hh index
  have wt := ticketTable_work (List.ofFn weights.get) height bits hi
  have ht := ticketTable_digits (List.ofFn weights.get) height bits hi
  simp only [List.length_ofFn] at wt ht
  have wr := binaryBucket_work (ticketTable (List.ofFn weights.get) bits).data
    (readBitTape bits word).digits (ticketTableDigitBound (count+1) height bits) ht (by
      rw [readBitTape_length];unfold ticketTableDigitBound;nlinarith)
  rw [ticketTable_length,List.length_ofFn] at wr
  simp only [binaryRationalDraw,binaryRationalDrawWork,readBitTape_work]
  omega

end AFT.BinaryArithmetic

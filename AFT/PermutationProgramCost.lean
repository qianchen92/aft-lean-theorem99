import AFT.PermutationProgram
import AFT.BetaCountedSearch
import AFT.RationalHeight

/-! # Counted integer implementation of permutation insertion choices

The count table is computed using one integer quotient and one remainder.
Earlier permutation stages are stored, not sampled again. Arithmetic work
and all ticket sizes have explicit bounds; no list of permutations is built.
-/
namespace AFT.PermutationProgram
open BetaReference
open scoped BigOperators

/-- Integer-only form of the quantized uniform choice table. -/
def uniformCounts (size tickets : ℕ) (index : Fin (size+1)) : ℕ :=
  tickets/(size+1)+if index=0 then tickets%(size+1) else 0

theorem uniformCounts_eq (size tickets : ℕ) :
    uniformCounts size tickets=RationalFiniteQuantization.counts (choiceWeight size) tickets := by
  have hf (index : Fin (size+1)) :
      RationalFiniteQuantization.floorCount (choiceWeight size) tickets index=tickets/(size+1) := by
    simp only [RationalFiniteQuantization.floorCount,choiceWeight,← div_eq_mul_inv,Nat.floor_div_natCast,Nat.floor_natCast]
  have hd : RationalFiniteQuantization.deficit (choiceWeight size) tickets=tickets%(size+1) := by
    simp only [RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,hf,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change tickets-(size+1)*(tickets/(size+1))=tickets%(size+1)
    have hh := Nat.mod_add_div tickets (size+1)
    omega
  funext index
  simp only [uniformCounts,RationalFiniteQuantization.counts,hf,hd]

def powerTwo : ℕ → CountedNatural
  | 0 => ⟨1,0⟩
  | bits+1 => let previous := powerTwo bits; ⟨2*previous.value,previous.work+1⟩

@[simp] theorem powerTwo_value (bits : ℕ) : (powerTwo bits).value=2^bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwo,ih,pow_succ']

@[simp] theorem powerTwo_work (bits : ℕ) : (powerTwo bits).work=bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [powerTwo,ih]

def bitValue : (bits : ℕ) → (Fin bits → Fin 2) → CountedNatural
  | 0,_ => ⟨0,0⟩
  | bits+1,word =>
      let previous := bitValue bits (Fin.tail word)
      ⟨(word 0).val+2*previous.value,previous.work+2⟩

theorem bitValue_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitValue bits word).value=(FiniteTicketSampler.bitTicket bits word).val := by
  rw [FiniteTicketSampler.bitTicket_value]
  induction bits with
  | zero => simp [bitValue]
  | succ bits ih =>
    simp only [bitValue,ih,Fin.sum_univ_succ,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    simp only [Fin.tail]
    ring

@[simp] theorem bitValue_work (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitValue bits word).work=2*bits := by
  induction bits with
  | zero => simp [bitValue]
  | succ bits ih => simp only [bitValue,ih]; omega

def countedBucket : List ℕ → ℕ → CountedNatural
  | [],_ => ⟨0,0⟩
  | count::rest,ticket =>
      if ticket<count then ⟨0,1⟩ else
        let next := countedBucket rest (ticket-count)
        ⟨1+next.value,next.work+3⟩

theorem countedBucket_value (counts : List ℕ) (ticket : ℕ) :
    (countedBucket counts ticket).value=FiniteTicketSampler.bucket counts ticket := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons count rest ih => simp only [countedBucket,FiniteTicketSampler.bucket];split_ifs <;> simp [ih]

theorem countedBucket_work (counts : List ℕ) (ticket : ℕ) :
    (countedBucket counts ticket).work≤3*counts.length := by
  induction counts generalizing ticket with
  | nil => simp [countedBucket]
  | cons count rest ih =>
    simp only [countedBucket,List.length_cons]
    split_ifs
    · dsimp only
      omega
    · dsimp only
      have hh := ih (ticket-count)
      omega

/-- Quotient/remainder and the dyadic ticket are materialized once. Each
list entry costs a comparison and an addition. -/
def countedChoice (size bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let tickets := powerTwo bits
  let ticket := bitValue bits word
  let quotient := tickets.value/(size+1)
  let remainder := tickets.value%(size+1)
  let counts := List.ofFn (fun index : Fin (size+1) => quotient+if index=0 then remainder else 0)
  let selected := countedBucket counts ticket.value
  ⟨selected.value,tickets.work+ticket.work+2*(size+1)+selected.work+3⟩

theorem countedChoice_value (size bits : ℕ) (word : Fin bits → Fin 2) :
    (countedChoice size bits word).value=(choiceDraw size bits word).val := by
  simp only [countedChoice,powerTwo_value,bitValue_value,countedBucket_value]
  change FiniteTicketSampler.bucket (List.ofFn (uniformCounts size (2^bits))) _=_
  rw [uniformCounts_eq]
  rfl

theorem countedChoice_work (size bits : ℕ) (word : Fin bits → Fin 2) :
    (countedChoice size bits word).work≤3*bits+5*(size+1)+3 := by
  have hh := countedBucket_work (List.ofFn (uniformCounts size (2^bits))) (bitValue bits word).value
  simp only [List.length_ofFn] at hh
  simp only [countedChoice,powerTwo_value,powerTwo_work,bitValue_work]
  change bits+2*bits+2*(size+1)+(countedBucket (List.ofFn (uniformCounts size (2^bits)))
    (bitValue bits word).value).work+3≤_
  omega

def countedChoiceFin (size bits : ℕ) (word : Fin bits → Fin 2) : Fin (size+1) :=
  ⟨(countedChoice size bits word).value,by rw [countedChoice_value];exact (choiceDraw size bits word).isLt⟩

@[simp] theorem countedChoiceFin_eq (size bits : ℕ) (word : Fin bits → Fin 2) :
    countedChoiceFin size bits word=choiceDraw size bits word := Fin.ext (countedChoice_value size bits word)

structure CountedPermutation (count : ℕ) where
  value : Equiv.Perm (Fin count)
  work : ℕ

def countedRows (bits : ℕ) : (count : ℕ) → (Fin count → Fin bits → Fin 2) → CountedPermutation count
  | 0,_ => ⟨Equiv.refl _,0⟩
  | count+1,word =>
      let choice := countedChoice count bits (word 0)
      let previous := countedRows bits count (Fin.tail word)
      ⟨Equiv.Perm.decomposeFin.symm (⟨choice.value,by rw [countedChoice_value];exact (choiceDraw count bits (word 0)).isLt⟩,
        previous.value),choice.work+previous.work+1⟩

theorem countedRows_value (count bits : ℕ) (word : Fin count → Fin bits → Fin 2) :
    (countedRows bits count word).value=rows bits count word := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [countedRows,rows,ih]
    congr 2
    exact Fin.ext (countedChoice_value count bits (word 0))

theorem countedRows_work (count bits : ℕ) (word : Fin count → Fin bits → Fin 2) :
    (countedRows bits count word).work≤count*(3*bits+5*count+4) := by
  induction count with
  | zero => simp [countedRows]
  | succ count ih =>
    have hc := countedChoice_work count bits (word 0)
    have hp := ih (Fin.tail word)
    simp only [countedRows]
    nlinarith

theorem choice_table_binary_size (size bits : ℕ) (index : Fin (size+1)) :
    (uniformCounts size (2^bits) index).size≤bits+1 := by
  rw [uniformCounts_eq]
  exact (Nat.size_le_size (RationalFiniteQuantization.count_le_tickets (choiceWeight size)
    (choiceWeight_nonneg size) (choiceWeight_sum size) (2^bits) index)).trans_eq Nat.size_pow

/-- Every subtraction made by the bucket scan stays in the original
nonnegative ticket range. -/
theorem bucket_remaining_binary_size (bits ticket removed : ℕ) (ht : ticket≤2^bits) :
    (ticket-removed).size≤bits+1 :=
  (Nat.size_le_size ((Nat.sub_le _ _).trans ht)).trans_eq Nat.size_pow

end AFT.PermutationProgram

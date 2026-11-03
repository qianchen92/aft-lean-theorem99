import AFT.BinaryBitTape

/-! # Binary accumulation and bucket selection

Tickets and table counts remain binary throughout, including subtraction
on a rejected bucket. Only the polynomially bounded output index is unary.
-/
namespace AFT.BinaryArithmetic
open BetaReference

def binaryBucket : List (List Bool) → List Bool → CountedNatural
  | [],_ => ⟨0,2⟩
  | head::tail,ticket =>
      let comparison := subtract false ticket head
      if comparison.borrow then ⟨0,comparison.work+3⟩ else
        let next := binaryBucket tail comparison.digits
        ⟨next.value.succ,comparison.work+next.work+3⟩

theorem binaryBucket_value (counts : List (List Bool)) (ticket : List Bool) :
    (binaryBucket counts ticket).value=FiniteTicketSampler.bucket (counts.map value) (value ticket) := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons head tail ih =>
      have hb := subtract_borrow ticket head
      simp only [binaryBucket,List.map_cons,FiniteTicketSampler.bucket]
      split <;> rename_i hc
      · rw [if_pos (hb.mp hc)]
      · have hh : value head≤ value ticket := Nat.le_of_not_gt (fun hl => hc (hb.mpr hl))
        rw [if_neg (by omega),ih,subtract_value ticket head hh]
        dsimp only
        omega

theorem binaryBucket_work (counts : List (List Bool)) (ticket : List Bool) (bits : ℕ)
    (hc : ∀ digits∈counts,digits.length≤ bits) (ht : ticket.length≤ bits) :
    (binaryBucket counts ticket).work≤ counts.length*(10*bits+5)+2 := by
  induction counts generalizing ticket with
  | nil => simp only [binaryBucket,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons head tail ih =>
      have hh : head.length≤ bits := hc _ (List.mem_cons_self ..)
      have hm : max ticket.length head.length≤ bits := by omega
      have hn : (subtract false ticket head).digits.length≤ bits := by rw [subtract_length];exact hm
      have hw := ih (subtract false ticket head).digits
        (fun digits hd => hc digits (List.mem_cons_of_mem _ hd)) hn
      simp only [binaryBucket,List.length_cons]
      split <;> simp only [subtract_work] <;> nlinarith

def sumDigits : List (List Bool) → Result
  | [] => ⟨[],2⟩
  | head::tail =>
      let previous := sumDigits tail
      let next := add false head previous.digits
      ⟨next.digits,previous.work+next.work+2⟩

theorem sumDigits_value (counts : List (List Bool)) : value (sumDigits counts).digits=(counts.map value).sum := by
  induction counts with
  | nil => rfl
  | cons head tail ih => simp only [sumDigits,add_value,ih,Bool.toNat_false,Nat.add_zero,List.map_cons,List.sum_cons]

theorem sumDigits_length (counts : List (List Bool)) (bits : ℕ)
    (hc : ∀ digits∈counts,digits.length≤ bits) :
    (sumDigits counts).digits.length≤ counts.length*(bits+1) := by
  induction counts with
  | nil => simp only [sumDigits,List.length_nil,Nat.zero_mul,le_refl]
  | cons head tail ih =>
      have hh := hc head (List.mem_cons_self ..)
      have ht := ih (fun digits hd => hc digits (List.mem_cons_of_mem _ hd))
      have hl := add_length head (sumDigits tail).digits false
      simp only [sumDigits,List.length_cons]
      have hm : max head.length (sumDigits tail).digits.length≤ tail.length*(bits+1)+bits := by
        apply max_le
        · exact hh.trans (Nat.le_add_left _ _)
        · exact ht.trans (Nat.le_add_right _ _)
      nlinarith

def sumDigitsWork (count bits : ℕ) : ℕ := count*(10*(count+1)*(bits+1)+4)+2

theorem sumDigits_work (counts : List (List Bool)) (bits : ℕ)
    (hc : ∀ digits∈counts,digits.length≤ bits) : (sumDigits counts).work≤ sumDigitsWork counts.length bits := by
  induction counts with
  | nil => simp only [sumDigits,sumDigitsWork,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons head tail ih =>
      have hh := hc head (List.mem_cons_self ..)
      have htail : ∀ digits∈tail,digits.length≤ bits := fun digits hd => hc digits (List.mem_cons_of_mem _ hd)
      have hw := ih htail
      have hl := sumDigits_length tail bits htail
      have hm : max head.length (sumDigits tail).digits.length≤ (tail.length+1)*(bits+1) := by
        apply max_le <;> nlinarith
      simp only [sumDigits,add_work,sumDigitsWork,List.length_cons] at hw ⊢
      nlinarith

end AFT.BinaryArithmetic

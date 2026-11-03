import AFT.BinaryTicketBucket
import AFT.BinaryDyadicFloor

/-! # Actual binary ticket-table preparation

Each weight is rounded once. The remaining tickets are computed by actual
binary subtraction and added to the first table entry, exactly as in the
support-preserving rational quantization program.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

structure DigitTableResult where
  data : List (List Bool)
  work : ℕ

def floorTable (weights : List RationalBits) (bits : ℕ) : DigitTableResult :=
  match weights with
  | [] => ⟨[],2⟩
  | head::tail =>
      let current := head.dyadicFloor bits
      let rest := floorTable tail bits
      ⟨current.digits::rest.data,current.work+rest.work+3⟩

theorem floorTable_value (weights : List RationalBits) (bits : ℕ) :
    (floorTable weights bits).data.map value=weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊) := by
  induction weights with
  | nil => rfl
  | cons head tail ih => simp only [floorTable,List.map_cons,RationalBits.dyadicFloor_value,ih]

theorem floorTable_length (weights : List RationalBits) (bits : ℕ) :
    (floorTable weights bits).data.length=weights.length := by
  induction weights with
  | nil => rfl
  | cons head tail ih => simp only [floorTable,List.length_cons,ih]

theorem floorTable_digits (weights : List RationalBits) (height bits : ℕ)
    (hh : ∀ input∈weights,HeightBound input.decode height) :
    ∀ digits∈(floorTable weights bits).data,digits.length≤ bits+height+1 := by
  induction weights with
  | nil => simp only [floorTable,List.not_mem_nil,false_implies,implies_true]
  | cons head tail ih =>
      intro digits hd
      simp only [floorTable,List.mem_cons] at hd
      rcases hd with rfl|hd
      · exact RationalBits.dyadicFloor_height head height bits (hh _ (List.mem_cons_self ..))
      · exact ih (fun input hi => hh input (List.mem_cons_of_mem _ hi)) digits hd

theorem floorTable_work (weights : List RationalBits) (height bits : ℕ)
    (hh : ∀ input∈weights,HeightBound input.decode height) :
    (floorTable weights bits).work≤ weights.length*(RationalBits.dyadicFloorWork height bits+3)+2 := by
  induction weights with
  | nil => simp only [floorTable,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons head tail ih =>
      have hw := RationalBits.dyadicFloor_work head height bits (hh _ (List.mem_cons_self ..))
      have ht := ih (fun input hi => hh input (List.mem_cons_of_mem _ hi))
      simp only [floorTable,List.length_cons]
      nlinarith

def supplementFirst (extra : ℕ) : List ℕ → List ℕ
  | [] => []
  | head::tail => (head+extra)::tail

def ticketTable (weights : List RationalBits) (bits : ℕ) : DigitTableResult :=
  let floored := floorTable weights bits
  let total := sumDigits floored.data
  let tickets := powerTwoDigits bits
  let deficit := subtract false tickets.digits total.digits
  match floored.data with
  | [] => ⟨[],floored.work+total.work+tickets.work+deficit.work+3⟩
  | head::tail =>
      let first := add false head deficit.digits
      ⟨first.digits::tail,floored.work+total.work+tickets.work+deficit.work+first.work+4⟩

theorem ticketTable_value (weights : List RationalBits) (bits : ℕ)
    (hbound : (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum≤ 2^bits) :
    (ticketTable weights bits).data.map value=
      supplementFirst (2^bits-(weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum)
        (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)) := by
  have ht := floorTable_value weights bits
  have hv : value (sumDigits (floorTable weights bits).data).digits=
      (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum := by rw [sumDigits_value,ht]
  have hd := subtract_value (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits
    (by rw [powerTwoDigits_value,hv];exact hbound)
  rw [powerTwoDigits_value,hv] at hd
  unfold ticketTable
  dsimp only
  split <;> rename_i he
  · rw [he] at ht
    simp only [List.map_nil] at ht
    rw [← ht]
    rfl
  · rw [he] at ht
    rw [← ht]
    simp only [List.map_cons,supplementFirst,add_value,Bool.toNat_false,Nat.add_zero]
    congr 2
    simpa only [← ht] using hd

theorem ticketTable_length (weights : List RationalBits) (bits : ℕ) :
    (ticketTable weights bits).data.length=weights.length := by
  have hl := floorTable_length weights bits
  unfold ticketTable
  dsimp only
  split <;> rename_i he <;> rw [he] at hl <;> simpa only [List.length_cons,List.length_nil] using hl

def ticketTableDigitBound (count height bits : ℕ) : ℕ := (count+1)*(bits+height+2)+1

theorem ticketTable_digits (weights : List RationalBits) (height bits : ℕ)
    (hh : ∀ input∈weights,HeightBound input.decode height) :
    ∀ digits∈(ticketTable weights bits).data,digits.length≤ ticketTableDigitBound weights.length height bits := by
  have hf := floorTable_digits weights height bits hh
  have hs := sumDigits_length (floorTable weights bits).data (bits+height+1) hf
  rw [floorTable_length] at hs
  have hd := subtract_length (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits false
  rw [powerTwoDigits_length] at hd
  unfold ticketTable
  dsimp only
  split <;> rename_i he
  · simp only [List.not_mem_nil,false_implies,implies_true]
  · rename_i head tail
    intro digits hg
    simp only [List.mem_cons] at hg
    have hh' : _ := hf _ (by rw [he];exact List.mem_cons_self ..)
    have hm : (subtract false (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits).digits.length≤
        (weights.length+1)*(bits+height+2) := by rw [hd];apply max_le <;> nlinarith
    rcases hg with rfl|hg
    · have ha := add_length head (subtract false (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits).digits false
      dsimp only [ticketTableDigitBound]
      have hh'' : head.length≤ (weights.length+1)*(bits+height+2) := by nlinarith
      have hmax := max_le hh'' hm
      omega
    · have hl := hf digits (by rw [he];exact List.mem_cons_of_mem _ hg)
      dsimp only [ticketTableDigitBound]
      nlinarith

def ticketTableWork (count height bits : ℕ) : ℕ :=
  count*(RationalBits.dyadicFloorWork height bits+3)+sumDigitsWork count (bits+height+1)+
    2*bits+20*ticketTableDigitBound count height bits+20

theorem ticketTable_work (weights : List RationalBits) (height bits : ℕ)
    (hh : ∀ input∈weights,HeightBound input.decode height) :
    (ticketTable weights bits).work≤ ticketTableWork weights.length height bits := by
  have wf := floorTable_work weights height bits hh
  have hf := floorTable_digits weights height bits hh
  have ws := sumDigits_work (floorTable weights bits).data (bits+height+1) hf
  have hs := sumDigits_length (floorTable weights bits).data (bits+height+1) hf
  rw [floorTable_length] at ws hs
  have hd := subtract_length (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits false
  rw [powerTwoDigits_length] at hd
  have hm : max (powerTwoDigits bits).digits.length (sumDigits (floorTable weights bits).data).digits.length≤
      ticketTableDigitBound weights.length height bits := by rw [powerTwoDigits_length];unfold ticketTableDigitBound;apply max_le <;> nlinarith
  unfold ticketTable
  dsimp only
  split <;> rename_i he
  · simp only [powerTwoDigits_work,subtract_work,ticketTableWork]
    omega
  · rename_i head tail
    have hh' : _ := hf head (by rw [he];exact List.mem_cons_self ..)
    have hfirst : max head.length (subtract false (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits).digits.length≤
        ticketTableDigitBound weights.length height bits := by
      apply max_le
      · dsimp only [ticketTableDigitBound];nlinarith [hh']
      · rw [hd];simpa only [powerTwoDigits_length] using hm
    simp only [powerTwoDigits_work,subtract_work,add_work,ticketTableWork]
    omega

end AFT.BinaryArithmetic

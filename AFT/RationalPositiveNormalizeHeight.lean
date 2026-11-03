import AFT.RationalPositiveNormalize

/-! # Rational positive normalization retains polynomial operand heights -/
namespace AFT.RationalNumerics
open scoped BigOperators

 theorem positivePartProgram_height {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ)
    (hraw : ∀ index,HeightBound (raw index) bits) (index : Fin (count+1)) :
    HeightBound (positivePartProgram raw index) bits := by
  unfold positivePartProgram
  by_cases hi : 0≤raw index
  · rw [max_eq_right hi]
    exact hraw index
  · rw [max_eq_left (le_of_not_ge hi)]
    exact HeightBound.zero.mono (Nat.zero_le _)

 theorem positiveNormalizerProgram_height {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ)
    (hraw : ∀ index,HeightBound (raw index) bits) :
    HeightBound (positiveNormalizerProgram raw) ((count+1)*(bits+1)) := by
  simpa only [positiveNormalizerProgram,Finset.card_univ,Fintype.card_fin] using
    HeightBound.sum Finset.univ _ bits (fun index _ => positivePartProgram_height raw bits hraw index)

 theorem positiveWeightProgram_height {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ)
    (hraw : ∀ index,HeightBound (raw index) bits) (index : Fin (count+1)) :
    HeightBound (positiveWeightProgram raw index) (bits+(count+1)*(bits+1)) := by
  unfold positiveWeightProgram
  split_ifs
  · exact HeightBound.one.mono (Nat.zero_le _)
  · exact HeightBound.zero.mono (Nat.zero_le _)
  · exact (positivePartProgram_height raw bits hraw index).div (positiveNormalizerProgram_height raw bits hraw)

 theorem positiveFloorOperand_height {count : ℕ} (raw : Fin (count+1) → ℚ) (bits ticketBits : ℕ)
    (hraw : ∀ index,HeightBound (raw index) bits) (index : Fin (count+1)) :
    HeightBound ((2 : ℚ)^ticketBits*positiveWeightProgram raw index) (ticketBits+bits+(count+1)*(bits+1)) := by
  have ht : HeightBound ((2 : ℚ)^ticketBits) ticketBits := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using HeightBound.of_nat (le_rfl : 2^ticketBits≤2^ticketBits)
  simpa only [Nat.add_assoc] using ht.mul (positiveWeightProgram_height raw bits hraw index)

 theorem positiveRoundTicket_size {count : ℕ} (raw : Fin (count+1) → ℚ) (ticketBits : ℕ) (index : Fin (count+1)) :
    (RationalFiniteQuantization.counts (positiveWeightProgram raw) (2^ticketBits) index).size≤ticketBits+1 := by
  have hh := RationalFiniteQuantization.count_le_tickets (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^ticketBits) index
  exact (Nat.size_le_size hh).trans_eq Nat.size_pow

end AFT.RationalNumerics

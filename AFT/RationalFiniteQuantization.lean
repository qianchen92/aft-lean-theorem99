import AFT.FiniteQuantization
import AFT.FairBitSampling
import Mathlib.Data.Rat.Floor

/-! # Executable dyadic sampling of finite rational distributions

The executable count table rounds rational numbers, and assigns the remaining
tickets to index zero. Its probability law is compared with the corresponding
real distribution only in the proofs below.
-/

namespace AFT.RationalFiniteQuantization

open scoped BigOperators

variable {size : ℕ}

def floorCount (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  ⌊(tickets : ℚ) * weight index⌋₊

def floorTotal (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  ∑ index, floorCount weight tickets index

def deficit (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  tickets - floorTotal weight tickets

def counts (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  floorCount weight tickets index + if index = 0 then deficit weight tickets else 0

theorem floorTotal_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : floorTotal weight tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun index (_ : index ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (hnonneg index))
  rw [← Finset.mul_sum, hsum, mul_one] at hh
  exact_mod_cast hh

theorem counts_total (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : ∑ index, counts weight tickets index = tickets := by
  have ht := floorTotal_le weight hnonneg hsum tickets
  simp only [counts, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal weight tickets + (tickets - floorTotal weight tickets) = tickets
  omega

/-- Exactly `bits` input bits select a ticket in the rationally computed table. -/
def draw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) : Fin (size + 1) :=
  FiniteTicketSampler.drawBitTable bits (counts weight (2 ^ bits))
    (counts_total weight hnonneg hsum (2 ^ bits)) word

noncomputable section

def law (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1) :
    FiniteDist (Fin (size + 1)) where
  weight index := weight index
  nonneg index := by exact_mod_cast hnonneg index
  sum_one := by exact_mod_cast hsum

theorem floorCount_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    floorCount weight tickets index =
      FiniteQuantization.floorCount (law weight hnonneg hsum) tickets index := by
  simp only [floorCount, FiniteQuantization.floorCount, law, ← Int.floor_toNat]
  have hcast : (tickets : ℝ) * (weight index : ℝ) =
      ((tickets : ℚ) * weight index : ℚ) := by push_cast; rfl
  rw [hcast, Rat.floor_cast]

theorem counts_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    counts weight tickets index =
      FiniteQuantization.count (law weight hnonneg hsum) tickets 0 index := by
  simp only [counts, FiniteQuantization.count, deficit, FiniteQuantization.deficit,
    floorTotal, FiniteQuantization.floorTotal, floorCount_eq weight hnonneg hsum]

theorem deficit_le_card (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : deficit weight tickets ≤ size + 1 := by
  simpa only [deficit, floorTotal, floorCount_eq weight hnonneg hsum,
    FiniteQuantization.deficit, FiniteQuantization.floorTotal, Fintype.card_fin] using
    FiniteQuantization.deficit_le_card (law weight hnonneg hsum) tickets

theorem count_le_tickets (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) : counts weight tickets index ≤ tickets := by
  calc
    _ ≤ ∑ color, counts weight tickets color := Finset.single_le_sum (by simp) (by simp)
    _ = _ := counts_total weight hnonneg hsum tickets

theorem floor_error_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) (index : Fin (size + 1)) :
    |(floorCount weight tickets index : ℝ) / tickets - (weight index : ℝ)| ≤
      1 / tickets := by
  rw [floorCount_eq weight hnonneg hsum]
  exact FiniteQuantization.floor_error_le (law weight hnonneg hsum) tickets ht index

def roundedLaw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) : FiniteDist (Fin (size + 1)) where
  weight index := (counts weight tickets index : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, counts_total weight hnonneg hsum]
    exact div_self (by exact_mod_cast ht.ne')

theorem roundedLaw_eq (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    roundedLaw weight hnonneg hsum tickets ht =
      FiniteQuantization.roundedLaw (law weight hnonneg hsum) tickets ht 0 := by
  apply FiniteDist.ext
  intro index
  exact congrArg (fun count : ℕ => (count : ℝ) / tickets)
    (counts_eq weight hnonneg hsum tickets index)

theorem roundedLaw_preserves_zero (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) (hzero : 0 < weight 0)
    (index : Fin (size + 1)) (hindex : weight index = 0) :
    (roundedLaw weight hnonneg hsum tickets ht).weight index = 0 := by
  rw [roundedLaw_eq]
  apply FiniteQuantization.roundedLaw_preserves_zero
  · change (0 : ℝ) < (weight 0 : ℝ)
    exact_mod_cast hzero
  · change (weight index : ℝ) = 0
    exact_mod_cast hindex

theorem roundedLaw_l1_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    (∑ index, |(roundedLaw weight hnonneg hsum tickets ht).weight index -
      (weight index : ℝ)|) ≤ 2 * (size + 1 : ℝ) / tickets := by
  rw [roundedLaw_eq]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, law] using
    FiniteQuantization.roundedLaw_l1_le (law weight hnonneg hsum) tickets ht 0

theorem draw_law (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw weight hnonneg hsum bits) =
      roundedLaw weight hnonneg hsum (2 ^ bits) (by positivity) := by
  apply FiniteDist.ext
  intro index
  simpa only [draw, roundedLaw, Nat.cast_pow, Nat.cast_ofNat] using
    FiniteTicketSampler.drawBitTable_law bits (counts weight (2 ^ bits))
      (counts_total weight hnonneg hsum (2 ^ bits)) index

theorem draw_l1_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    (∑ index, |((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw weight hnonneg hsum bits)).weight index - (weight index : ℝ)|) ≤
      2 * (size + 1 : ℝ) / (2 : ℝ) ^ bits := by
  rw [draw_law]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    roundedLaw_l1_le weight hnonneg hsum (2 ^ bits) (by positivity)

theorem draw_tv (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    FiniteDist.TVBound
      ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
        (draw weight hnonneg hsum bits))
      (law weight hnonneg hsum) ((size + 1 : ℝ) / (2 : ℝ) ^ bits) := by
  rw [draw_law, roundedLaw_eq]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    FiniteQuantization.roundedLaw_dyadic_tv (law weight hnonneg hsum) bits 0

end
end AFT.RationalFiniteQuantization

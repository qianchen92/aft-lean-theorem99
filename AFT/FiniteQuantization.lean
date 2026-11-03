import AFT.FiniteTicketSampler
import AFT.TotalVariation

/-! # Support-preserving finite count tables and their approximation error

The rounding specification uses real weights. The resulting count table is
sampled by `FiniteTicketSampler.draw`; computability of the original real
weights is a separate obligation, not hidden in this statement.
-/

namespace AFT.FiniteQuantization

open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def floorCount (law : FiniteDist Color) (tickets : ℕ) (color : Color) : ℕ :=
  ⌊(tickets : ℝ) * law.weight color⌋₊

def floorTotal (law : FiniteDist Color) (tickets : ℕ) : ℕ := ∑ color, floorCount law tickets color

theorem floorTotal_le (law : FiniteDist Color) (tickets : ℕ) : floorTotal law tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (law.nonneg color))
  rw [← Finset.mul_sum, law.sum_one, mul_one] at hh
  exact_mod_cast hh

def deficit (law : FiniteDist Color) (tickets : ℕ) : ℕ := tickets - floorTotal law tickets

theorem deficit_le_card (law : FiniteDist Color) (tickets : ℕ) : deficit law tickets ≤ Fintype.card Color := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    (Nat.lt_floor_add_one ((tickets : ℝ) * law.weight color)).le
  rw [← Finset.mul_sum, law.sum_one, mul_one, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  have ht : (tickets : ℝ) ≤ (floorTotal law tickets : ℝ) + Fintype.card Color := by
    simpa only [floorTotal, floorCount, Nat.cast_sum] using hh
  have ht' : tickets ≤ floorTotal law tickets + Fintype.card Color := by exact_mod_cast ht
  unfold deficit
  omega

def count (law : FiniteDist Color) (tickets : ℕ) (fallback color : Color) : ℕ :=
  floorCount law tickets color + if color = fallback then deficit law tickets else 0

theorem count_sum (law : FiniteDist Color) (tickets : ℕ) (fallback : Color) :
    (∑ color, count law tickets fallback color) = tickets := by
  have ht := floorTotal_le law tickets
  simp only [count, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal law tickets + (tickets - floorTotal law tickets) = tickets
  omega

def roundedLaw (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) : FiniteDist Color where
  weight color := (count law tickets fallback color : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, count_sum]
    exact div_self (by exact_mod_cast ht.ne')

theorem roundedLaw_preserves_zero (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets)
    (fallback : Color) (hf : 0 < law.weight fallback) (color : Color) (hz : law.weight color = 0) :
    (roundedLaw law tickets ht fallback).weight color = 0 := by
  have hne : color ≠ fallback := by intro heq; subst color; linarith
  simp only [roundedLaw, count, floorCount, hz, mul_zero, Nat.floor_zero, if_neg hne,
    zero_add, Nat.cast_zero, zero_div]

theorem floor_error_le (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (color : Color) :
    |(floorCount law tickets color : ℝ) / tickets - law.weight color| ≤ 1 / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hh := Nat.abs_floor_sub_le (mul_nonneg ht0.le (law.nonneg color))
  have heq : (floorCount law tickets color : ℝ) / tickets - law.weight color =
      ((floorCount law tickets color : ℝ) - (tickets : ℝ) * law.weight color) / tickets := by field_simp
  rw [heq, abs_div, abs_of_pos ht0]
  exact div_le_div_of_nonneg_right hh ht0.le

theorem roundedLaw_l1_le (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) :
    (∑ color, |(roundedLaw law tickets ht fallback).weight color - law.weight color|) ≤
      2 * (Fintype.card Color : ℝ) / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hp (color) : |(roundedLaw law tickets ht fallback).weight color - law.weight color| ≤
      1 / tickets + if color = fallback then (deficit law tickets : ℝ) / tickets else 0 := by
    have heq : (roundedLaw law tickets ht fallback).weight color - law.weight color =
        ((floorCount law tickets color : ℝ) / tickets - law.weight color) +
          (if color = fallback then (deficit law tickets : ℝ) / tickets else 0) := by
      simp only [roundedLaw, count, Nat.cast_add, add_div]
      split_ifs <;> push_cast <;> ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add (floor_error_le law tickets ht color)
    apply le_of_eq
    apply abs_of_nonneg
    split_ifs <;> positivity
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hp color)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  have hd : (deficit law tickets : ℝ) ≤ Fintype.card Color := by exact_mod_cast deficit_le_card law tickets
  have hd' := div_le_div_of_nonneg_right hd ht0.le
  calc
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + (deficit law tickets : ℝ) / tickets := hh
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + Fintype.card Color / tickets := add_le_add le_rfl hd'
    _ = _ := by ring

theorem roundedLaw_tv (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) :
    FiniteDist.TVBound (roundedLaw law tickets ht fallback) law ((Fintype.card Color : ℝ) / tickets) := by
  apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr
  rw [FiniteDist.totalVariation_eq_half_l1]
  have hh := roundedLaw_l1_le law tickets ht fallback
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

theorem roundedLaw_dyadic_tv (law : FiniteDist Color) (bits : ℕ) (fallback : Color) :
    FiniteDist.TVBound (roundedLaw law (2 ^ bits) (by positivity) fallback) law
      ((Fintype.card Color : ℝ) / (2 : ℝ) ^ bits) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    roundedLaw_tv law (2 ^ bits) (by positivity) fallback

end
end AFT.FiniteQuantization

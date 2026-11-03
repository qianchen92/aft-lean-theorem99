import AFT.RationalHeight

/-! # A computed common denominator with polynomial binary height -/
namespace AFT.RationalNumerics
open scoped BigOperators

variable {Index : Type*} [Fintype Index]

def commonDenominator (values : Index → ℚ) : ℕ := ∏ index,(values index).den

def commonNumerator (values : Index → ℚ) (index : Index) : ℤ :=
  (values index).num*(commonDenominator values/(values index).den : ℕ)

theorem commonDenominator_pos (values : Index → ℚ) : 0<commonDenominator values :=
  Finset.prod_pos (fun index _ => (values index).den_pos)

theorem denominator_dvd_common (values : Index → ℚ) (index : Index) :
    (values index).den∣commonDenominator values :=
  Finset.dvd_prod_of_mem (fun index => (values index).den) (Finset.mem_univ index)

theorem commonNumerator_cast (values : Index → ℚ) (index : Index) :
    (commonNumerator values index : ℚ)=(commonDenominator values : ℚ)*values index := by
  have hd : ((values index).den : ℚ)≠0 := by exact_mod_cast (values index).den_ne_zero
  simp only [commonNumerator,Int.cast_mul,Int.cast_natCast,Nat.cast_div (denominator_dvd_common values index) hd]
  rw [←Rat.mul_den_eq_num (values index)]
  field_simp

theorem commonNumerator_div (values : Index → ℚ) (index : Index) :
    (commonNumerator values index : ℚ)/(commonDenominator values : ℚ)=values index := by
  rw [commonNumerator_cast]
  have hD : (commonDenominator values : ℚ)≠0 := by exact_mod_cast (commonDenominator_pos values).ne'
  field_simp

theorem commonDenominator_le (values : Index → ℚ) (bits : ℕ)
    (h : ∀index,HeightBound (values index) bits) :
    commonDenominator values≤2^(Fintype.card Index*bits) := by
  calc
    _ ≤ ∏ _index : Index,2^bits := Finset.prod_le_prod (fun index _ => Nat.zero_le _) (fun index _ => (h index).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←pow_mul];congr 1;ring

theorem commonNumerator_abs_le (values : Index → ℚ) (bits : ℕ)
    (h : ∀index,HeightBound (values index) bits) (index : Index) :
    (commonNumerator values index).natAbs≤2^((Fintype.card Index+1)*bits) := by
  simp only [commonNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  calc
    _ ≤ 2^bits*commonDenominator values := Nat.mul_le_mul (h index).1 (Nat.div_le_self _ _)
    _ ≤ 2^bits*2^(Fintype.card Index*bits) := Nat.mul_le_mul_left _ (commonDenominator_le values bits h)
    _ = _ := by rw [←pow_add];congr 1;ring

end AFT.RationalNumerics

import Mathlib

/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- The reduced numerator and denominator each fit below a binary power. -/
def HeightBound (value : ℚ) (bits : ℕ) : Prop :=
  value.num.natAbs ≤ 2^bits ∧ value.den ≤ 2^bits

namespace HeightBound

theorem mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem zero : HeightBound 0 0 := by norm_num [HeightBound]
theorem one : HeightBound 1 0 := by norm_num [HeightBound]

theorem of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))

theorem of_nat {value bits : ℕ} (h : value ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  simpa only [Int.cast_natCast] using of_int (value:=(value : ℤ)) (by simpa using h)

theorem nat_coarse (value : ℕ) : HeightBound (value : ℚ) value :=
  of_nat (Nat.lt_two_pow_self (n:=value)).le

theorem neg {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound (-value) bits := by
  simpa only [HeightBound,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using h

theorem add {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first+second) (firstBits+secondBits+1) := by
  have hr := reduced_le (first.num*second.den+first.den*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul] at hr
  rw [← Rat.add_num_den] at hr
  have hnum : (first.num*second.den+first.den*second.num).natAbs ≤
      2*(2^firstBits*2^secondBits) := by
    apply (Int.natAbs_add_le _ _).trans
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul hf.1 hs.2
    have h2 := Nat.mul_le_mul hf.2 hs.1
    omega
  have he : 2*(2^firstBits*2^secondBits)=2^(firstBits+secondBits+1) := by simp only [pow_add,pow_one]; ring
  refine ⟨hr.1.trans (hnum.trans_eq he),?_⟩
  have hh := hr.2.trans (Nat.mul_le_mul hf.2 hs.2)
  rw [← pow_add] at hh
  exact hh.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))

theorem mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := reduced_le (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩

theorem inv {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by
  by_cases hz : value=0
  · subst value
    norm_num [HeightBound]
    exact Nat.one_le_pow bits 2 (by decide)
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hsign : value.num.sign.natAbs=1 := by
      rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hz) with hn|hn
      · simp [Int.sign_eq_neg_one_of_neg hn]
      · simp [Int.sign_eq_one_of_pos hn]
    simpa only [hsign,one_mul,mul_one] using h.2
  · simpa only [Rat.den_inv_of_ne_zero hz] using h.1

theorem div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv

theorem pow {value : ℚ} {bits : ℕ} (h : HeightBound value bits) (power : ℕ) :
    HeightBound (value^power) (bits*power) := by
  induction power with
  | zero => simpa using one
  | succ power ih => simpa only [pow_succ,Nat.mul_succ] using ih.mul h

theorem sum {Index : Type*} (set : Finset Index) (value : Index → ℚ) (bits : ℕ)
    (h : ∀ index∈set,HeightBound (value index) bits) :
    HeightBound (∑ index∈set,value index) (set.card*(bits+1)) := by
  classical
  induction set using Finset.induction_on with
  | empty => simpa using zero
  | @insert index set hindex ih =>
    rw [Finset.sum_insert hindex,Finset.card_insert_of_notMem hindex]
    have hh := (h index (Finset.mem_insert_self _ _)).add (ih (fun point hp => h point (Finset.mem_insert_of_mem hp)))
    convert hh using 1
    ring

theorem binary_size {value : ℚ} {bits : ℕ} (h : HeightBound value bits) :
    value.num.natAbs.size ≤ bits+1 ∧ value.den.size ≤ bits+1 := by
  exact ⟨(Nat.size_le_size h.1).trans_eq Nat.size_pow,(Nat.size_le_size h.2).trans_eq Nat.size_pow⟩

end HeightBound
end AFT.RationalNumerics

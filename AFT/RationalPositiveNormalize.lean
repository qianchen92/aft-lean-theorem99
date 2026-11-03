import AFT.RationalFiniteQuantization
import AFT.RationalHeight
import AFT.SignedConditioning

/-! # Executable positive normalization and finite fair-bit sampling -/
namespace AFT.RationalNumerics
open scoped BigOperators

def positivePartProgram {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) : ℚ := max 0 (raw index)
def positiveNormalizerProgram {count : ℕ} (raw : Fin (count+1) → ℚ) : ℚ := ∑index,positivePartProgram raw index

def positiveWeightProgram {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) : ℚ :=
  if positiveNormalizerProgram raw=0 then (if index=0 then 1 else 0)
  else positivePartProgram raw index/positiveNormalizerProgram raw

theorem positiveNormalizerProgram_nonneg {count : ℕ} (raw : Fin (count+1) → ℚ) : 0≤positiveNormalizerProgram raw :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

theorem positiveWeightProgram_nonneg {count : ℕ} (raw : Fin (count+1) → ℚ) (index : Fin (count+1)) :
    0≤positiveWeightProgram raw index := by
  unfold positiveWeightProgram
  split_ifs
  · exact zero_le_one
  · exact le_refl _
  · exact div_nonneg (le_max_left _ _) (positiveNormalizerProgram_nonneg raw)

theorem positiveWeightProgram_sum {count : ℕ} (raw : Fin (count+1) → ℚ) :
    ∑index,positiveWeightProgram raw index=1 := by
  unfold positiveWeightProgram
  split_ifs with hz
  · simp
  · rw [←Finset.sum_div]
    exact div_self hz

def positiveNormalizeDraw {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) : Fin (count+1) :=
  RationalFiniteQuantization.draw (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (bits+(count+1)+1) word

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def positiveProgramLaw {count : ℕ} (raw : Fin (count+1) → ℚ) : FiniteDist (Fin (count+1)) where
  weight index := (positiveWeightProgram raw index : ℝ)
  nonneg index := by exact_mod_cast positiveWeightProgram_nonneg raw index
  sum_one := by exact_mod_cast positiveWeightProgram_sum raw

private theorem positivePart_distance (first second : ℝ) (hsecond : 0≤second) :
    |max 0 first-second|≤|first-second| := by
  by_cases hfirst : 0≤first
  · rw [max_eq_right hfirst]
  · rw [max_eq_left (by linarith)]
    rw [abs_of_nonpos (by linarith : first-second≤0),abs_of_nonpos (by linarith : 0-second≤0)]
    linarith

/-- The positive repair is stable against an actual probability table.
The normalizer and every rounded weight remain rational computations. -/
theorem positiveProgramLaw_l1 {count : ℕ} (raw : Fin (count+1) → ℚ)
    (reference : FiniteDist (Fin (count+1))) (error : ℝ)
    (herror : (∑index,|(raw index : ℝ)-reference.weight index|)≤error) (hsmall : error≤1/2) :
    (∑index,|(positiveProgramLaw raw).weight index-reference.weight index|)≤4*error := by
  let positive := fun index => (positivePartProgram raw index : ℝ)
  have hp (index) : positive index=max 0 (raw index : ℝ) := by simp only [positive,positivePartProgram,Rat.cast_max,Rat.cast_zero]
  have herr : (∑index,|positive index-reference.weight index|)≤error := by
    apply le_trans _ herror
    exact Finset.sum_le_sum (fun index _ => by rw [hp];exact positivePart_distance _ _ (reference.nonneg index))
  have hm := (SignedConditioning.mass_difference_le_l1 positive reference.weight).trans herr
  rw [reference.sum_one] at hm
  have hlower : 1/2≤∑index,positive index := by have h := (abs_le.mp hm).1;linarith
  have hpositive : 0<∑index,positive index := lt_of_lt_of_le (by norm_num) hlower
  have hz : positiveNormalizerProgram raw≠0 := by
    have hcast : (positiveNormalizerProgram raw : ℝ)=∑index,positive index := by simp only [positiveNormalizerProgram,Rat.cast_sum,positive]
    intro hh
    rw [hh,Rat.cast_zero] at hcast
    linarith
  have hnormal := SignedConditioning.normalized_signed_l1 positive reference.weight reference.nonneg
    hpositive (by rw [reference.sum_one];norm_num)
  have hw (index : Fin (count+1)) : positiveWeightProgram raw index=positivePartProgram raw index/positiveNormalizerProgram raw := if_neg hz
  have heq : (∑index,|(positiveProgramLaw raw).weight index-reference.weight index|)=
      ∑index,|positive index/(∑i,positive i)-reference.weight index/(∑i,reference.weight i)| := by
    simp only [positiveProgramLaw,hw,Rat.cast_div,positiveNormalizerProgram,
      Rat.cast_sum,positive,reference.sum_one,div_one]
  rw [heq]
  apply hnormal.trans
  calc
    _≤2*error/(∑i,positive i) := div_le_div_of_nonneg_right (by linarith) hpositive.le
    _≤2*error/(1/2) := div_le_div_of_nonneg_left (by
      have he0 := (Finset.sum_nonneg fun i (_ : i∈Finset.univ) => abs_nonneg (positive i-reference.weight i)).trans herr
      positivity) (by norm_num) hlower
    _=4*error := by ring

 theorem positiveNormalizeDraw_law {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map (positiveNormalizeDraw raw bits)=
      RationalFiniteQuantization.roundedLaw (positiveWeightProgram raw)
        (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity) := by
  exact RationalFiniteQuantization.draw_law _ _ _ _

 theorem positiveNormalizeDraw_l1 {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (∑index,|((FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map
      (positiveNormalizeDraw raw bits)).weight index-(positiveProgramLaw raw).weight index|)≤1/(2 : ℝ)^bits := by
  rw [positiveNormalizeDraw_law]
  have hh := RationalFiniteQuantization.roundedLaw_l1_le (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity)
  apply hh.trans
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  have hp : ((count+1 : ℕ) : ℝ)≤(2 : ℝ)^(count+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=count+1)).le
  calc
    _≤2*((2 : ℝ)^(count+1))/(2 : ℝ)^(bits+(count+1)+1) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hp
    _=_ := by rw [pow_add,pow_add];field_simp;ring

end
end AFT.RationalNumerics

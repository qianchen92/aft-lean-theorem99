import AFT.RationalHeight

/-! # Polynomial binary heights of rational determinants and inverses

A common denominator clears the matrix before applying the determinant
formula. Thus the bound counts the number of summands logarithmically,
without iterating the generic rational-addition height estimate over n! terms.
-/
namespace AFT.RationalNumerics
open Matrix
open scoped BigOperators

/-- A common integer denominator for the whole input array. -/
def matrixDenominator {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) : ℕ :=
  ∏ point : Fin count × Fin count,(matrix point.1 point.2).den

def integerMatrix {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) :
    Matrix (Fin count) (Fin count) ℤ := fun row column =>
  (matrix row column).num *
    (∏ point ∈ (Finset.univ : Finset (Fin count × Fin count)).erase (row,column),
      (matrix point.1 point.2).den : ℕ)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem factorial_le_binary (count : ℕ) : count.factorial≤2^(count*count) := by
  calc
    _ ≤ count^count := Nat.factorial_le_pow count
    _ ≤ (2^count)^count := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=count)).le count
    _ = _ := by rw [← pow_mul]

private theorem integer_det_bound {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℤ)
    (h : ∀ row column,(matrix row column).natAbs≤2^bits) :
    matrix.det.natAbs≤2^(count*count+bits*count) := by
  have he (row column : Fin count) : |matrix row column|≤(2 : ℤ)^bits := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h row column
  have hu (unit : ℤˣ) : |(unit : ℤ)|=1 := by
    have hh := Int.units_natAbs unit
    rw [← Int.natCast_natAbs]
    exact_mod_cast hh
  have hb : |matrix.det|≤(count.factorial : ℤ)*(2 : ℤ)^(bits*count) := by
    rw [Matrix.det_apply']
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ = ∑ permutation : Equiv.Perm (Fin count),∏ i,|matrix (permutation i) i| := by
        apply Finset.sum_congr rfl
        intro permutation _
        simp only [Int.cast_id,abs_mul,hu,one_mul,Finset.abs_prod]
      _ ≤ ∑ _permutation : Equiv.Perm (Fin count),(2 : ℤ)^(bits*count) := by
        apply Finset.sum_le_sum
        intro permutation _
        calc
          _ ≤ ∏ _i : Fin count,(2 : ℤ)^bits := Finset.prod_le_prod (by intros; positivity) (by intros; apply he)
          _ = _ := by simp [← pow_mul]
      _ = _ := by simp [Fintype.card_perm]
  have hf : (count.factorial : ℤ)≤(2 : ℤ)^(count*count) := by
    exact_mod_cast factorial_le_binary count
  have hh := hb.trans (mul_le_mul_of_nonneg_right hf (by positivity : 0≤(2 : ℤ)^(bits*count)))
  rw [← pow_add] at hh
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem matrixDenominator_pos {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) :
    0 < matrixDenominator matrix := by
  apply Finset.prod_pos
  intro point _
  exact Rat.den_pos _

theorem matrixDenominator_bound {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (h : ∀ row column,HeightBound (matrix row column) bits) :
    matrixDenominator matrix≤2^(count*count*bits) := by
  calc
    _ ≤ ∏ _point : Fin count × Fin count,2^bits := Finset.prod_le_prod (by simp) (fun p _ => (h p.1 p.2).2)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,← pow_mul]
      rw [Nat.mul_comm bits (count*count)]

theorem integerMatrix_cast {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) :
    (integerMatrix matrix).map (fun value => (value : ℚ))=(matrixDenominator matrix : ℚ) • matrix := by
  ext row column
  have hp := Finset.prod_erase_mul (Finset.univ : Finset (Fin count × Fin count))
    (fun point => (matrix point.1 point.2).den) (Finset.mem_univ (row,column))
  change (∏ point ∈ (Finset.univ : Finset (Fin count × Fin count)).erase (row,column),
    (matrix point.1 point.2).den)*(matrix row column).den=matrixDenominator matrix at hp
  simp only [integerMatrix,Matrix.map_apply,Int.cast_mul,Int.cast_natCast,Matrix.smul_apply,smul_eq_mul]
  rw [← hp,Nat.cast_mul,← Rat.mul_den_eq_num]
  ring

theorem integerMatrix_bound {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (h : ∀ row column,HeightBound (matrix row column) bits) (row column : Fin count) :
    (integerMatrix matrix row column).natAbs≤2^((count*count+1)*bits) := by
  have hp : (∏ point ∈ (Finset.univ : Finset (Fin count × Fin count)).erase (row,column),
      (matrix point.1 point.2).den) ≤ matrixDenominator matrix :=
    Finset.prod_le_prod_of_subset_of_one_le' (Finset.erase_subset _ _)
      (fun point _ _ => Nat.one_le_iff_ne_zero.mpr (Rat.den_ne_zero _))
  have hh := Nat.mul_le_mul (h row column).1 (hp.trans (matrixDenominator_bound matrix h))
  simp only [integerMatrix,Int.natAbs_mul,Int.natAbs_natCast]
  apply hh.trans_eq
  rw [← pow_add]
  congr 1
  ring

/-- A degree-four bound in dimension and input height. It also applies to
singular matrices and empty matrices. -/
theorem determinant_height {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (h : ∀ row column,HeightBound (matrix row column) bits) :
    HeightBound matrix.det (count*count+((count*count+1)*bits)*count+(count*count*bits)*count) := by
  have hi := HeightBound.of_int (integer_det_bound (integerMatrix matrix) (integerMatrix_bound matrix h))
  have hd := (HeightBound.of_nat (matrixDenominator_bound matrix h)).pow count
  have hd0 : (matrixDenominator matrix : ℚ)≠0 := by exact_mod_cast (matrixDenominator_pos matrix).ne'
  have he : matrix.det=((integerMatrix matrix).det : ℚ)/(matrixDenominator matrix : ℚ)^count := by
    rw [Int.cast_det,integerMatrix_cast,Matrix.det_smul,Fintype.card_fin]
    field_simp
  rw [he]
  exact hi.div hd

/-- Every exact inverse entry has polynomial binary height. The proof uses
cofactors solely as a size certificate, not as the evaluation algorithm. -/
theorem matrixInverse_height {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (h : ∀ row column,HeightBound (matrix row column) bits) (row column : Fin count) :
    HeightBound (matrix⁻¹ row column)
      (2*(count*count+((count*count+1)*bits)*count+(count*count*bits)*count)) := by
  have ha : ∀ i j,HeightBound ((matrix.updateRow column (Pi.single row 1)) i j) bits := by
    intro i j
    by_cases hi : i=column
    · subst i
      simp only [Matrix.updateRow_self,Pi.single_apply]
      split_ifs
      · exact HeightBound.one.mono (Nat.zero_le _)
      · exact HeightBound.zero.mono (Nat.zero_le _)
    · simpa only [Matrix.updateRow_ne hi] using h i j
  have hh := (determinant_height matrix h).inv.mul
    (determinant_height (matrix.updateRow column (Pi.single row 1)) ha)
  simpa only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_apply,two_mul] using hh

end
end AFT.RationalNumerics

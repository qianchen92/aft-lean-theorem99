import AFT.BodyPaddingInverse
import AFT.RationalHeight

/-! # Executable rational Green matrix for the actual body padding covariance -/
namespace AFT.BodyPadding
open Matrix RationalNumerics
open scoped BigOperators

/-- Discrete Dirichlet Green kernel, using only rational arithmetic. -/
def rationalPathGreen (count : ℕ) (row column : Fin count) : ℚ :=
  (min (row.val+1) (column.val+1) : ℕ)-
    ((row.val+1 : ℕ) : ℚ)*(column.val+1 : ℕ)/(count+1 : ℕ)

/-- The variance parameter is its rational square, so no square root is
computed by the covariance program. -/
def rationalBodyPaddingCovariance (count : ℕ) (squaredWidth : ℚ) : Matrix (Fin count) (Fin count) ℚ :=
  fun row column => squaredWidth*(8*rationalPathGreen count row column-if row=column then 1 else 0)

private def greenPrimitive (count : ℕ) (column : Fin count) (position : ℕ) : ℚ :=
  (min position (column.val+1) : ℕ)-(position : ℚ)*(column.val+1 : ℕ)/(count+1 : ℕ)

private theorem greenPrimitive_zero (count : ℕ) (column : Fin count) : greenPrimitive count column 0=0 := by
  simp [greenPrimitive]

private theorem greenPrimitive_last (count : ℕ) (column : Fin count) : greenPrimitive count column (count+1)=0 := by
  have hm : min (count+1) (column.val+1)=column.val+1 := min_eq_right (by omega)
  have hn : ((count+1 : ℕ) : ℚ)≠0 := by positivity
  simp only [greenPrimitive,hm]
  field_simp
  ring

private theorem greenPrimitive_succ (count : ℕ) (column : Fin count) (position : ℕ) :
    greenPrimitive count column (position+1)-greenPrimitive count column position=
      (if position≤column.val then 1 else 0)-(column.val+1 : ℕ)/(count+1 : ℕ) := by
  unfold greenPrimitive
  by_cases hp : position≤column.val
  · rw [if_pos hp,min_eq_left (by omega : position+1≤column.val+1),
      min_eq_left (by omega : position≤column.val+1)]
    push_cast
    ring
  · rw [if_neg hp,min_eq_right (by omega : column.val+1≤position+1),
      min_eq_right (by omega : column.val+1≤position)]
    push_cast
    ring

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realPath_green_column (count : ℕ) (column : Fin count) (vertex : Fin (count+1)) :
    realPath (fun row => (rationalPathGreen count row column : ℝ)) vertex=
      (if vertex.val≤column.val then 1 else 0)-((column.val+1 : ℕ) : ℝ)/(count+1 : ℕ) := by
  have hs : (Fin.snoc (fun row => (rationalPathGreen count row column : ℝ)) 0 : Fin (count+1) → ℝ) vertex=
      (greenPrimitive count column (vertex.val+1) : ℝ) := by
    refine Fin.lastCases ?_ (fun row => ?_) vertex
    · simp only [Fin.snoc_last,Fin.val_last,greenPrimitive_last,Rat.cast_zero]
    · simp only [Fin.snoc_castSucc,Fin.val_castSucc]
      rfl
  have hc : (Fin.cons 0 (fun row => (rationalPathGreen count row column : ℝ)) : Fin (count+1) → ℝ) vertex=
      (greenPrimitive count column vertex.val : ℝ) := by
    refine Fin.cases ?_ (fun row => ?_) vertex
    · simp only [Fin.cons_zero,Fin.val_zero,greenPrimitive_zero,Rat.cast_zero]
    · rfl
  change (Fin.snoc _ 0 : Fin (count+1) → ℝ) vertex-(Fin.cons 0 _ : Fin (count+1) → ℝ) vertex=_
  rw [hs,hc,← Rat.cast_sub,greenPrimitive_succ]
  push_cast
  split_ifs <;> simp

private theorem pathGram_green_column (count : ℕ) (column : Fin count) :
    (pathGram count).mulVec (fun row => (rationalPathGreen count row column : ℝ))=Pi.single column 1 := by
  rw [pathGram,← Matrix.mulVec_mulVec,pathMatrix_mulVec]
  funext row
  rw [pathTranspose_mulVec,realPath_green_column,realPath_green_column]
  simp only [Fin.val_castSucc,Fin.val_succ]
  by_cases he : row=column
  · subst row
    simp
  · have hv : row.val≠column.val := fun hh => he (Fin.ext hh)
    simp only [Pi.single_apply,if_neg he]
    by_cases hh : row.val≤column.val
    · have hh' : row.val+1≤column.val := by omega
      rw [if_pos hh,if_pos hh']
      ring
    · have hh' : ¬row.val+1≤column.val := by omega
      rw [if_neg hh,if_neg hh']
      ring

/-- The computed rational array is exactly the inverse of the actual path
Gram matrix used throughout the Gaussian convolution proof. -/
theorem rationalPathGreen_cast (count : ℕ) :
    (fun row column => (rationalPathGreen count row column : ℝ))=(pathGram count)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  ext row column
  have hh := congrFun (pathGram_green_column count column) row
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Pi.single_apply,Matrix.one_apply] using hh

theorem rationalBodyPaddingCovariance_cast (count : ℕ) (squaredWidth : ℚ) (sigma : ℝ)
    (hwidth : (squaredWidth : ℝ)=sigma^2) :
    (fun row column => (rationalBodyPaddingCovariance count squaredWidth row column : ℝ))=
      bodyPaddingCovariance count sigma := by
  ext row column
  have hh := congrFun (congrFun (rationalPathGreen_cast count) row) column
  simp only [rationalBodyPaddingCovariance,Rat.cast_mul,Rat.cast_sub,Rat.cast_ofNat,
    apply_ite,Rat.cast_one,Rat.cast_zero,hwidth,hh,bodyPaddingCovariance,
    Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply,smul_eq_mul]
  split_ifs <;> simp_all


/-- Every covariance entry is computed with polynomially bounded rational
numerator and denominator; no real matrix inverse is evaluated. -/
theorem rationalPathGreen_height (count : ℕ) (row column : Fin count) :
    HeightBound (rationalPathGreen count row column) (4*count+2) := by
  have hr : HeightBound ((row.val+1 : ℕ) : ℚ) count := (HeightBound.nat_coarse _).mono (by omega)
  have hc : HeightBound ((column.val+1 : ℕ) : ℚ) count := (HeightBound.nat_coarse _).mono (by omega)
  have hm : HeightBound ((min (row.val+1) (column.val+1) : ℕ) : ℚ) count :=
    (HeightBound.nat_coarse _).mono (by omega)
  have hd : HeightBound ((count+1 : ℕ) : ℚ) (count+1) := HeightBound.nat_coarse _
  have hh := hm.add (((hr.mul hc).div hd).neg)
  have he : count+(count+count+(count+1))+1=4*count+2 := by omega
  rw [he] at hh
  simpa only [rationalPathGreen,sub_eq_add_neg] using hh

theorem rationalBodyPaddingCovariance_height (count : ℕ) (squaredWidth : ℚ) (bits : ℕ)
    (hwidth : HeightBound squaredWidth bits) (row column : Fin count) :
    HeightBound (rationalBodyPaddingCovariance count squaredWidth row column) (bits+4*count+6) := by
  have he : HeightBound (8 : ℚ) 3 := by norm_num [HeightBound]
  have hi : HeightBound (if row=column then (1 : ℚ) else 0) 0 := by
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  have hh := hwidth.mul ((he.mul (rationalPathGreen_height count row column)).add hi.neg)
  have heq : bits+(3+(4*count+2)+0+1)=bits+4*count+6 := by omega
  rw [heq] at hh
  simpa only [rationalBodyPaddingCovariance,sub_eq_add_neg] using hh

end
end AFT.BodyPadding

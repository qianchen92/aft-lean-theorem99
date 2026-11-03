import AFT.GaussianLeadingMinor

/-! # Polynomial bit heights of the actual cached LDL program -/
namespace AFT.RationalNumerics
open Matrix
open scoped BigOperators

/-- These explicit expressions are polynomials in dimension and input height. -/
def rationalLDLRowHeight (count bits : ℕ) : ℕ :=
  count*(2*(count*count+((count*count+1)*bits)*count+(count*count*bits)*count)+bits+1)

def rationalLDLDiagonalHeight (count bits : ℕ) : ℕ :=
  count*(count*(bits+rationalLDLRowHeight count bits+1)+rationalLDLRowHeight count bits+1)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem rationalLDLLower_leading_inverse {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hpositive : Matrix.PosDef (fun i j => (matrix i j : ℝ))) (row : Fin count) :
    (fun index => ((rationalLDLLower matrix).get row).get (leadingIndex row index))=
      (leadingMatrix matrix row)⁻¹.mulVec (fun index => -matrix (leadingIndex row index) row) := by
  have heq : (leadingMatrix matrix row).mulVec
      (fun index => ((rationalLDLLower matrix).get row).get (leadingIndex row index))=
      fun index => -matrix (leadingIndex row index) row := by
    funext first
    apply Rat.cast_injective (α := ℝ)
    have hh := congrFun (lowerInv_leading_equation hpositive row) first
    simpa only [Matrix.mulVec,dotProduct,leadingMatrix,Rat.cast_sum,Rat.cast_mul,Rat.cast_neg,
      rationalLDLLower_cast matrix hpositive] using hh
  have hd : (leadingMatrix matrix row).det≠0 := by
    intro he
    have hh := (leadingMatrix_posDef hpositive row).det_pos
    have hc : ((leadingMatrix matrix row).det : ℝ)=
        (leadingMatrix (fun i j => (matrix i j : ℝ)) row).det := by
      rw [Rat.cast_det]
      rfl
    rw [he,Rat.cast_zero] at hc
    rw [←hc] at hh
    exact (lt_irrefl (0 : ℝ)) hh
  rw [←heq,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]

/-- The bound is obtained from principal minors of the original input,
not by recursively amplifying the heights of the elimination history. -/
theorem rationalLDLLower_height {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hpositive : Matrix.PosDef (fun i j => (matrix i j : ℝ)))
    (hheight : ∀ row column,HeightBound (matrix row column) bits) (row column : Fin count) :
    HeightBound (((rationalLDLLower matrix).get row).get column) (rationalLDLRowHeight count bits) := by
  by_cases hbefore : column < row
  · let index : Fin row.val := ⟨column.val,hbefore⟩
    have he := congrFun (rationalLDLLower_leading_inverse matrix hpositive row) index
    have hind : leadingIndex row index=column := Fin.ext rfl
    rw [hind] at he
    rw [he]
    have hmatrix (first second : Fin row.val) :
        HeightBound ((leadingMatrix matrix row)⁻¹ first second)
          (2*(count*count+((count*count+1)*bits)*count+(count*count*bits)*count)) := by
      apply (matrixInverse_height (leadingMatrix matrix row)
        (fun i j => hheight (leadingIndex row i) (leadingIndex row j)) first second).mono
      gcongr <;> exact row.isLt.le
    have hs := HeightBound.sum Finset.univ
      (fun second : Fin row.val => (leadingMatrix matrix row)⁻¹ index second*(-matrix (leadingIndex row second) row))
      (2*(count*count+((count*count+1)*bits)*count+(count*count*bits)*count)+bits)
      (fun second _ => (hmatrix index second).mul (hheight (leadingIndex row second) row).neg)
    simp only [Finset.card_univ,Fintype.card_fin] at hs
    apply hs.mono
    unfold rationalLDLRowHeight
    exact Nat.mul_le_mul_right _ row.isLt.le
  · by_cases he : column=row
    · subst column
      have hh : ((rationalLDLLower matrix).get row).get row=1 := by
        apply Rat.cast_injective (α := ℝ)
        rw [rationalLDLLower_cast matrix hpositive,GaussianSource.gaussianLDL_unit_diagonal,Rat.cast_one]
      rw [hh]
      exact HeightBound.one.mono (Nat.zero_le _)
    · have hh : ((rationalLDLLower matrix).get row).get column=0 := by
        apply Rat.cast_injective (α := ℝ)
        rw [rationalLDLLower_cast matrix hpositive,LDL.lowerInv_triangular hpositive
          (lt_of_le_of_ne (le_of_not_gt hbefore) (Ne.symm he)),Rat.cast_zero]
      rw [hh]
      exact HeightBound.zero.mono (Nat.zero_le _)

theorem rationalLDLDiagonal_height {count bits : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hpositive : Matrix.PosDef (fun i j => (matrix i j : ℝ)))
    (hheight : ∀ row column,HeightBound (matrix row column) bits) (row : Fin count) :
    HeightBound ((rationalLDLDiagonal matrix).get row) (rationalLDLDiagonalHeight count bits) := by
  have hlower := rationalLDLLower_height matrix hpositive hheight row
  have hinner (first : Fin count) := HeightBound.sum Finset.univ
    (fun second : Fin count => matrix second first*((rationalLDLLower matrix).get row).get second)
    (bits+rationalLDLRowHeight count bits)
    (fun second _ => (hheight second first).mul (hlower second))
  simp only [Finset.card_univ,Fintype.card_fin] at hinner
  have hsum := HeightBound.sum Finset.univ
    (fun first : Fin count => (∑ second,matrix second first*((rationalLDLLower matrix).get row).get second)*
      ((rationalLDLLower matrix).get row).get first)
    (count*(bits+rationalLDLRowHeight count bits+1)+rationalLDLRowHeight count bits)
    (fun first _ => (hinner first).mul (hlower first))
  simpa only [rationalLDLDiagonal,Vector.get_ofFn,rationalLDLInner,rationalLDLDiagonalHeight,
    Finset.card_univ,Fintype.card_fin] using hsum

end
end AFT.RationalNumerics

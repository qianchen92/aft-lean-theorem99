import AFT.RationalLDL
import AFT.RationalMatrixHeight

/-! # LDL rows as solutions of actual leading principal systems -/
namespace AFT.RationalNumerics
open Matrix Module InnerProductSpace
open scoped BigOperators

def leadingIndex {count : ℕ} (row : Fin count) (index : Fin row.val) : Fin count :=
  ⟨index.val,index.isLt.trans row.isLt⟩

def leadingMatrix {count : ℕ} {Field : Type*} (matrix : Matrix (Fin count) (Fin count) Field)
    (row : Fin count) : Matrix (Fin row.val) (Fin row.val) Field :=
  fun first second => matrix (leadingIndex row first) (leadingIndex row second)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem leadingIndex_injective {count : ℕ} (row : Fin count) : Function.Injective (leadingIndex row) := by
  intro first second he
  exact Fin.ext (congrArg (fun value : Fin count => value.val) he)

private theorem posDef_submatrix_injective {First Second : Type*}
    {matrix : Matrix First First ℝ} (hpositive : matrix.PosDef)
    (embedding : Second → First) (hinjective : Function.Injective embedding) :
    (matrix.submatrix embedding embedding).PosDef := by
  refine ⟨hpositive.1.submatrix _,fun vector hvector => ?_⟩
  have hn : vector.mapDomain embedding≠0 := by
    intro he
    apply hvector
    apply Finsupp.mapDomain_injective hinjective
    simpa only [Finsupp.mapDomain_zero] using he
  simpa only [Finsupp.sum_mapDomain_index_inj hinjective,Matrix.submatrix_apply] using hpositive.2 hn

theorem leadingMatrix_posDef {count : ℕ} {matrix : Matrix (Fin count) (Fin count) ℝ}
    (hpositive : matrix.PosDef) (row : Fin count) : (leadingMatrix matrix row).PosDef :=
  posDef_submatrix_injective hpositive (leadingIndex row) (leadingIndex_injective row)

/-- The current orthogonalized basis vector is orthogonal to every original
earlier coordinate, not merely to the earlier orthogonalized rows. -/
theorem lowerInv_before {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (row earlier : Fin count) (hearlier : earlier<row) :
    covariance.mulVec (LDL.lowerInv hcovariance row) earlier=0 := by
  let normed := covarianceᵀ.toNormedAddCommGroup hcovariance.transpose
  let innerSpace := covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef
  have hh := @gramSchmidt_def'' ℝ (Fin count → ℝ) _ normed innerSpace
    (Fin count) _ _ _ (Pi.basisFun ℝ (Fin count)) earlier
  have hz := congrArg (fun vector => covarianceᵀ.mulVec vector ⬝ᵥ LDL.lowerInv hcovariance row) hh
  simp only [Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_smul,add_dotProduct,
    sum_dotProduct,smul_dotProduct,smul_eq_mul,RCLike.ofReal_real_eq_id,id_eq] at hz
  have horth (index : Fin count) (hi : index≠row) :
      @inner ℝ (Fin count → ℝ) innerSpace.toInner (LDL.lowerInv hcovariance row)
        (LDL.lowerInv hcovariance index)=0 :=
    @gramSchmidt_orthogonal ℝ (Fin count → ℝ) _ normed innerSpace
      (Fin count) _ _ _ (Pi.basisFun ℝ (Fin count)) row index hi.symm
  have hmatrix (index : Fin count) (hi : index≠row) :
      covarianceᵀ.mulVec (LDL.lowerInv hcovariance index) ⬝ᵥ LDL.lowerInv hcovariance row=0 := horth index hi
  have hsum (coefficient : Fin count → ℝ) :
      (∑ index ∈ Finset.Iio earlier,coefficient index*
        (covarianceᵀ.mulVec (LDL.lowerInv hcovariance index) ⬝ᵥ LDL.lowerInv hcovariance row))=0 := by
    apply Finset.sum_eq_zero
    intro index hi
    rw [hmatrix index (lt_trans (Finset.mem_Iio.mp hi) hearlier).ne,mul_zero]
  change covarianceᵀ.mulVec ((Pi.basisFun ℝ (Fin count)) earlier) ⬝ᵥ LDL.lowerInv hcovariance row=
    covarianceᵀ.mulVec (LDL.lowerInv hcovariance earlier) ⬝ᵥ LDL.lowerInv hcovariance row+_ at hz
  rw [hmatrix earlier hearlier.ne] at hz
  change covarianceᵀ.mulVec ((Pi.basisFun ℝ (Fin count)) earlier) ⬝ᵥ LDL.lowerInv hcovariance row=
    0+∑ index ∈ Finset.Iio earlier,_*
      (covarianceᵀ.mulVec (LDL.lowerInv hcovariance index) ⬝ᵥ LDL.lowerInv hcovariance row) at hz
  rw [hsum,add_zero] at hz
  simp only [Pi.basisFun_apply] at hz
  change covarianceᵀ.mulVec (Pi.single earlier 1) ⬝ᵥ LDL.lowerInv hcovariance row=0 at hz
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hz

private theorem sum_before {count : ℕ} (row : Fin count) (function : Fin count → ℝ) :
    (∑ index,if index<row then function index else 0)=∑ index : Fin row.val,function (leadingIndex row index) := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun index _ => leadingIndex row index)
  · intro index _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact index.isLt
  · intro first _ second _ he
    exact leadingIndex_injective row he
  · intro index hi
    have hh := (Finset.mem_filter.mp hi).2
    exact ⟨⟨index.val,hh⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · intro index _
    rfl

/-- The lower part of a genuine LDL row satisfies the original leading
principal linear system, with the actual cross-covariance right hand side. -/
theorem lowerInv_leading_equation {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (row : Fin count) :
    (leadingMatrix covariance row).mulVec (fun index => LDL.lowerInv hcovariance row (leadingIndex row index))=
      fun index => -covariance (leadingIndex row index) row := by
  funext first
  have he := lowerInv_before hcovariance row (leadingIndex row first) first.isLt
  have hterm (index : Fin count) :
      covariance (leadingIndex row first) index*LDL.lowerInv hcovariance row index=
      (if index<row then covariance (leadingIndex row first) index*LDL.lowerInv hcovariance row index else 0)+
        (if index=row then covariance (leadingIndex row first) row else 0) := by
    by_cases hi : index<row
    · simp only [if_pos hi,if_neg hi.ne,add_zero]
    · by_cases heq : index=row
      · subst index
        simp only [lt_self_iff_false,if_false,if_true,GaussianSource.gaussianLDL_unit_diagonal,mul_one,zero_add]
      · have hgt : row < index := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm heq)
        rw [LDL.lowerInv_triangular hcovariance hgt,if_neg hi,if_neg heq]
        ring
  change (∑ index,covariance (leadingIndex row first) index*LDL.lowerInv hcovariance row index)=0 at he
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun index _ => hterm index)
  rw [Finset.sum_add_distrib,sum_before] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
  change (∑ index,covariance (leadingIndex row first) (leadingIndex row index)*LDL.lowerInv hcovariance row (leadingIndex row index))=_
  linarith

/-- The explicit inverse of the smaller principal matrix gives the entire
strictly lower row. This identity supplies polynomial rational heights. -/
theorem lowerInv_leading_inverse {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (row : Fin count) :
    (fun index => LDL.lowerInv hcovariance row (leadingIndex row index))=
      (leadingMatrix covariance row)⁻¹.mulVec (fun index => -covariance (leadingIndex row index) row) := by
  rw [←lowerInv_leading_equation hcovariance row,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (leadingMatrix_posDef hcovariance row).det_pos.ne'),Matrix.one_mulVec]

end
end AFT.RationalNumerics

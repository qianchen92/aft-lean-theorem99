import AFT.BodyPaddingInverse
import Mathlib.Analysis.Matrix.LDL

/-! # Quantitative LDL coordinates for the actual padding covariances -/
namespace AFT.GaussianSource
open Matrix Module InnerProductSpace
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false


private theorem gramSchmidt_basis_diagonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {count : ℕ} (basis : Basis (Fin count) ℝ E) (i : Fin count) :
    basis.repr (gramSchmidt ℝ basis i) i=1 := by
  have hh := congrArg (fun vector : E => basis.repr vector i) (gramSchmidt_def'' ℝ basis i)
  simp only [map_add,map_sum,map_smul,Finsupp.add_apply,Finsupp.finset_sum_apply,Finsupp.smul_apply,
    smul_eq_mul,Basis.repr_self,Finsupp.single_eq_same,RCLike.ofReal_real_eq_id,id_eq] at hh
  have hz : (∑ j ∈ Finset.Iio i,
      (inner ℝ (gramSchmidt ℝ basis j) (basis i) / ‖gramSchmidt ℝ basis j‖^2) *
        basis.repr (gramSchmidt ℝ basis j) i)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) basis,mul_zero]
  rw [hz,add_zero] at hh
  exact hh.symm

private theorem gramSchmidt_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {count : ℕ} (basis : Basis (Fin count) ℝ E) (i : Fin count) :
    inner ℝ (gramSchmidt ℝ basis i) (gramSchmidt ℝ basis i)≤ inner ℝ (basis i) (basis i) := by
  let orthogonal := gramSchmidt ℝ basis
  have heq : inner ℝ (orthogonal i) (basis i)=inner ℝ (orthogonal i) (orthogonal i) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ basis i]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal i)
        (∑ j ∈ Finset.Iio i,(inner ℝ (orthogonal j) (basis i)/‖orthogonal j‖^2) • orthogonal j)=0 by
      change inner ℝ (orthogonal i) (orthogonal i)+_=inner ℝ (orthogonal i) (orthogonal i)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_orthogonal ℝ basis (Finset.mem_Iio.mp hj).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := basis i-orthogonal i))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal i) (basis i),heq] at hnonneg
  change inner ℝ (orthogonal i) (orthogonal i)≤_
  linarith

variable {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}

/-- The Gram--Schmidt lower factor is unit triangular, so its rows have
Euclidean square norm at least one. -/
theorem gaussianLDL_unit_diagonal (hcovariance : covariance.PosDef) (i : Fin count) :
    LDL.lowerInv hcovariance i i=1 := by
  have hh := @gramSchmidt_basis_diagonal (Fin count → ℝ)
    (covarianceᵀ.toNormedAddCommGroup hcovariance.transpose)
    (covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef) count
    (Pi.basisFun ℝ (Fin count)) i
  simpa only [Pi.basisFun_repr,LDL.lowerInv] using hh

/-- Any lower quadratic-form bound on the covariance holds for each
actual LDL scalar variance. This preserves the exact Gaussian width. -/
theorem gaussianLDL_diagonal_lower (hcovariance : covariance.PosDef) (lower : ℝ)
    (hlower : 0≤lower)
    (hbound : ∀ vector : Fin count → ℝ,lower*(∑ j,vector j^2)≤
      star vector ⬝ᵥ covariance.mulVec vector) (i : Fin count) :
    lower≤LDL.diagEntries hcovariance i := by
  have hnorm : 1≤∑ j,(LDL.lowerInv hcovariance i j)^2 := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin count))) =>
      sq_nonneg (LDL.lowerInv hcovariance i j)) (Finset.mem_univ i)
    simpa only [gaussianLDL_unit_diagonal hcovariance i,one_pow] using hh
  have hh := hbound (LDL.lowerInv hcovariance i)
  have he : LDL.diagEntries hcovariance i=
      star (LDL.lowerInv hcovariance i) ⬝ᵥ covariance.mulVec (LDL.lowerInv hcovariance i) := by
    simp only [LDL.diagEntries,EuclideanSpace.inner_toLp_toLp,star_trivial]
    exact dotProduct_comm _ _
  rw [he]
  exact (le_mul_of_one_le_right hlower hnorm).trans hh


theorem gaussianLDL_diagonal_upper (hcovariance : covariance.PosDef) (i : Fin count) :
    LDL.diagEntries hcovariance i≤covariance i i := by
  have hh := @gramSchmidt_inner_le (Fin count → ℝ)
    (covarianceᵀ.toNormedAddCommGroup hcovariance.transpose)
    (covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef) count
    (Pi.basisFun ℝ (Fin count)) i
  change covarianceᵀ.mulVec (LDL.lowerInv hcovariance i) ⬝ᵥ LDL.lowerInv hcovariance i≤
    covarianceᵀ.mulVec ((Pi.basisFun ℝ (Fin count)) i) ⬝ᵥ ((Pi.basisFun ℝ (Fin count)) i) at hh
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hcovariance.isHermitian.eq] at hh
  simpa only [LDL.diagEntries,EuclideanSpace.inner_toLp_toLp,star_trivial,Pi.basisFun_apply,
    Matrix.mulVec_single,MulOpposite.op_one,one_smul,dotProduct_single,mul_one,Matrix.col_apply] using hh


/-- The inverse covariance is exactly the triangular sum of squares used
by the sequential integer sampler. -/
theorem gaussianLDL_precision (hcovariance : covariance.PosDef) :
    covariance⁻¹=(LDL.lowerInv hcovariance)ᴴ*(LDL.diag hcovariance)⁻¹*LDL.lowerInv hcovariance := by
  rw [LDL.diag_eq_lowerInv_conj,Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.mul_one]
  rw [← Matrix.mul_assoc,Matrix.mul_inv_of_invertible,Matrix.one_mul]

theorem gaussianLDL_quadratic (hcovariance : covariance.PosDef) (vector : Fin count → ℝ) :
    star vector ⬝ᵥ covariance⁻¹.mulVec vector=
      ∑ i,((LDL.lowerInv hcovariance).mulVec vector i)^2/LDL.diagEntries hcovariance i := by
  rw [gaussianLDL_precision hcovariance,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_conjTranspose]
  have hnonzero (i : Fin count) : LDL.diagEntries hcovariance i≠0 := by
    have hrow : LDL.lowerInv hcovariance i≠0 := by
      intro he
      have hh := congrFun he i
      simp only [Pi.zero_apply,gaussianLDL_unit_diagonal hcovariance i] at hh
      norm_num at hh
    have hp := hcovariance.dotProduct_mulVec_pos hrow
    simp only [LDL.diagEntries,EuclideanSpace.inner_toLp_toLp,star_trivial]
    exact (by simpa only [star_trivial,dotProduct_comm] using hp :
      0<covariance.mulVec (LDL.lowerInv hcovariance i) ⬝ᵥ LDL.lowerInv hcovariance i).ne'
  have hinv : (LDL.diag hcovariance)⁻¹=Matrix.diagonal (fun i => (LDL.diagEntries hcovariance i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp only [LDL.diag,Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j; simp [hnonzero i]
    · simp [hij]
  rw [hinv]
  simp only [Matrix.mulVec_diagonal,star_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual padding sampler has no scalar Gaussian narrower than sigma. -/
theorem bodyPadding_LDL_width_bounds (count : ℕ) (sigma : ℝ) (hsigma : 0<sigma)
    (i : Fin count) :
    sigma≤Real.sqrt (LDL.diagEntries (BodyPadding.bodyPaddingCovariance_posDef count sigma hsigma.ne') i) ∧
      Real.sqrt (LDL.diagEntries (BodyPadding.bodyPaddingCovariance_posDef count sigma hsigma.ne') i)≤
        Real.sqrt 8*sigma*(count+1) := by
  have hlo := gaussianLDL_diagonal_lower (BodyPadding.bodyPaddingCovariance_posDef count sigma hsigma.ne')
    (sigma^2) (sq_nonneg _) (fun vector => (BodyPadding.bodyPaddingCovariance_bounds count sigma vector).1) i
  have hhi := gaussianLDL_diagonal_upper (BodyPadding.bodyPaddingCovariance_posDef count sigma hsigma.ne') i
  have hb := (BodyPadding.bodyPaddingCovariance_bounds count sigma (Pi.single i 1)).2
  simp only [star_trivial,Matrix.mulVec_single,MulOpposite.op_one,one_smul,single_dotProduct,mul_one,one_mul,Matrix.col_apply,
    Pi.single_apply,ite_pow,one_pow,zero_pow (by decide : 2≠0),Finset.sum_ite_eq',Finset.mem_univ,if_true] at hb
  have hn : 0≤LDL.diagEntries (BodyPadding.bodyPaddingCovariance_posDef count sigma hsigma.ne') i :=
    (sq_nonneg sigma).trans hlo
  constructor
  · exact (Real.le_sqrt hsigma.le hn).mpr hlo
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hsq : (Real.sqrt 8*sigma*(count+1))^2=8*sigma^2*(count+1)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤8)]
    rw [hsq]
    exact hhi.trans hb

end
end AFT.GaussianSource

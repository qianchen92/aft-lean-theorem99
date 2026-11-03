import AFT.GaussianMatrixChain

/-! # Stored rational Gram--Schmidt coordinates for Gaussian padding

The recursion materializes every computed row before advancing. Its values
are exactly the actual positive-definite covariance LDL coordinates.
-/
namespace AFT.RationalNumerics
open Matrix Module InnerProductSpace
open scoped BigOperators

/-- The covariance inner product, written using only rational arithmetic. -/
def rationalLDLInner {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (left right : Fin count → ℚ) : ℚ :=
  ∑ i,(∑ j,matrix j i*right j)*left i

/-- Row storage avoids recursively recomputing earlier Gram--Schmidt rows. -/
def rationalLDLState {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) :
    ℕ → Vector (Vector ℚ count) count
  | 0 => Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0))
  | steps+1 =>
      let previous := rationalLDLState matrix steps
      Vector.ofFn (fun row => if row.val=steps then
        Vector.ofFn (fun column => (if row=column then 1 else 0)-
          ∑ earlier ∈ Finset.Iio row,
            rationalLDLInner matrix (fun i => (previous.get earlier).get i) (Pi.single row 1)/
              rationalLDLInner matrix (fun i => (previous.get earlier).get i)
                (fun i => (previous.get earlier).get i)*(previous.get earlier).get column)
        else previous.get row)

def rationalLDLLower {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) :
    Vector (Vector ℚ count) count := rationalLDLState matrix count

def rationalLDLDiagonal {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ) : Vector ℚ count :=
  let lower := rationalLDLLower matrix
  Vector.ofFn (fun row => rationalLDLInner matrix (fun i => (lower.get row).get i)
    (fun i => (lower.get row).get i))

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem lowerInv_recurrence {count : ℕ} {covariance : Matrix (Fin count) (Fin count) ℝ}
    (hcovariance : covariance.PosDef) (row column : Fin count) :
    LDL.lowerInv hcovariance row column=(if row=column then 1 else 0)-
      ∑ earlier ∈ Finset.Iio row,
        ((covarianceᵀ.mulVec (Pi.single row 1)) ⬝ᵥ (LDL.lowerInv hcovariance earlier))/
          ((covarianceᵀ.mulVec (LDL.lowerInv hcovariance earlier)) ⬝ᵥ LDL.lowerInv hcovariance earlier)*
          LDL.lowerInv hcovariance earlier column := by
  letI := covarianceᵀ.toNormedAddCommGroup hcovariance.transpose
  letI := covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef
  have hh := congrArg (fun vector : Fin count → ℝ => vector column)
    (@gramSchmidt_def'' ℝ (Fin count → ℝ) _
      (covarianceᵀ.toNormedAddCommGroup hcovariance.transpose)
      (covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef)
      (Fin count) _ _ _ (Pi.basisFun ℝ (Fin count)) row)
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,RCLike.ofReal_real_eq_id,id_eq,
    ] at hh
  have hnorm (vector : Fin count → ℝ) := @real_inner_self_eq_norm_sq (Fin count → ℝ)
    (covarianceᵀ.toNormedAddCommGroup hcovariance.transpose).toSeminormedAddCommGroup
    (covarianceᵀ.toInnerProductSpace hcovariance.transpose.posSemidef) vector
  simp only [← hnorm,Pi.basisFun_apply] at hh
  change (Pi.single row (1 : ℝ) : Fin count → ℝ) column =
    LDL.lowerInv hcovariance row column+
      ∑ earlier ∈ Finset.Iio row,
        ((covarianceᵀ.mulVec (Pi.single row 1)) ⬝ᵥ (LDL.lowerInv hcovariance earlier))/
          ((covarianceᵀ.mulVec (LDL.lowerInv hcovariance earlier)) ⬝ᵥ LDL.lowerInv hcovariance earlier)*
          LDL.lowerInv hcovariance earlier column at hh
  simpa only [Pi.basisFun_apply,Pi.single_apply,eq_comm] using (eq_sub_iff_add_eq.mpr hh.symm)

private theorem rationalLDLInner_cast {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (left right : Fin count → ℚ) :
    (rationalLDLInner matrix left right : ℝ)=
      ((fun i j => (matrix i j : ℝ))ᵀ.mulVec (fun i => (right i : ℝ))) ⬝ᵥ (fun i => (left i : ℝ)) := by
  simp only [rationalLDLInner,Rat.cast_sum,Rat.cast_mul,Matrix.mulVec,Matrix.transpose_apply,dotProduct]

/-- Every stored row is the genuine real covariance LDL row as soon as its
stage has completed. No nonsingularity premise is added to the program. -/
theorem rationalLDLState_cast {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hcovariance : Matrix.PosDef (fun i j => (matrix i j : ℝ))) (steps : ℕ)
    (row column : Fin count) (hrow : row.val<steps) :
    ((rationalLDLState matrix steps).get row |>.get column : ℝ)=
      LDL.lowerInv hcovariance row column := by
  induction steps generalizing row column with
  | zero => omega
  | succ steps ih =>
    simp only [rationalLDLState,Vector.get_ofFn]
    by_cases heq : row.val=steps
    · rw [if_pos heq,Vector.get_ofFn]
      simp only [Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,apply_ite,Rat.cast_one,Rat.cast_zero,
        rationalLDLInner_cast]
      rw [lowerInv_recurrence]
      congr 1
      apply Finset.sum_congr rfl
      intro earlier hearlier
      have hj : earlier.val<steps := by
        have hj := Finset.mem_Iio.mp hearlier
        exact heq ▸ hj
      have hprevious : (fun i => ((rationalLDLState matrix steps).get earlier |>.get i : ℝ))=
          LDL.lowerInv hcovariance earlier := funext (fun i => ih earlier i hj)
      have hsingle : (fun i : Fin count => ((Pi.single row (1 : ℚ) : Fin count → ℚ) i : ℝ))=(Pi.single row (1 : ℝ) : Fin count → ℝ) := by
        funext i
        by_cases hi : i=row <;> simp [Pi.single_apply,hi]
      rw [hprevious,hsingle,ih earlier column hj]
    · rw [if_neg heq]
      exact ih row column (by omega)

theorem rationalLDLLower_cast {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hcovariance : Matrix.PosDef (fun i j => (matrix i j : ℝ))) (row column : Fin count) :
    ((rationalLDLLower matrix).get row |>.get column : ℝ)=LDL.lowerInv hcovariance row column :=
  rationalLDLState_cast matrix hcovariance count row column row.isLt

theorem rationalLDLDiagonal_cast {count : ℕ} (matrix : Matrix (Fin count) (Fin count) ℚ)
    (hcovariance : Matrix.PosDef (fun i j => (matrix i j : ℝ))) (row : Fin count) :
    ((rationalLDLDiagonal matrix).get row : ℝ)=LDL.diagEntries hcovariance row := by
  simp only [rationalLDLDiagonal,Vector.get_ofFn,rationalLDLInner_cast]
  have he : (fun i => ((rationalLDLLower matrix).get row |>.get i : ℝ))=
      LDL.lowerInv hcovariance row := funext (rationalLDLLower_cast matrix hcovariance row)
  rw [he]
  have hs : (fun i j => (matrix i j : ℝ))ᵀ=(fun i j => (matrix i j : ℝ)) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hcovariance.isHermitian.eq]
  rw [hs]
  simp only [LDL.diagEntries,EuclideanSpace.inner_toLp_toLp,star_trivial]

end
end AFT.RationalNumerics

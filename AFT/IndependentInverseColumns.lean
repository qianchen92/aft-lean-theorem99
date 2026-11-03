import AFT.JointInverseMatrix
import AFT.IndependentJointCanonical
import AFT.ActualDensityInverseBounds

/-! # Actual nonlinear joint replacement as explicit calibrated columns -/
namespace AFT.V7Calibration
open GaussianSource MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance independentInverseColumnsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentInverseColumnsSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _

/-- A column already includes every newly introduced inverse coordinate. -/
def independentInverseColumn (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (selected : Finset (Fin 4)) (point : Fin (Parameters.modulus n))
    (output : selected → Fin (Parameters.modulus n)) : ℝ :=
  ∑ input,independentReferenceChannel C n beta charts selected (Pi.single point 1) input*
    ∏ slot,actualDensityInverseEntry C n beta operator (input slot) (output slot)

private theorem finite_basis_expansion {Color : Type*} [Fintype Color] (profile : Color → ℝ) :
    (∑ point,profile point • (Pi.single point (1 : ℝ) : Color → ℝ))=profile := by
  classical
  funext color
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

omit [Fintype Rest] in
/-- Only the one replaced input is summed out. All unchanged primary and
body coordinates remain a joint fixed fiber throughout the calculation. -/
theorem independentJointInverse_columns (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n))) (selected : Finset (Fin 4))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ)
    (output : selected → Fin (Parameters.modulus n)) (rest : Rest → Fin (Parameters.modulus n)) :
    independentJointInverse C n beta operator charts other selected kernel (Sum.elim output rest)=
      ∑ point,kernel point rest*independentInverseColumn C n beta operator charts selected point output := by
  unfold independentJointInverse
  rw [coordinateInverseKernel_new_matrix]
  have hkernel (input : selected → Fin (Parameters.modulus n)) :
      independentReferenceReplacement C n beta charts selected kernel (Sum.elim input rest)=
        ∑ point,kernel point rest*independentReferenceChannel C n beta charts selected (Pi.single point 1) input := by
    rw [independentReferenceReplacement_eq]
    change independentReferenceChannel C n beta charts selected (fun point => kernel point rest) input=_
    rw [←finite_basis_expansion (fun point => kernel point rest)]
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp only [hkernel,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  simp only [independentInverseColumn,Finset.mul_sum,actualDensityInverseEntry]
  apply Finset.sum_congr rfl
  intro input _
  ring

end
end AFT.V7Calibration

import CurrentAFT.RationalLocalFamilyProgram
import CurrentAFT.RationalPositiveReferenceProgram
import CurrentAFT.RationalFamilyReciprocalBounds

/-! # The actual positive local reference as a rational coefficient table -/
namespace CurrentAFT.RationalPositiveFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def coefficient (security bits : ℕ) (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalCoefficientExtraction.selectedKernel security bits (RationalPositiveReferenceProgram.current security bits) selected output

def positive (security bits order : ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => unit order arity colors centers +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      RationalLocalFamilyProgram.insertSelected order selected (coefficient security bits selected) arity colors centers

def inverse (security bits order : ℕ) : Table ℚ ℕ ℕ order := reciprocal order (positive security bits order)

def primaryChannel (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) : Table ℚ ℕ ℕ order :=
  product order (RationalLocalFamilyProgram.numerator security bits order compensatorRoot attachmentRoot primaryColor)
    (inverse security bits order)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def coefficientError (security degree : ℕ) : ℝ :=
  RationalCoefficientExtraction.normalizedError security degree 1 (RationalPositiveReferenceProgram.errorConstant security)

theorem massError_nonneg (security : ℕ) : 0 ≤ RationalPositiveReferenceProgram.errorConstant security := by
  unfold RationalPositiveReferenceProgram.errorConstant RationalPositiveReferenceProgram.fixedErrorConstant
    RationalRootMassProgram.primaryErrorConstant
  positivity

theorem coefficientError_nonneg (security degree : ℕ) : 0 ≤ coefficientError security degree := by
  unfold coefficientError RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError RationalCoefficientExtraction.atomErrorConstant
    RationalRootMassProgram.primaryErrorConstant RationalTensorInverseProgram.tensorErrorConstant
  positivity [massError_nonneg security, RationalTensorInverseProgram.actualBound_nonneg security,
    RationalTensorInverseProgram.errorConstant_nonneg security, RationalTensorInverseProgram.factorBound_one_le security]

theorem coefficient_error (security bits : ℕ) (selected : Finset (Fin 4))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (centers : Fin 0 → SafePalette security) :
    |(coefficient security bits selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card
        (NormalizedLocalPolynomial.independentPositiveLaw security).weight selected (by simp)).val output centers| ≤
      coefficientError security selected.card * (1 / (2 : ℝ)^bits) := by
  exact RationalCoefficientExtraction.selectedKernel_error security bits
    (RationalPositiveReferenceProgram.current security bits) (NormalizedLocalPolynomial.independentPositiveLaw security).weight
    selected 1 (RationalPositiveReferenceProgram.errorConstant security) (by norm_num) (massError_nonneg security)
    (fun word => by
      rw [abs_of_nonneg ((NormalizedLocalPolynomial.independentPositiveLaw security).nonneg word)]
      exact (NormalizedLocalPolynomial.independentPositiveLaw security).atom_le_one word)
    (fun word => RationalPositiveReferenceProgram.current_error security bits hprecision hbudget word)
    hfirst hprecision hbudget output centers

theorem unit_point_cast (order security : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    ((unit order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℚ) : ℝ) =
      unit order arity colors centers := by
  unfold unit
  split_ifs <;> norm_num

theorem positiveFamily_point (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val
      colors centers = unit order arity colors centers +
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        RationalLocalFamilyProgram.insertSelected order selected
          (fun word => (LocalCoefficientFamily.selectedKernel security selected.card
            (NormalizedLocalPolynomial.independentPositiveLaw security).weight selected (by simp)).val word Fin.elim0)
          arity colors centers := by
  unfold NormalizedLocalPolynomial.positiveFamily NormalizedLocalPolynomial.completeFamily
  rw [FiniteDist.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hunit := congrFun (congrFun (congrFun (unit_actual (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [← hunit]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (RationalLocalFamilyProgram.insertSelected_actual security order _ selected arity colors centers).symm

def errorConstant (security : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅, coefficientError security selected.card

theorem positive_error (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val
        colors centers| ≤ errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsum : (positive security bits order arity (fun index => (colors index).val)
      (fun index => (centers index).val.val) : ℝ) = unit order arity colors centers +
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        (RationalLocalFamilyProgram.insertSelected order selected (coefficient security bits selected)
          arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold positive
    simp only [Rat.cast_add, Rat.cast_sum]
    have hu : ((unit order arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℚ) : ℝ) = unit order arity colors centers := by
      unfold unit
      split_ifs <;> norm_num
    rw [hu]
    congr 1
  rw [hsum, positiveFamily_point, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        coefficientError security selected.card * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact RationalLocalFamilyProgram.insertSelected_error order selected security _ _ _
        (by positivity [coefficientError_nonneg security selected.card])
        (fun word => coefficient_error security bits selected hfirst hprecision hbudget word Fin.elim0)
        arity colors centers
    _ = _ := by rw [← Finset.sum_mul]; rfl

end
end CurrentAFT.RationalPositiveFamilyProgram

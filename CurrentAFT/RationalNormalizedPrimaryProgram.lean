import CurrentAFT.RationalPositiveFamilyProgram
import CurrentAFT.RationalFamilyPullback
import CurrentAFT.PositiveFamilyPointBound
import CurrentAFT.LocalCoefficientPointBounds

/-! # Actual normalized primary columns from rational finite reciprocals -/
namespace CurrentAFT.RationalNormalizedPrimaryProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def lifted (security order : ℕ) (table : Table ℚ ℕ ℕ order) : Table ℝ (Palette security) (SafePalette security) order :=
  pullback order (fun color : Palette security => color.val) (fun color : SafePalette security => color.val.val)
    (realTable order table)

theorem inverse_lifted (security bits order : ℕ) :
    lifted security order (RationalPositiveFamilyProgram.inverse security bits order) =
      reciprocal order (lifted security order (RationalPositiveFamilyProgram.positive security bits order)) := by
  unfold lifted RationalPositiveFamilyProgram.inverse
  rw [reciprocal_cast, pullback_reciprocal]

theorem inverse_actual (security order : ℕ) :
    reciprocal order (fun arity =>
      (NormalizedLocalPolynomial.positiveFamily security order (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val) =
      fun arity => (LocalRaisingBounds.positiveInverse security order arity).val := by
  rw [reciprocal_actual]
  rfl

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ RationalPositiveFamilyProgram.errorConstant security := by
  unfold RationalPositiveFamilyProgram.errorConstant
  exact Finset.sum_nonneg (fun selected _ => RationalPositiveFamilyProgram.coefficientError_nonneg security selected.card)

def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + PositiveFamilyPointBound.bound security order) 0)^order

theorem inverseBound_nonneg (security order : ℕ) : 0 ≤ inverseBound security order := by
  unfold inverseBound
  positivity [growth_ge_one order (1 + PositiveFamilyPointBound.bound security order) 0
    (by positivity [PositiveFamilyPointBound.bound_nonneg security order]) (by norm_num)]

theorem actual_inverse_bound (security order : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(LocalRaisingBounds.positiveInverse security order arity).val colors centers| ≤ inverseBound security order := by
  have h := reciprocal_bound order
    (fun arity => (NormalizedLocalPolynomial.positiveFamily security order
      (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val)
    (PositiveFamilyPointBound.bound security order) (PositiveFamilyPointBound.bound_nonneg security order)
    (PositiveFamilyPointBound.point_bound security order) arity colors centers
  rw [inverse_actual] at h
  exact h

def inverseErrorConstant (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * RationalPositiveFamilyProgram.errorConstant security *
    (growth order (1 + PositiveFamilyPointBound.bound security order)
      (RationalPositiveFamilyProgram.errorConstant security))^(order + 1)

theorem inverseErrorConstant_nonneg (security order : ℕ) : 0 ≤ inverseErrorConstant security order := by
  unfold inverseErrorConstant
  positivity [errorConstant_nonneg security, growth_ge_one order
    (1 + PositiveFamilyPointBound.bound security order) (RationalPositiveFamilyProgram.errorConstant security)
    (by positivity [PositiveFamilyPointBound.bound_nonneg security order]) (errorConstant_nonneg security)]

theorem inverse_error (security bits order : ℕ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RationalPositiveFamilyProgram.inverse security bits order arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (LocalRaisingBounds.positiveInverse security order arity).val colors centers| ≤
      inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := RationalPositiveFamilyProgram.errorConstant security
  let A := PositiveFamilyPointBound.bound security order
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := errorConstant_nonneg security
  have hA : 0 ≤ A := PositiveFamilyPointBound.bound_nonneg security order
  have h := reciprocal_error order
    (fun arity => (NormalizedLocalPolynomial.positiveFamily security order
      (NormalizedLocalPolynomial.independentPositiveLaw security) arity).val)
    (lifted security order (RationalPositiveFamilyProgram.positive security bits order)) A (E * epsilon) hA (by positivity)
    (PositiveFamilyPointBound.point_bound security order)
    (fun arity colors centers => RationalPositiveFamilyProgram.positive_error security bits order
      hfirst hprecision hbudget arity colors centers) arity colors centers
  rw [← inverse_lifted, inverse_actual] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by
    unfold growth
    gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (growth_ge_one order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [E, A, epsilon]; ring

theorem primaryChannel_lifted (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) :
    lifted security order (RationalPositiveFamilyProgram.primaryChannel security bits order compensatorRoot attachmentRoot primaryColor) =
      product order (lifted security order (RationalLocalFamilyProgram.numerator security bits order compensatorRoot attachmentRoot primaryColor))
        (lifted security order (RationalPositiveFamilyProgram.inverse security bits order)) := by
  unfold lifted RationalPositiveFamilyProgram.primaryChannel
  rw [product_cast, pullback_product]

def primaryErrorConstant (security order : ℕ) : ℝ :=
  (Nat.card (TruncatedArity order) : ℝ)^2 *
    (RationalLocalFamilyProgram.numeratorErrorConstant security * inverseBound security order +
      (LocalCoefficientPointBounds.numeratorBound security + RationalLocalFamilyProgram.numeratorErrorConstant security) *
        inverseErrorConstant security order)

theorem primaryChannel_error (security bits order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RationalPositiveFamilyProgram.primaryChannel security bits order roots.1.val roots.2.val primaryColor.val arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.primaryAt security order roots primaryColor arity).val colors centers| ≤
        primaryErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let numerator := LocalRaisingLinear.completeFamilyLinear security order
    (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let eN := RationalLocalFamilyProgram.numeratorErrorConstant security
  let eI := inverseErrorConstant security order
  let A := LocalCoefficientPointBounds.numeratorBound security
  let B := inverseBound security order
  have he : 0 ≤ epsilon := by positivity
  have heN : 0 ≤ eN := by
    unfold eN RationalLocalFamilyProgram.numeratorErrorConstant
    exact Finset.sum_nonneg (fun selected _ => RationalLocalFamilyProgram.primaryError_nonneg security selected.card)
  have heI : 0 ≤ eI := inverseErrorConstant_nonneg security order
  have hA : 0 ≤ A := LocalCoefficientPointBounds.numeratorBound_nonneg security
  have hB : 0 ≤ B := inverseBound_nonneg security order
  have h := product_error order (fun arity => (numerator arity).val)
    (lifted security order (RationalLocalFamilyProgram.numerator security bits order roots.1.val roots.2.val primaryColor.val))
    (fun arity => (LocalRaisingBounds.positiveInverse security order arity).val)
    (lifted security order (RationalPositiveFamilyProgram.inverse security bits order)) A B (eN * epsilon) (eI * epsilon)
    hA hB (by positivity) (by positivity)
    (LocalCoefficientPointBounds.numerator_bound security order roots primaryColor)
    (actual_inverse_bound security order)
    (fun arity colors centers => RationalLocalFamilyProgram.numerator_error security bits order roots primaryColor
      hfirst hprecision hbudget arity colors centers)
    (fun arity colors centers => inverse_error security bits order hfirst hprecision hbudget arity colors centers)
    arity colors centers
  rw [← primaryChannel_lifted, product_actual] at h
  simp only [Fintype.card_eq_nat_card] at h
  have hsmall : eN * epsilon ≤ eN := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) heN
  calc
    _ ≤ _ := h
    _ ≤ (Nat.card (TruncatedArity order) : ℝ)^2 *
        ((eN * epsilon) * B + (A + eN) * (eI * epsilon)) := by gcongr
    _ = _ := by unfold primaryErrorConstant; dsimp only [eN, eI, A, B, epsilon]; ring

end
end CurrentAFT.RationalNormalizedPrimaryProgram

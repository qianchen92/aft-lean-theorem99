import CurrentAFT.RationalPackedRootApproximation
import CurrentAFT.NumericalGroupConstants

/-! # A polynomial error envelope for the complete packed root channel -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
  GradedControlAlgebra RationalActualFamilyApproximation PolynomialErrorEnvelope
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedRatesFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedRatesSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedRatesSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def kernelErrorBound (security order : ℕ) : ℝ :=
  order*(RationalRootMassProgram.primaryErrorConstant security+
    (RationalRootMassProgram.primaryErrorConstant security*Parameters.modulus security+2))

def uniformScalarBound (security order : ℕ) : ℝ := (1+kernelErrorBound security order)*(1+4*order)

def uniformScalarError (security order : ℕ) : ℝ :=
  (kernelErrorBound security order+8*order)*(1+4*order)+4*order

def errorConstant (security order : ℕ) : ℝ :=
  (CurrentRectangleIndex.colors security:ℝ)^(6*order) *
    ((uniformScalarBound security order*(2*order)*RationalRootGroupProgram.errorConstant security order+
      uniformScalarError security order)*(localGrowth security order)^(2*order))

theorem kernelErrorBound_nonneg (security order : ℕ) : 0 ≤ kernelErrorBound security order := by
  unfold kernelErrorBound RationalRootMassProgram.primaryErrorConstant
  positivity

theorem errorConstant_nonneg (security order : ℕ) : 0 ≤ errorConstant security order := by
  have hk := kernelErrorBound_nonneg security order
  have hE := RationalRootGroupProgram.errorConstant_nonneg security order
  have hC := (by norm_num : (0:ℝ)≤1).trans (localGrowth_one_le security order)
  unfold errorConstant uniformScalarBound uniformScalarError
  positivity

theorem pointKernelError_le (security order r s : ℕ) (hdegree : r+s≤order) :
    WeightedPointKernelProgram.errorConstant security r s ≤ kernelErrorBound security order := by
  have hp : 0 ≤ RationalRootMassProgram.primaryErrorConstant security := by
    unfold RationalRootMassProgram.primaryErrorConstant; positivity
  have hb : 0 ≤ RationalRootMassProgram.primaryErrorConstant security*Parameters.modulus security+2 := by positivity
  have hr : (r:ℝ)≤order := by exact_mod_cast (show r≤order by omega)
  have hs : (s:ℝ)≤order := by exact_mod_cast (show s≤order by omega)
  unfold WeightedPointKernelProgram.errorConstant kernelErrorBound
  nlinarith [mul_le_mul_of_nonneg_right hr hp, mul_le_mul_of_nonneg_right hs hb]

theorem rawError_le (security order r s count tags : ℕ) (hdegree : r+s≤order)
    (hcount : count≤2*order) (htags : tags≤order) :
    rawErrorConstant security order r s count tags ≤ errorConstant security order := by
  have hE := RationalRootGroupProgram.errorConstant_nonneg security order
  have hK := pointKernelError_nonneg security r s
  have hU := kernelErrorBound_nonneg security order
  have hC := localGrowth_one_le security order
  have hKle := pointKernelError_le security order r s hdegree
  have hcountR : (count:ℝ)≤2*order := by exact_mod_cast hcount
  have htagsR : (tags:ℝ)≤order := by exact_mod_cast htags
  have hsb : scalarBound security r s tags ≤ uniformScalarBound security order := by
    unfold scalarBound uniformScalarBound
    gcongr
  have hse : scalarError security r s count tags ≤ uniformScalarError security order := by
    unfold scalarError uniformScalarError
    have hfirst : WeightedPointKernelProgram.errorConstant security r s+4*count ≤
        kernelErrorBound security order+8*order := by linarith
    have hsecond : (1:ℝ)+4*tags≤1+4*order := by linarith
    exact add_le_add (mul_le_mul hfirst hsecond (by positivity) (by positivity)) (by linarith)
  have hSB : 0 ≤ uniformScalarBound security order := by unfold uniformScalarBound; positivity
  have hpre : scalarBound security r s tags*count*RationalRootGroupProgram.errorConstant security order+
      scalarError security r s count tags ≤
      uniformScalarBound security order*(2*order)*RationalRootGroupProgram.errorConstant security order+
        uniformScalarError security order := by
    gcongr
  have hpow := pow_le_pow_right₀ hC hcount
  have hsource : sourceError security order r s count tags ≤
      (uniformScalarBound security order*(2*order)*RationalRootGroupProgram.errorConstant security order+
        uniformScalarError security order)*(localGrowth security order)^(2*order) := by
    unfold sourceError
    exact mul_le_mul hpre hpow (pow_nonneg ((by norm_num : (0:ℝ)≤1).trans hC) _) (by
      unfold uniformScalarBound uniformScalarError; positivity)
  have hq : (1:ℝ)≤CurrentRectangleIndex.colors security := by
    exact_mod_cast CurrentRectangleIndex.colors_pos security
  have hqpow : (CurrentRectangleIndex.colors security:ℝ)^(count*3) ≤
      (CurrentRectangleIndex.colors security:ℝ)^(6*order) :=
    pow_le_pow_right₀ hq (by omega)
  unfold rawErrorConstant errorConstant
  exact mul_le_mul hqpow hsource (sourceError_nonneg _ _ _ _ _ _) (by positivity)

theorem current_error {security r s : ℕ} (bits order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security) (hroom : tagged.card ≤ Parameters.bodySize security)
    (hdegree : r+s≤order) (htags : tagged.card≤order)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order queue (actualMetadata selection tagged)
        (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)) arity colors centers -
      data security order (ActualRootResponse.response order horder queue selection tagged layout
        (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)) arity colors centers| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  have hc : groupCount selection tagged≤2*order := by
    have hk := CurrentRootOrdering.kept_count_le selection tagged
    unfold groupCount
    omega
  exact (current_error_raw bits order horder queue selection tagged layout hroom sourcePrimary sourceBody
    hfirst hprecision hbudget arity colors centers).trans
    (mul_le_mul_of_nonneg_right (rawError_le security order r s _ _ hdegree hc htags) (by positivity))

theorem error_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => errorConstant security order) := by
  have hp := NumericalGroupConstants.error order
  have hb := NumericalGroupConstants.point_bound order
  have hc : PolynomialErrorEnvelope RationalRootMassProgram.primaryErrorConstant := by
    change PolynomialErrorEnvelope (fun security => RationalRootMassProgram.primaryErrorConstant security)
    simp only [RationalRootMassProgram.primaryErrorConstant]
    repeat' first
      | exact PolynomialErrorEnvelope.base
      | exact PolynomialErrorEnvelope.dimension
      | exact PolynomialErrorEnvelope.constant _
      | apply PolynomialErrorEnvelope.mul
  simp only [errorConstant, uniformScalarBound, uniformScalarError, kernelErrorBound, localGrowth,
    RationalFamilyProductProgram.growth, CurrentRectangleIndex.colors_eq]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem error_negligible (order : ℕ) : AFT.Negligible (fun security => errorConstant security order*(1/(2:ℝ)^security)) :=
  (error_polynomial order).dyadic

end
end CurrentAFT.RationalPackedRootProgram

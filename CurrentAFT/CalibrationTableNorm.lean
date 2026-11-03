import CurrentAFT.CalibrationCoordinateError
import AFT.BinaryChartIteration

/-! # A stable norm on the explicit full calibration table

The exact response is contractive on the decoded coefficient family and
annihilates the redundant part of the table. The norm below records both
parts, with polynomial comparisons to the ordinary coordinate sup norm.
-/
namespace CurrentAFT.CalibrationTableNorm
open AFT ActualControls ProposalPrimary LocalCoefficientFamily BackgroundRates
  CalibrationPointCoordinates CalibrationCoordinateError GradedControlAlgebra
  GradedControlNorm GradedControlStability ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance tableFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Index (security order : ℕ) :=
  PointIndex (ActualControls.Palette security) (SafePalette security) order
abbrev Table (security order : ℕ) := Index security order → ℝ

def encodeCurrent (security order : ℕ) : Family security order →ₗ[ℝ] Table security order :=
  encode (primaryLaw security) (bodyReference security) order
def decodeCurrent (security order : ℕ) : Table security order →ₗ[ℝ] Family security order :=
  decode (primaryLaw security) (bodyReference security) (primaryReference_positive security)
    (bodyReference_positive security) order
def remainder (security order : ℕ) : Module.End ℝ (Table security order) :=
  LinearMap.id - (encodeCurrent security order).comp (decodeCurrent security order)
def measure (security order : ℕ) (table : Table security order) : ℝ :=
  LocalRaisingBounds.coefficientNorm security order (decodeCurrent security order table) +
    ‖remainder security order table‖

def encodeFactor (security order : ℕ) : ℝ :=
  (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order
def decodeFactor (security order : ℕ) : ℝ :=
  (order + 1 : ℕ)^2 * (2 * (Parameters.modulus security : ℝ) + 1)^order
def comparisonFactor (security order : ℕ) : ℝ :=
  1 + (1 + encodeFactor security order) * decodeFactor security order

theorem family_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ _ _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le family

theorem decode_encode_current (security order : ℕ) (family : Family security order) :
    decodeCurrent security order (encodeCurrent security order family) = family :=
  decode_encode _ _ _ _ _ family

theorem remainder_encode (security order : ℕ) (family : Family security order) :
    remainder security order (encodeCurrent security order family) = 0 := by
  simp only [remainder, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    decode_encode_current, sub_self]

theorem measure_encode (security order : ℕ) (family : Family security order) :
    measure security order (encodeCurrent security order family) =
      LocalRaisingBounds.coefficientNorm security order family := by
  simp only [measure, decode_encode_current, remainder_encode, norm_zero, add_zero]

theorem measure_nonneg (security order : ℕ) (table : Table security order) :
    0 ≤ measure security order table := add_nonneg (family_nonneg security order _) (norm_nonneg _)

theorem measure_zero (security order : ℕ) : measure security order 0 = 0 := by
  simp only [measure, map_zero, LocalRaisingBounds.coefficientNorm, familyNorm_zero, norm_zero, add_zero]

theorem measure_add (security order : ℕ) (first second : Table security order) :
    measure security order (first + second) ≤ measure security order first + measure security order second := by
  have hf := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le (decodeCurrent security order first) (decodeCurrent security order second)
  have hr := norm_add_le (remainder security order first) (remainder security order second)
  simp only [measure, map_add, LocalRaisingBounds.coefficientNorm]
  linarith

theorem measure_neg (security order : ℕ) (table : Table security order) :
    measure security order (-table) = measure security order table := by
  simp only [measure, map_neg, LocalRaisingBounds.coefficientNorm, familyNorm_neg, norm_neg]

theorem encode_norm (security order : ℕ) (family : Family security order) :
    ‖encodeCurrent security order family‖ ≤
      encodeFactor security order * LocalRaisingBounds.coefficientNorm security order family := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by unfold encodeFactor; positivity)
    (family_nonneg security order family))).mpr
  intro point
  exact ActualCoordinateBounds.family_point_bound security order family point.1 point.2.1 point.2.2

theorem decode_norm (security order : ℕ) (table : Table security order) :
    LocalRaisingBounds.coefficientNorm security order (decodeCurrent security order table) ≤
      decodeFactor security order * ‖table‖ := by
  have h := current_decode_error security order table ‖table‖ (norm_nonneg _)
    (fun point => (norm_le_pi_norm table point))
  simpa only [decodeCurrent, decodeFactor, mul_assoc] using h

theorem coordinate_le_measure (security order : ℕ) (table : Table security order) :
    ‖table‖ ≤ (1 + encodeFactor security order) * measure security order table := by
  have hsplit : table = encodeCurrent security order (decodeCurrent security order table) +
      remainder security order table := by
    simp only [remainder, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel
  have htri := norm_add_le (encodeCurrent security order (decodeCurrent security order table))
    (remainder security order table)
  rw [← hsplit] at htri
  have he := encode_norm security order (decodeCurrent security order table)
  have hp : 0 ≤ encodeFactor security order := by unfold encodeFactor; positivity
  unfold measure
  nlinarith [family_nonneg security order (decodeCurrent security order table), norm_nonneg (remainder security order table)]

theorem measure_le_coordinate (security order : ℕ) (table : Table security order) :
    measure security order table ≤ comparisonFactor security order * ‖table‖ := by
  have hd := decode_norm security order table
  have he := encode_norm security order (decodeCurrent security order table)
  have hr := norm_sub_le table (encodeCurrent security order (decodeCurrent security order table))
  have hp : 0 ≤ encodeFactor security order := by unfold encodeFactor; positivity
  have hm := mul_le_mul_of_nonneg_left hd hp
  unfold measure comparisonFactor remainder
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  nlinarith

def exactDefect (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Module.End ℝ (Table security order) :=
  (encodeCurrent security order).comp
    ((fullResponse security order horder (room security order horder hsecurity) layout - LinearMap.id).comp
      (decodeCurrent security order))

theorem exactDefect_contracts (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (table : Table security order) :
    measure security order (exactDefect security order horder hsecurity layout table) ≤
      (1 / 2 : ℝ) * measure security order table := by
  have hs := stable security order horder hsecurity layout
  have hn := family_nonneg security order (decodeCurrent security order table)
  have hbound := (hs.2 (decodeCurrent security order table)).trans (mul_le_mul_of_nonneg_right hs.1 hn)
  simp only [exactDefect, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, measure_encode]
  have he : fullResponse security order horder (room security order horder hsecurity) layout
      (decodeCurrent security order table) - decodeCurrent security order table =
      -(decodeCurrent security order table - fullResponse security order horder
        (room security order horder hsecurity) layout (decodeCurrent security order table)) := by abel
  rw [he]
  simp only [LocalRaisingBounds.coefficientNorm, familyNorm_neg] at hbound ⊢
  unfold measure
  simp only [LocalRaisingBounds.coefficientNorm]
  linarith [norm_nonneg (remainder security order table)]

theorem target_fixed (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    encodeCurrent security order 1 - exactDefect security order horder hsecurity layout
        (encodeCurrent security order (solution security order horder hsecurity layout)) =
      encodeCurrent security order (solution security order horder hsecurity layout) := by
  simp only [exactDefect, LinearMap.comp_apply, decode_encode_current, LinearMap.sub_apply,
    LinearMap.id_apply, solution_response, map_sub]
  abel

theorem exactDefect_matrix (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) =
      currentMatrix security order horder hsecurity layout - 1 := by
  have he : exactDefect security order horder hsecurity layout =
      extend (primaryLaw security) (bodyReference security) (primaryReference_positive security)
        (bodyReference_positive security) order
        (fullResponse security order horder (room security order horder hsecurity) layout) - LinearMap.id := by
    ext table point
    simp only [exactDefect, extend, encodeCurrent, decodeCurrent, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply, map_sub, Pi.sub_apply]
    ring
  rw [he, map_sub]
  simp only [currentMatrix, LinearMap.toMatrix'_id]

end
end CurrentAFT.CalibrationTableNorm

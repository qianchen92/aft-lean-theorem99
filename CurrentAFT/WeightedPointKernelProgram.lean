import CurrentAFT.CalibrationPointCoordinates
import CurrentAFT.RationalPrimaryColumnProgram
import CurrentAFT.RationalFamilyProductProgram

/-! # Weighted point-source columns without source-reference reciprocals

The reference mass in exact point reconstruction cancels each centered
Dirac denominator before the joint point tensor is symmetrized.
-/
namespace CurrentAFT.WeightedPointKernelProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CanonicalReconstruction
  ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def bodyDelta (security bits source color : ℕ) : ℚ :=
  (if color = source then 1 else 0) - RationalProposalProgram.center security bits source

def current (security bits r s : ℕ) (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ)
    (colors : Fin r → ℕ) (centers : Fin s → ℕ) : ℚ :=
  RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
    (∏ index, RationalPrimaryColumnProgram.centerDelta security bits (sourcePrimary index) (colors (primaryOrder index))) *
    ∏ index, bodyDelta security bits (sourceBody index) (centers (bodyOrder index)))

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

section Generic
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def weightedTensor {r s : ℕ} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers => MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors *
    MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers

theorem weight_absorption (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      (pointKernel primary body hp hb sourcePrimary sourceBody).val =
        symmetrize (weightedTensor primary body sourcePrimary sourceBody) := by
  have hraw : ((∏ index, primary.weight (sourcePrimary index)) * (∏ index, body.weight (sourceBody index))) •
      pointTensor primary body sourcePrimary sourceBody = weightedTensor primary body sourcePrimary sourceBody := by
    funext colors centers
    simp only [Pi.smul_apply, smul_eq_mul, pointTensor, weightedTensor]
    rw [← weighted_basis_product primary hp, ← weighted_basis_product body hb]
    ring
  have h := congrArg (symmetrizeLinear (Primary := Primary) (Body := Body)) hraw
  rw [map_smul] at h
  exact h

end Generic

def actualKernel (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s :=
  ((∏ index, (primaryLaw security).weight (sourcePrimary index)) *
    (∏ index, (bodyReference security).weight (sourceBody index))) •
      pointKernel (primaryLaw security) (bodyReference security) (primaryReference_positive security)
        (bodyReference_positive security) sourcePrimary sourceBody

theorem actualKernel_formula (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    (actualKernel security sourcePrimary sourceBody).val colors centers =
      RationalFamilyProductProgram.average r s (fun primaryOrder bodyOrder =>
        (∏ index, ((if colors (primaryOrder index) = sourcePrimary index then (1 : ℝ) else 0) -
          (primaryLaw security).weight (sourcePrimary index))) *
        ∏ index, ((if centers (bodyOrder index) = sourceBody index then (1 : ℝ) else 0) -
          (bodyReference security).weight (sourceBody index))) := by
  have h := congrFun (congrFun (weight_absorption (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) sourcePrimary sourceBody) colors) centers
  change (actualKernel security sourcePrimary sourceBody).val colors centers = _ at h
  rw [ControlProduct.symmetrize_apply] at h
  simp only [Fintype.card_perm, Fintype.card_fin, weightedTensor, MixedKernel.canonicalPointBasis] at h
  rw [h]
  unfold RationalFamilyProductProgram.average
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext; simp)
  intro primaryOrder _
  apply Finset.sum_congr (by ext; simp)
  intro bodyOrder _
  dsimp only
  apply congrArg₂ (fun first second : ℝ => first * second)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : colors (primaryOrder index) = sourcePrimary index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    by_cases hequal : centers (bodyOrder index) = sourceBody index <;>
      simp only [Function.comp_apply, hequal, if_true, if_false]

theorem actualKernel_bound (security : ℕ) {r s : ℕ} (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    |(actualKernel security sourcePrimary sourceBody).val colors centers| ≤ 1 := by
  rw [actualKernel_formula]
  apply RationalFamilyProductProgram.average_bound
  intro primaryOrder bodyOrder
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  have hproduct {Index Color : Type} [Fintype Index] [Fintype Color] (law : FiniteDist Color)
      (source output : Index → Color) :
      (∏ index, |(if output index = source index then (1 : ℝ) else 0) - law.weight (source index)|) ≤ 1 := by
    apply Finset.prod_le_one
    · intro _ _
      exact abs_nonneg _
    · intro index _
      have hlo := law.nonneg (source index)
      have hhi := law.atom_le_one (source index)
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul (hproduct (primaryLaw security) sourcePrimary (fun index => colors (primaryOrder index)))
    (hproduct (bodyReference security) sourceBody (fun index => centers (bodyOrder index)))
    (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem bodyDelta_cast (security bits : ℕ) (source color : SafePalette security) :
    (bodyDelta security bits source.val.val color.val.val : ℝ) =
      (if color = source then (1 : ℝ) else 0) -
        (RationalProposalProgram.approximateBodyReference security bits).weight source := by
  unfold bodyDelta
  by_cases hequal : color = source
  · subst color
    simp only [if_true, Rat.cast_sub, Rat.cast_one]
    rfl
  · have hne : color.val.val ≠ source.val.val := fun h => hequal (Subtype.ext (Fin.ext h))
    simp only [if_neg hne, if_neg hequal, Rat.cast_sub, Rat.cast_zero]
    rfl

theorem bodyDelta_bound (security bits : ℕ) (source color : SafePalette security) :
    |(bodyDelta security bits source.val.val color.val.val : ℝ)| ≤ 1 := by
  rw [bodyDelta_cast]
  have hlo := (RationalProposalProgram.approximateBodyReference security bits).nonneg source
  have hhi := (RationalProposalProgram.approximateBodyReference security bits).atom_le_one source
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem bodyDelta_error (security bits : ℕ) (source color : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(bodyDelta security bits source.val.val color.val.val : ℝ) -
      ((if color = source then (1 : ℝ) else 0) - (bodyReference security).weight source)| ≤
      (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits) := by
  rw [bodyDelta_cast]
  have h := RationalProposalProgram.bodyReference_error security bits source hprecision hbudget
  have hequal : ((if color = source then (1 : ℝ) else 0) -
      (RationalProposalProgram.approximateBodyReference security bits).weight source) -
      ((if color = source then (1 : ℝ) else 0) - (bodyReference security).weight source) =
        (bodyReference security).weight source - (RationalProposalProgram.approximateBodyReference security bits).weight source := by ring
  rw [hequal, abs_sub_comm]
  exact h

private theorem product_bound {Index : Type} [Fintype Index] (value : Index → ℝ)
    (hvalue : ∀ index, |value index| ≤ 1) : |∏ index, value index| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun index _ => hvalue index)

def errorConstant (security r s : ℕ) : ℝ :=
  r * RationalRootMassProgram.primaryErrorConstant security +
    s * (RationalRootMassProgram.primaryErrorConstant security * Parameters.modulus security + 2)

theorem current_error (security bits r s : ℕ) (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (colors : Fin r → Palette security) (centers : Fin s → SafePalette security) :
    |(current security bits r s (fun index => (sourcePrimary index).val) (fun index => (sourceBody index).val.val)
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (actualKernel security sourcePrimary sourceBody).val colors centers| ≤
      errorConstant security r s * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let Cp := RationalRootMassProgram.primaryErrorConstant security
  let Cb : ℝ := Cp * Parameters.modulus security + 2
  have he : 0 ≤ epsilon := by positivity
  have hp : 0 ≤ Cp := by unfold Cp RationalRootMassProgram.primaryErrorConstant; positivity
  have hb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  rw [current, RationalFamilyProductProgram.average_cast, actualKernel_formula,
    RationalFamilyProductProgram.average_sub]
  apply RationalFamilyProductProgram.average_bound
  intro primaryOrder bodyOrder
  simp only [Rat.cast_mul, Rat.cast_prod]
  let a : Fin r → ℝ := fun index =>
    (RationalPrimaryColumnProgram.centerDelta security bits (sourcePrimary index).val (colors (primaryOrder index)).val : ℝ)
  let b : Fin s → ℝ := fun index =>
    (bodyDelta security bits (sourceBody index).val.val (centers (bodyOrder index)).val.val : ℝ)
  let x : Fin r → ℝ := fun index => (if colors (primaryOrder index) = sourcePrimary index then 1 else 0) -
    (primaryLaw security).weight (sourcePrimary index)
  let y : Fin s → ℝ := fun index => (if centers (bodyOrder index) = sourceBody index then 1 else 0) -
    (bodyReference security).weight (sourceBody index)
  have ha (index : Fin r) : |a index| ≤ 1 := RationalPrimaryColumnProgram.centerDelta_bound security bits _ _
  have hb' (index : Fin s) : |b index| ≤ 1 := bodyDelta_bound security bits _ _
  have hx (index : Fin r) : |x index| ≤ 1 := by
    simpa only [RationalPrimaryColumnProgram.actual_centerDelta] using
      RationalPrimaryColumnProgram.actual_centerDelta_bound security (sourcePrimary index) (colors (primaryOrder index))
  have hy (index : Fin s) : |y index| ≤ 1 := by
    have hlo := (bodyReference security).nonneg (sourceBody index)
    have hhi := (bodyReference security).atom_le_one (sourceBody index)
    dsimp only [y]
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have haprod := RationalTensorInverseProgram.product_difference_bound Finset.univ a x 1 (Cp * epsilon)
    (by norm_num) (by positivity) (fun index _ => ha index) (fun index _ => hx index)
    (fun index _ => by
      simpa only [RationalPrimaryColumnProgram.actual_centerDelta] using
        RationalPrimaryColumnProgram.centerDelta_error security bits (sourcePrimary index) (colors (primaryOrder index)) hprecision hbudget)
  have hbprod := RationalTensorInverseProgram.product_difference_bound Finset.univ b y 1 (Cb * epsilon)
    (by norm_num) (by positivity) (fun index _ => hb' index) (fun index _ => hy index)
    (fun index _ => bodyDelta_error security bits _ _ hprecision hbudget)
  simp only [Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at haprod hbprod
  change |(∏ index, a index) * (∏ index, b index) - (∏ index, x index) * (∏ index, y index)| ≤ _
  calc
    _ = |((∏ index, a index) - ∏ index, x index) * (∏ index, b index) +
      (∏ index, x index) * ((∏ index, b index) - ∏ index, y index)| := by congr 1; ring
    _ ≤ |(∏ index, a index) - ∏ index, x index| * |∏ index, b index| +
      |∏ index, x index| * |(∏ index, b index) - ∏ index, y index| := by
        simpa only [abs_mul] using abs_add_le
          (((∏ index, a index) - ∏ index, x index) * (∏ index, b index))
          ((∏ index, x index) * ((∏ index, b index) - ∏ index, y index))
    _ ≤ ((r : ℝ) * (Cp * epsilon)) * 1 + 1 * ((s : ℝ) * (Cb * epsilon)) :=
      add_le_add (mul_le_mul haprod (product_bound b hb') (abs_nonneg _) (by positivity))
        (mul_le_mul (product_bound x hx) hbprod (abs_nonneg _) (by norm_num))
    _ = _ := by unfold errorConstant; dsimp only [Cp, Cb, epsilon]; ring

theorem decode_single_weighted (security order : ℕ)
    (source : CalibrationPointCoordinates.PointIndex (Palette security) (SafePalette security) order) :
    CalibrationPointCoordinates.decode (primaryLaw security) (bodyReference security)
      (primaryReference_positive security) (bodyReference_positive security) order (Pi.single source 1) =
      Pi.single (M := fun arity : TruncatedArity order =>
        canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val)
        source.1 (actualKernel security source.2.1 source.2.2) := by
  rw [CalibrationPointCoordinates.decode_single, ← Pi.single_smul]
  rfl

end
end CurrentAFT.WeightedPointKernelProgram

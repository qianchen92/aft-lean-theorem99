import CurrentAFT.RationalOrdinaryProfileProgram
import CurrentAFT.WeightedPointKernelProgram

/-! # Literal ordinary hybrid coefficient tables before the outer root sums -/
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def first (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (RationalOrdinaryProfileProgram.density security bits source root) (fun _ => 0)

def bodyFirst (security bits order source : ℕ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (fun _ => 0) (WeightedPointKernelProgram.bodyDelta security bits source)

def atRoot (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (first security bits order source root) (RationalSingletonProgram.inverse security bits order .free 0)

def independent (security bits order source : ℕ) : Table ℚ ℕ ℕ order :=
  product order (bodyFirst security bits order source) (RationalSingletonProgram.inverse security bits order .free 0)

def mean (security bits order source : ℕ) : Table ℚ ℕ ℕ order := fun arity colors centers =>
  ∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val * atRoot security bits order source root.val arity colors centers

def current (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  independent security bits order source + atRoot security bits order source root - mean security bits order source

noncomputable section
open scoped Classical
local instance ordinaryFamilyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinaryFamilySafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus

def firstActual (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security) :
    BackgroundFamilies.ActualFamily security order :=
  LocalRaisingLinear.primaryEmbeddingLinear security order horder
    ⟨RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1),
      RootReferenceColumns.ordinaryDensityAt_mean security root (Pi.single source 1)⟩

theorem first_data (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security) :
    RationalBackgroundTable.firstTable order (RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1))
      (fun _ : SafePalette security => 0) = fun arity => (firstActual security order horder source root arity).val :=
  RationalSingletonProgram.firstTable_primary _ _ _ _ _ _

theorem firstError_nonneg (security : ℕ) : 0 ≤ RationalOrdinaryProfileProgram.errorConstant security := by
  unfold RationalOrdinaryProfileProgram.errorConstant RationalOrdinaryProfileProgram.profileErrorConstant
    RationalBackgroundDensities.centerErrorConstant
  positivity [RationalMassLiftProgram.errorConstant_nonneg security, RationalTensorInverseProgram.actualBound_nonneg security]

theorem first_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (first security bits order source.val.val root.val) arity colors centers -
      (firstActual security order horder source root arity).val colors centers| ≤
      RationalOrdinaryProfileProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := RationalBackgroundTable.firstTable_error order
    (RationalOrdinaryProfileProgram.density security bits source.val.val root.val) (fun _ => 0)
    (RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1)) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalOrdinaryProfileProgram.errorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [firstError_nonneg security]) (by norm_num)
    (RationalOrdinaryProfileProgram.density_error security bits source root hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [first_data security order horder source root] at h
  simpa only [interpret, realTable, pullback, first, add_zero] using h

theorem body_data (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    RationalBackgroundTable.firstTable order (fun _ : Palette security => 0)
      (centerLinear (bodyReference security) (Pi.single source 1)) =
      fun arity => (RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val := by
  have hz : ∑ color, (primaryLaw security).weight color * (0 : ℝ) = 0 := by simp
  have hk : BackgroundFamilies.primaryKernel (primaryLaw security) (bodyReference security) (fun _ => 0) hz = 0 := by
    apply Subtype.ext; rfl
  rw [RationalBackgroundTable.firstTable_actual _ _ _ _ _ _ hz (center_mean _ _)]
  simp only [BackgroundFamilies.primaryFamily, hk, Pi.single_zero, zero_add]
  rfl

theorem body_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (bodyFirst security bits order source.val.val) arity colors centers -
      (RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val colors centers| ≤
      RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hcenter (color : SafePalette security) : centerLinear (bodyReference security) (Pi.single source 1) color =
      (if color = source then 1 else 0) - (bodyReference security).weight source := by
    simp [centerLinear, FiniteDist.expectation, Pi.single_apply, mul_ite]
  have hd (color : SafePalette security) :
      |(WeightedPointKernelProgram.bodyDelta security bits source.val.val color.val.val : ℝ) -
        centerLinear (bodyReference security) (Pi.single source 1) color| ≤
        RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits) := by
    rw [hcenter]
    exact WeightedPointKernelProgram.bodyDelta_error security bits source color hprecision hbudget
  have h := RationalBackgroundTable.firstTable_error order (fun _ => 0)
    (WeightedPointKernelProgram.bodyDelta security bits source.val.val) (fun _ : Palette security => 0)
    (centerLinear (bodyReference security) (Pi.single source 1)) Fin.val (fun color : SafePalette security => color.val.val)
    0 (RationalBackgroundDensities.centerErrorConstant security * (1 / (2 : ℝ)^bits)) (by norm_num)
    (by unfold RationalBackgroundDensities.centerErrorConstant; positivity) (by intro; simp) hd arity colors centers
  rw [body_data security order horder source] at h
  simpa only [interpret, realTable, pullback, bodyFirst, zero_add] using h

theorem centeredDelta_bound {Color : Type*} [Fintype Color] (law : FiniteDist Color) (source color : Color) :
    |centerLinear law (Pi.single source 1) color| ≤ 1 := by
  have hlo := law.nonneg source
  have hhi := law.atom_le_one source
  simp only [centerLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem push_bound {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : FiniteDist Source) (embedding : Source → Output) (score : Source → ℝ)
    (hscore : ∀ source, |score source| ≤ 1) (output : Output) :
    |SelectedOrdinaryRoot.pushLinear law embedding score output| ≤ 1 := by
  change |∑ source, if embedding source = output then law.weight source * score source else 0| ≤ 1
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ source, law.weight source := by
      apply Finset.sum_le_sum
      intro source _
      split_ifs
      · rw [abs_mul, abs_of_nonneg (law.nonneg source)]
        exact (mul_le_mul_of_nonneg_left (hscore source) (law.nonneg source)).trans_eq (mul_one _)
      · simpa only [abs_zero] using law.nonneg source
    _ = 1 := law.sum_one

theorem actual_density_bound (security : ℕ) (source : SafePalette security) (root : Root security) (output : Palette security) :
    |RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1) output| ≤ RationalTensorInverseProgram.actualBound security := by
  have hprofile (color : Palette security) :
      |RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) (Pi.single source 1)) color| ≤ 1 :=
    push_bound (bodyReference security) _ _ (centeredDelta_bound (bodyReference security) source) color
  have h := RationalMassLiftProgram.actual_bound security _ 1 (by norm_num) hprofile output
  simpa only [mul_one] using h

theorem actual_first_bound (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(firstActual security order horder source root arity).val colors centers| ≤ RationalTensorInverseProgram.actualBound security := by
  rw [← congrFun (congrFun (congrFun (first_data security order horder source root) arity) colors) centers]
  exact RationalSingletonProgram.firstTable_bound _ _ _ (RationalTensorInverseProgram.actualBound_nonneg security)
    (actual_density_bound security source root) arity colors centers

theorem actual_body_bound (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RaisingChannels.bodyLeading security order horder (Pi.single source 1) arity).val colors centers| ≤ 1 := by
  rw [← congrFun (congrFun (congrFun (body_data security order horder source) arity) colors) centers]
  unfold RationalBackgroundTable.firstTable
  split_ifs
  · norm_num
  · exact centeredDelta_bound (bodyReference security) source _
  · norm_num

end
end CurrentAFT.RationalOrdinaryFamilyProgram

import CurrentAFT.RationalRootProfileProgram
import CurrentAFT.RationalBackgroundTable
import CurrentAFT.RationalNormalizedPrimaryProgram

/-! # Rational pure-primary singleton columns and their actual finite reciprocals -/
namespace CurrentAFT.RationalSingletonProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RootTaggedLocal
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def first (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (RationalRootProfileProgram.firstDensity security bits role queue root) (fun _ => 0)

def positive (security bits order : ℕ) (role : BodyRole) (queue : ℤ) : Table ℚ ℕ ℕ order :=
  unit order + RationalBackgroundTable.firstTable order (RationalRootProfileProgram.meanDensity security bits role queue) (fun _ => 0)

def inverse (security bits order : ℕ) (role : BodyRole) (queue : ℤ) : Table ℚ ℕ ℕ order :=
  reciprocal order (positive security bits order role queue)

def current (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (first security bits order role queue root) (inverse security bits order role queue)

noncomputable section
open scoped Classical
local instance programFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem firstTable_primary {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    RationalBackgroundTable.firstTable order density (fun _ : Body => 0) =
      fun arity => (BackgroundFamilies.primaryFamily primary body order horder density hcenter arity).val := by
  have hz : ∑ color, body.weight color * (0 : ℝ) = 0 := by simp
  have hk : BackgroundFamilies.bodyKernel primary body (fun _ => 0) hz = 0 := by
    apply Subtype.ext
    rfl
  rw [RationalBackgroundTable.firstTable_actual primary body order horder density (fun _ => 0) hcenter hz]
  simp only [BackgroundFamilies.bodyFamily, hk, Pi.single_zero, add_zero]

theorem massCertificate_one (security order : ℕ) (horder : 1 ≤ order)
    (profile : Palette security → ℝ) (hzero : ∑ color, profile color = 0) :
    PrimaryMassFamilies.massCertificateFamily security order 1 horder
      (PrimaryMassFamilies.oneWordProfile profile)
      (PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (PrimaryMassFamilies.oneWordProfile_symmetric profile) =
      BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
        (RationalMassLiftProgram.actual security profile)
        (by
          change (primaryLaw security).expectation (RationalMassLiftProgram.actual security profile) = 0
          rw [RationalMassLiftProgram.actual, LinearMap.comp_apply,
            PrimaryTensorInverse.densityInverse_mean, profileDensity_mean, hzero, mul_zero]) := by
  unfold PrimaryMassFamilies.massCertificateFamily BackgroundFamilies.primaryFamily
  change Pi.single (M := fun arity : TruncatedArity order =>
      canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val)
    (BackgroundFamilies.primaryArity order horder)
    (PrimaryMassFamilies.massLiftKernel security 1 (PrimaryMassFamilies.oneWordProfile profile)
      (PrimaryMassFamilies.oneWordProfile_centered profile hzero)
      (PrimaryMassFamilies.oneWordProfile_symmetric profile)) = _
  congr 1
  apply Subtype.ext
  funext colors centers
  exact RationalMassLiftProgram.massLift_one security profile colors

theorem positiveAtom_data (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    RationalBackgroundTable.firstTable order
      (RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue))
      (fun _ : SafePalette security => 0) =
      fun arity => (RootMeanPrimary.positiveAtom security order horder role queue arity).val := by
  unfold RootMeanPrimary.positiveAtom
  rw [massCertificate_one security order horder _ (RootMeanPrimary.meanProfile_mass security role queue)]
  exact firstTable_primary _ _ _ _ _ _

theorem first_data (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) :
    RationalBackgroundTable.firstTable order (RootReferenceColumns.singletonDensityAt security role queue root)
      (fun _ : SafePalette security => 0) =
      fun arity => (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val := by
  exact firstTable_primary _ _ _ _ _ _

theorem first_error (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(first security bits order role queue root.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val colors centers| ≤
      RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := RationalBackgroundTable.firstTable_error order
    (RationalRootProfileProgram.firstDensity security bits role queue root.val) (fun _ => 0)
    (RootReferenceColumns.singletonDensityAt security role queue root) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalRootProfileProgram.firstErrorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [(RationalRootProfileProgram.densityError_nonneg security).1]) (by norm_num)
    (RationalRootProfileProgram.firstDensity_error security bits role queue root hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [first_data security order horder role queue root] at h
  simpa only [first, add_zero] using h

theorem positive_error (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order role queue arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootMeanPrimary.positiveFamily security order horder role queue arity).val colors centers| ≤
      RationalRootProfileProgram.meanErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have h := RationalBackgroundTable.firstTable_error order
    (RationalRootProfileProgram.meanDensity security bits role queue) (fun _ => 0)
    (RationalMassLiftProgram.actual security (RootMeanPrimary.meanProfile security role queue)) (fun _ : SafePalette security => 0)
    Fin.val (fun color : SafePalette security => color.val.val)
    (RationalRootProfileProgram.meanErrorConstant security * (1 / (2 : ℝ)^bits)) 0
    (by positivity [(RationalRootProfileProgram.densityError_nonneg security).2]) (by norm_num)
    (RationalRootProfileProgram.meanDensity_error security bits role queue hfirst hprecision hbudget)
    (by intro; simp) arity colors centers
  rw [positiveAtom_data security order horder role queue] at h
  have hu := RationalPositiveFamilyProgram.unit_point_cast order security arity colors centers
  have huActual := congrFun (congrFun (congrFun
    (unit_actual (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [huActual] at hu
  simpa only [positive, Pi.add_apply, Rat.cast_add, hu, RootMeanPrimary.positiveFamily,
    Submodule.coe_add, Pi.add_apply, add_sub_add_left_eq_sub, add_zero] using h

theorem firstTable_bound {Primary Body : Type*} (order : ℕ) (density : Primary → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hdensity : ∀ color, |density color| ≤ bound)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |RationalBackgroundTable.firstTable order density (fun _ => 0) arity colors centers| ≤ bound := by
  unfold RationalBackgroundTable.firstTable
  split_ifs
  · exact hdensity _
  · simpa only [abs_zero] using hb
  · simpa only [abs_zero] using hb

theorem profile_bounds (security : ℕ) (role : BodyRole) (queue : ℤ) (root : CycleRootExpansion.Root security)
    (output : Palette security) : |deviationProfile security role queue root output| ≤ 2 ∧
      |RootMeanPrimary.meanProfile security role queue output| ≤ 2 := by
  have hatom (law : FiniteDist (Palette security)) : |law.weight output| ≤ 1 := by
    rw [abs_of_nonneg (law.nonneg output)]
    exact law.atom_le_one output
  constructor
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))
  · exact (abs_sub _ _).trans ((add_le_add (hatom _) (hatom _)).trans_eq (by norm_num))

def firstBound (security : ℕ) : ℝ := 2 * RationalTensorInverseProgram.actualBound security

def positiveBound (security : ℕ) : ℝ := 1 + firstBound security

theorem firstBound_nonneg (security : ℕ) : 0 ≤ firstBound security := by
  exact mul_nonneg (by norm_num) (RationalTensorInverseProgram.actualBound_nonneg security)

theorem actual_first_bound (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val colors centers| ≤ firstBound security := by
  rw [← congrFun (congrFun (congrFun (first_data security order horder role queue root) arity) colors) centers]
  apply firstTable_bound _ _ _ (firstBound_nonneg security)
  intro output
  exact (RationalMassLiftProgram.actual_bound security (deviationProfile security role queue root) 2 (by norm_num)
    (fun color => (profile_bounds security role queue root color).1) output).trans_eq (by unfold firstBound; ring)

theorem actual_positive_bound (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootMeanPrimary.positiveFamily security order horder role queue arity).val colors centers| ≤ positiveBound security := by
  have hm : |(RootMeanPrimary.positiveAtom security order horder role queue arity).val colors centers| ≤ firstBound security := by
    rw [← congrFun (congrFun (congrFun (positiveAtom_data security order horder role queue) arity) colors) centers]
    apply firstTable_bound _ _ _ (firstBound_nonneg security)
    intro output
    exact (RationalMassLiftProgram.actual_bound security (RootMeanPrimary.meanProfile security role queue) 2 (by norm_num)
      (fun color => (profile_bounds security role queue 0 color).2) output).trans_eq (by unfold firstBound; ring)
  have hu : |((1 : LocalCoefficientFamily.Family security order) arity).val colors centers| ≤ 1 := by
    rw [← congrFun (congrFun (congrFun (unit_actual (primaryLaw security) (bodyReference security) order) arity) colors) centers]
    unfold unit
    split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hu hm)

theorem inverse_lifted (security bits order : ℕ) (role : BodyRole) (queue : ℤ) :
    RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue) =
      reciprocal order (RationalNormalizedPrimaryProgram.lifted security order (positive security bits order role queue)) := by
  unfold RationalNormalizedPrimaryProgram.lifted inverse
  rw [reciprocal_cast, pullback_reciprocal]

theorem inverse_actual (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    reciprocal order (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val) =
      fun arity => (RootMeanPrimary.positiveInverse security order horder role queue arity).val := by
  rw [reciprocal_actual]
  rfl

def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + positiveBound security) 0)^order

theorem actual_inverse_bound (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootMeanPrimary.positiveInverse security order horder role queue arity).val colors centers| ≤ inverseBound security order := by
  have h := reciprocal_bound order (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val)
    (positiveBound security) (by unfold positiveBound; positivity [firstBound_nonneg security])
    (actual_positive_bound security order horder role queue) arity colors centers
  rw [inverse_actual] at h
  exact h

def inverseErrorConstant (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * RationalRootProfileProgram.meanErrorConstant security *
    (growth order (1 + positiveBound security) (RationalRootProfileProgram.meanErrorConstant security))^(order + 1)

theorem inverse_error (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(inverse security bits order role queue arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootMeanPrimary.positiveInverse security order horder role queue arity).val colors centers| ≤
      inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let E := RationalRootProfileProgram.meanErrorConstant security
  let A := positiveBound security
  have he : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := (RationalRootProfileProgram.densityError_nonneg security).2
  have hA : 0 ≤ A := by unfold A positiveBound; positivity [firstBound_nonneg security]
  have h := reciprocal_error order
    (fun arity => (RootMeanPrimary.positiveFamily security order horder role queue arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (positive security bits order role queue)) A (E * epsilon) hA (by positivity)
    (actual_positive_bound security order horder role queue)
    (positive_error security bits order horder role queue hfirst hprecision hbudget) arity colors centers
  rw [← inverse_lifted, inverse_actual] at h
  have hsmall : E * epsilon ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) hE
  have hg : growth order (1 + A) (E * epsilon) ≤ growth order (1 + A) E := by unfold growth; gcongr
  have hg0 : 0 ≤ growth order (1 + A) (E * epsilon) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (growth_ge_one order (1 + A) (E * epsilon) (by positivity) (by positivity))
  calc
    _ ≤ _ := h
    _ ≤ ((order + 1 : ℕ) : ℝ)^2 * (E * epsilon) * (growth order (1 + A) E)^(order + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg _) (by positivity)
    _ = _ := by unfold inverseErrorConstant; dsimp only [E, A, epsilon]; ring

theorem current_lifted (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) :
    RationalNormalizedPrimaryProgram.lifted security order (current security bits order role queue root) =
      product order (RationalNormalizedPrimaryProgram.lifted security order (first security bits order role queue root))
        (RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue)) := by
  unfold RationalNormalizedPrimaryProgram.lifted current
  rw [product_cast, pullback_product]

def errorConstant (security order : ℕ) : ℝ :=
  (Nat.card (TruncatedArity order) : ℝ)^2 *
    (RationalRootProfileProgram.firstErrorConstant security * inverseBound security order +
      (firstBound security + RationalRootProfileProgram.firstErrorConstant security) * inverseErrorConstant security order)

theorem current_error (security bits order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (root : CycleRootExpansion.Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(current security bits order role queue root.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootReferenceColumns.singletonAt security order horder role queue root arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let eN := RationalRootProfileProgram.firstErrorConstant security
  let eI := inverseErrorConstant security order
  let A := firstBound security
  let B := inverseBound security order
  have he : 0 ≤ epsilon := by positivity
  have heN : 0 ≤ eN := (RationalRootProfileProgram.densityError_nonneg security).1
  have hA : 0 ≤ A := firstBound_nonneg security
  have hpos : 0 ≤ positiveBound security := by unfold positiveBound; positivity
  have hg : 1 ≤ growth order (1 + positiveBound security) 0 := growth_ge_one _ _ _ (by positivity) (by norm_num)
  have hB : 0 ≤ B := by unfold B inverseBound; positivity
  have hE := (RationalRootProfileProgram.densityError_nonneg security).2
  have hgE := growth_ge_one order (1 + positiveBound security) (RationalRootProfileProgram.meanErrorConstant security)
    (by positivity) hE
  have heI : 0 ≤ eI := by unfold eI inverseErrorConstant; positivity
  have h := product_error order
    (fun arity => (RootReferenceColumns.singletonFirstAt security order horder role queue root arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (first security bits order role queue root.val))
    (fun arity => (RootMeanPrimary.positiveInverse security order horder role queue arity).val)
    (RationalNormalizedPrimaryProgram.lifted security order (inverse security bits order role queue)) A B (eN * epsilon) (eI * epsilon)
    hA hB (by positivity) (by positivity) (actual_first_bound security order horder role queue root)
    (actual_inverse_bound security order horder role queue)
    (first_error security bits order horder role queue root hfirst hprecision hbudget)
    (inverse_error security bits order horder role queue hfirst hprecision hbudget) arity colors centers
  rw [← current_lifted, product_actual] at h
  simp only [Fintype.card_eq_nat_card] at h
  have hsmall : eN * epsilon ≤ eN := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (RationalCoefficientExtraction.epsilon_le_one bits) heN
  calc
    _ ≤ _ := h
    _ ≤ (Nat.card (TruncatedArity order) : ℝ)^2 *
        ((eN * epsilon) * B + (A + eN) * (eI * epsilon)) := by gcongr
    _ = _ := by unfold errorConstant; dsimp only [eN, eI, A, B, epsilon]; ring

end
end CurrentAFT.RationalSingletonProgram

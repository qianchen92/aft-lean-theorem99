import CurrentAFT.OrdinaryRaising
import CurrentAFT.CompleteRaising
import CurrentAFT.CoefficientHilbert
import AFT.DependentTensorChannel

/-! # Actual local Hilbert channels for both kinds of selected controls -/
namespace CurrentAFT.RaisingChannels

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily
  LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryProjection (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] centeredScores security :=
  (centerLinear (primaryLaw security)).codRestrict (centeredScores security) (fun score => center_mean _ score)

def bodyProjection (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] OrdinaryRaising.centeredBodyScores security :=
  (centerLinear (bodyReference security)).codRestrict (OrdinaryRaising.centeredBodyScores security) (fun score => center_mean _ score)

def primaryLeading (security order : ℕ) (horder : 1 ≤ order) : (Palette security → ℝ) →ₗ[ℝ] Family security order :=
  (primaryEmbeddingLinear security order horder).comp (primaryProjection security)

def primaryRaised (security order : ℕ) (horder : 1 ≤ order) : (Palette security → ℝ) →ₗ[ℝ] Family security order :=
  (localRaisingLinear security order horder).comp (primaryProjection security)

def bodyLeading (security order : ℕ) (horder : 1 ≤ order) : (SafePalette security → ℝ) →ₗ[ℝ] Family security order :=
  (OrdinaryRaising.bodyEmbeddingLinear security order horder).comp (bodyProjection security)

def bodyRaised (security order : ℕ) (horder : 1 ≤ order) : (SafePalette security → ℝ) →ₗ[ℝ] Family security order :=
  (OrdinaryRaising.raisingLinear security order horder).comp (bodyProjection security)

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

theorem primaryLeading_norm (security order : ℕ) (horder : 1 ≤ order) (score : Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (primaryLeading security order horder score) ≤
      BackgroundRates.primaryFactor security * Real.sqrt ((primaryLaw security).l2Sq score) := by
  change LocalRaisingBounds.coefficientNorm security order
    (BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
      (centerLinear (primaryLaw security) score) (center_mean _ score)) ≤ _
  rw [LocalRaisingBounds.coefficientNorm, BackgroundFamilies.primaryFamily_norm]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (primaryFactor_nonneg security)

theorem primaryRaised_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) (score : Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (primaryRaised security order horder score) ≤
      (raisingConstant / (Parameters.base security : ℝ) ^ 102) * Real.sqrt ((primaryLaw security).l2Sq score) := by
  have h := localRaising_bound security order horder hlarge (centerLinear (primaryLaw security) score) (center_mean _ score)
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (by
    unfold raisingConstant
    exact div_nonneg (mul_nonneg (by norm_num) (add_nonneg higherConstant_nonneg positiveConstant_nonneg))
      (pow_nonneg (FirstResponse.base_pos security).le _))

theorem bodyLeading_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (bodyLeading security order horder score) ≤
      BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score) := by
  change LocalRaisingBounds.coefficientNorm security order
    (BackgroundFamilies.bodyFamily (primaryLaw security) (bodyReference security) order horder
      (centerLinear (bodyReference security) score) (center_mean _ score)) ≤ _
  rw [LocalRaisingBounds.coefficientNorm, BackgroundFamilies.bodyFamily_norm]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (bodyFactor_nonneg security)

theorem bodyRaised_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (bodyRaised security order horder score) ≤
      ((80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security) *
        Real.sqrt ((bodyReference security).l2Sq score) := by
  have h := OrdinaryRaising.raisingFamily_norm security order horder (centerLinear (bodyReference security) score) (center_mean _ score)
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score))
    (mul_nonneg (by positivity) (bodyFactor_nonneg security))

theorem centerLinear_single {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source : Color) :
    centerLinear law (Pi.single source 1) = law.weight source • Hoeffding.centeredAtom law source := by
  classical
  have hmean : law.expectation (Pi.single source 1) = law.weight source := by
    simp [FiniteDist.expectation, Pi.single_apply]
  funext color
  change (Pi.single source (1 : ℝ) : Color → ℝ) color - law.expectation (Pi.single source 1) = _
  rw [hmean]
  by_cases hequal : color = source
  · subst color
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Hoeffding.centeredAtom, if_true]
    field_simp [(hpositive source).ne']
  · simp only [Pi.single_eq_of_ne hequal, Pi.smul_apply, smul_eq_mul, Hoeffding.centeredAtom,
      Ne.symm hequal, if_false]
    ring

theorem primaryProjection_single (security : ℕ) (source : Palette security) :
    primaryProjection security (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.primaryAtom security source := by
  apply Subtype.ext
  exact centerLinear_single _ (primaryReference_positive security) source

theorem bodyProjection_single (security : ℕ) (source : SafePalette security) :
    bodyProjection security (Pi.single source 1) =
      (bodyReference security).weight source • CompleteRaising.bodyAtom security source := by
  apply Subtype.ext
  funext color
  change centerLinear (bodyReference security) (Pi.single source 1) color =
    (bodyReference security).weight source * Hoeffding.centeredAtom (bodyReference security) source color
  exact congrFun (centerLinear_single _ (bodyReference_positive security) source) color

theorem primaryLeading_single (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    primaryLeading security order horder (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.primaryPoint security order horder source := by
  unfold primaryLeading
  rw [LinearMap.comp_apply, primaryProjection_single, map_smul]
  rfl

theorem primaryRaised_single (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    primaryRaised security order horder (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.raisedPoint security order horder source := by
  unfold primaryRaised
  rw [LinearMap.comp_apply, primaryProjection_single, map_smul]
  rfl

theorem bodyLeading_single (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    bodyLeading security order horder (Pi.single source 1) =
      (bodyReference security).weight source • GlobalRaising.bodyPoint security order horder source := by
  unfold bodyLeading
  rw [LinearMap.comp_apply, bodyProjection_single, map_smul]
  rfl

theorem bodyRaised_single (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    bodyRaised security order horder (Pi.single source 1) =
      (bodyReference security).weight source • CompleteRaising.ordinaryRaisedPoint security order horder source := by
  unfold bodyRaised
  rw [LinearMap.comp_apply, bodyProjection_single, map_smul]
  rfl

section Fibers
variable {Primary Body Input : Type*} [Fintype Primary] [Fintype Body] [Fintype Input]

def outputReference (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (arity : TruncatedArity order) :=
  (FiniteDist.independent (fun _ : Fin arity.val.1.val => primary)).prod
    (FiniteDist.independent (fun _ : Fin arity.val.2.val => body))

def fiberLinear (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (arity : TruncatedArity order) :
    KernelFamily primary body order →ₗ[ℝ]
      (((Fin arity.val.1.val → Primary) × (Fin arity.val.2.val → Body)) → ℝ) where
  toFun family word := (family arity).val word.1 word.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fiber_weighted_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (arity : TruncatedArity order) (family : KernelFamily primary body order) :
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      Real.sqrt ((outputReference primary body order arity).l2Sq (fiberLinear primary body order arity family)) ≤
        familyNorm primary body order primaryFactor bodyFactor family := by
  change gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
    blockL2 primary body (family arity).val ≤ _
  unfold familyNorm
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun other : TruncatedArity order => gradeWeight primaryFactor bodyFactor other.val.1.val other.val.2.val *
      blockL2 primary body (family other).val)
    (fun other _ => mul_nonneg (gradeWeight_nonneg _ _ hprimary hbody _ _) (blockL2_nonneg primary body _))
    (Finset.mem_univ arity)

theorem fiber_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (input : FiniteDist Input) (channel : (Input → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (bound : ℝ) (hchannel : ∀ score, familyNorm primary body order primaryFactor bodyFactor (channel score) ≤
      bound * Real.sqrt (input.l2Sq score)) (arity : TruncatedArity order) (score : Input → ℝ) :
    (outputReference primary body order arity).l2Sq ((fiberLinear primary body order arity).comp channel score) ≤
      (bound / gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val) ^ 2 * input.l2Sq score := by
  let weight := gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val
  have hw : 0 < weight := by unfold weight gradeWeight; positivity
  have h := (fiber_weighted_norm_le primary body order primaryFactor bodyFactor hprimary.le hbody.le arity (channel score)).trans (hchannel score)
  have hsqrt : Real.sqrt ((outputReference primary body order arity).l2Sq
      (fiberLinear primary body order arity (channel score))) ≤
      (bound / weight) * Real.sqrt (input.l2Sq score) := by
    rw [show (bound / weight) * Real.sqrt (input.l2Sq score) =
      (bound * Real.sqrt (input.l2Sq score)) / weight by ring]
    apply (le_div_iff₀ hw).mpr
    calc
      _ = weight * Real.sqrt ((outputReference primary body order arity).l2Sq
          (fiberLinear primary body order arity (channel score))) := by ring
      _ ≤ _ := h
  have hsquared := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  simpa only [Real.sq_sqrt (FiniteDist.l2Sq_nonneg _ _), mul_pow, LinearMap.comp_apply] using hsquared

end Fibers

end
end CurrentAFT.RaisingChannels

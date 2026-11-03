import CurrentAFT.RootTaggedSelectedChannel
import CurrentAFT.BodyChannelEvaluation

/-!
# Actual selected ordinary root/control response

One root and its original safe body control are retained as a joint input.
The physical signed output is the real cyclic translate of that control.
A genuine first-primary inverse lifts its centered mass, followed by the
finite positive reciprocal of the independent ordinary output law.
-/
namespace CurrentAFT.SelectedOrdinaryRoot

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert PrimaryTensorInverse
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := Root security × SafePalette security

def inputLaw (security : ℕ) : FiniteDist (Input security) := (rootReference security).prod (bodyReference security)

section Push
variable {Source Output : Type*} [Fintype Source] [Fintype Output]

def pushLinear (law : FiniteDist Source) (embedding : Source → Output) : (Source → ℝ) →ₗ[ℝ] (Output → ℝ) where
  toFun score output := ∑ source, if embedding source = output then law.weight source * score source else 0
  map_add' first second := by
    funext output
    change (∑ source, if embedding source = output then law.weight source * (first source + second source) else 0) =
      (∑ source, if embedding source = output then law.weight source * first source else 0) +
        ∑ source, if embedding source = output then law.weight source * second source else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> ring
  map_smul' scalar score := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> ring

theorem push_test (law : FiniteDist Source) (embedding : Source → Output) (score : Source → ℝ) (test : Output → ℝ) :
    (∑ output, pushLinear law embedding score output * test output) = law.expectation (fun source => score source * test (embedding source)) := by
  simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem push_energy (law : FiniteDist Source) (embedding : Source → Output) (hinjective : Function.Injective embedding)
    (reference : Output → ℝ) (score : Source → ℝ) :
    profileSquareNorm reference (pushLinear law embedding score) =
      ∑ source, (law.weight source * score source) ^ 2 / reference (embedding source) := by
  have hpoint (output : Output) : pushLinear law embedding score output ^ 2 / reference output =
      ∑ source, if embedding source = output then (law.weight source * score source) ^ 2 / reference output else 0 := by
    by_cases hexists : ∃ source, embedding source = output
    · obtain ⟨source, hequal⟩ := hexists
      subst output
      have heq (other : Source) : embedding other = embedding source ↔ other = source := hinjective.eq_iff
      simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have hnone (source : Source) : embedding source ≠ output := fun hequal => hexists ⟨source, hequal⟩
      simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, hnone, if_false, Finset.sum_const_zero,
        zero_pow (by decide : 2 ≠ 0), zero_div]
  unfold profileSquareNorm
  simp only [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp

theorem push_energy_le (law : FiniteDist Source) (embedding : Source → Output) (hinjective : Function.Injective embedding)
    (reference : Output → ℝ) (hpositive : ∀ output, 0 < reference output) (bound : ℝ)
    (hratio : ∀ source, law.weight source ≤ bound * reference (embedding source)) (score : Source → ℝ) :
    profileSquareNorm reference (pushLinear law embedding score) ≤ bound * law.l2Sq score := by
  rw [push_energy law embedding hinjective]
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro source _
  apply (div_le_iff₀ (hpositive _)).mpr
  calc
    _ = (law.weight source * score source ^ 2) * law.weight source := by ring
    _ ≤ (law.weight source * score source ^ 2) * (bound * reference (embedding source)) :=
      mul_le_mul_of_nonneg_left (hratio source) (mul_nonneg (law.nonneg source) (sq_nonneg (score source)))
    _ = _ := by ring
end Push

def rootEmbedding (security : ℕ) (root : Root security) (center : SafePalette security) : Palette security :=
  (shiftEquiv security (root.val : ℤ)) center.val

theorem rootEmbedding_injective (security : ℕ) (root : Root security) : Function.Injective (rootEmbedding security root) :=
  (shiftEquiv security (root.val : ℤ)).injective.comp Subtype.val_injective

def sliceLinear (security : ℕ) (root : Root security) : (Input security → ℝ) →ₗ[ℝ] (SafePalette security → ℝ) where
  toFun score center := score (root, center)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rawMassLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  ∑ root : Root security, (rootReference security).weight root •
    ((pushLinear (bodyReference security) (rootEmbedding security root)).comp (sliceLinear security root))

def rawMass (security : ℕ) (score : Input security → ℝ) := rawMassLinear security score

theorem rawMass_apply (security : ℕ) (score : Input security → ℝ) (output : Palette security) :
    rawMass security score output = ∑ root, (rootReference security).weight root *
      pushLinear (bodyReference security) (rootEmbedding security root) (fun center => score (root, center)) output := by
  simp only [rawMass, rawMassLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sliceLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem rawMass_physical (security : ℕ) (score : Input security → ℝ) (test : Palette security → ℝ) :
    (∑ output, rawMass security score output * test output) =
      (inputLaw security).expectation (fun sample => score sample * test (rootEmbedding security sample.1 sample.2)) := by
  simp only [rawMass_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold inputLaw
  rw [FiniteDist.expectation_prod]
  apply Finset.sum_congr rfl
  intro root _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [push_test]

theorem rawMass_mass (security : ℕ) (score : Input security → ℝ) :
    (∑ output, rawMass security score output) = (inputLaw security).expectation score := by
  have h := rawMass_physical security score (fun _ => 1)
  simpa only [mul_one] using h

theorem fixed_uniform_energy (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    profileSquareNorm (LocalReferenceEnergy.uniformReference security).weight
      (pushLinear (bodyReference security) (rootEmbedding security root) score) ≤ 4 * (bodyReference security).l2Sq score := by
  apply push_energy_le _ _ (rootEmbedding_injective security root)
    (LocalReferenceEnergy.uniformReference security).weight
    (fun color => by rw [LocalReferenceEnergy.uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    4 (fun center => by rw [LocalReferenceEnergy.uniformReference_weight]; exact (bodyReference_upper security center).trans_eq (by ring))

theorem rawMass_uniform_energy (security : ℕ) (score : Input security → ℝ) :
    profileSquareNorm (LocalReferenceEnergy.uniformReference security).weight (rawMass security score) ≤ 4 * (inputLaw security).l2Sq score := by
  have hequal : rawMass security score = fun output => ∑ root, (rootReference security).weight root *
      pushLinear (bodyReference security) (rootEmbedding security root) (fun center => score (root, center)) output :=
    funext (rawMass_apply security score)
  rw [hequal]
  apply (profileSquareNorm_average_le (rootReference security) (LocalReferenceEnergy.uniformReference security).weight
    (LocalReferenceEnergy.uniformReference security).nonneg _).trans
  calc
    _ ≤ ∑ root, (rootReference security).weight root * (4 * (bodyReference security).l2Sq (fun center => score (root, center))) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left (fixed_uniform_energy security root _) ((rootReference security).nonneg root))
    _ = _ := by
      change (rootReference security).expectation (fun root => 4 * (bodyReference security).l2Sq (fun center => score (root, center))) = _
      rw [FiniteDist.expectation_const_mul]
      unfold inputLaw FiniteDist.l2Sq
      rw [FiniteDist.expectation_prod]

theorem rawMass_primary_energy (security : ℕ) (score : Input security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (rawMass security score) ≤ 8 * (inputLaw security).l2Sq score :=
  (OrdinaryRaising.profile_primary_energy_le_uniform security _).trans
    ((mul_le_mul_of_nonneg_left (rawMass_uniform_energy security score) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

def controlCenterLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := centerLinear (bodyReference security) (fun center => score (sample.1, center)) sample.2
  map_add' first second := by
    funext sample
    exact congrFun ((centerLinear (bodyReference security)).map_add (fun center => first (sample.1, center)) (fun center => second (sample.1, center))) sample.2
  map_smul' scalar score := by
    funext sample
    exact congrFun ((centerLinear (bodyReference security)).map_smul scalar (fun center => score (sample.1, center))) sample.2

theorem controlCenter_energy_le (security : ℕ) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (controlCenterLinear security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  apply Finset.sum_le_sum
  intro root _
  exact mul_le_mul_of_nonneg_left (center_energy_le (bodyReference security) (fun center => score (root, center))) ((rootReference security).nonneg root)

theorem centeredMass_zero (security : ℕ) (score : Input security → ℝ) :
    (∑ output, rawMass security (controlCenterLinear security score) output) = 0 := by
  rw [rawMass_mass]
  unfold inputLaw
  rw [FiniteDist.expectation_prod]
  have hmean (root : Root security) : (bodyReference security).expectation (fun center => controlCenterLinear security score (root, center)) = 0 :=
    center_mean _ _
  simp only [hmean, FiniteDist.expectation_const]

def densityLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  (densityInverse security).comp ((diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    ((rawMassLinear security).comp (controlCenterLinear security)))

theorem densityLinear_apply (security : ℕ) (score : Input security → ℝ) :
    densityLinear security score = densityInverse security
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) := by
  apply congrArg (densityInverse security)
  funext color
  simp only [diagonal, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change ((primaryLaw security).weight color)⁻¹ * rawMass security (controlCenterLinear security score) color = _
  ring

theorem densityLinear_centered (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).expectation (densityLinear security score) = 0 := by
  rw [densityLinear_apply, densityInverse_mean]
  have hmean : (primaryLaw security).expectation
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) = 0 := by
    have hpoint (color : Palette security) : (primaryLaw security).weight color *
        (rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) =
      rawMass security (controlCenterLinear security score) color := by field_simp [(primaryReference_positive security color).ne']
    simpa only [FiniteDist.expectation, hpoint] using centeredMass_zero security score
  rw [hmean, mul_zero]

def centeredDensityLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] centeredScores security :=
  (densityLinear security).codRestrict (centeredScores security) (densityLinear_centered security)

def numeratorLinear (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (primaryEmbeddingLinear security order horder).comp (centeredDensityLinear security)

def channel (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := numeratorLinear security order horder score * OrdinaryRaising.positiveInverse security order horder
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, smul_mul_assoc, RingHom.id_apply]

end
end CurrentAFT.SelectedOrdinaryRoot

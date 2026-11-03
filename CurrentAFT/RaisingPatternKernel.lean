import CurrentAFT.RaisingPatternBudget
import CurrentAFT.GroupedKernelProductFinite

/-! # Genuine mixed-role joint tensors for each local arity pattern -/
namespace CurrentAFT.RaisingPatternKernel

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm LocalCoefficientFamily LocalRaisingBounds RaisingChannels
  RaisingPatternBudget GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def totalPrimary {r s order : ℕ} (pattern : Role r s → TruncatedArity order) : ℕ :=
  ∑ role, (pattern role).val.1.val

def totalBody {r s order : ℕ} (pattern : Role r s → TruncatedArity order) : ℕ :=
  ∑ role, (pattern role).val.2.val

abbrev primarySlots {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :=
  Fin (pattern role).val.1.val

abbrev bodySlots {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :=
  Fin (pattern role).val.2.val

def primaryEquiv {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    Sigma (primarySlots pattern) ≃ Fin (totalPrimary pattern) :=
  GroupedKernelProduct.finiteSlotsEquiv (fun role => (pattern role).val.1.val)

def bodyEquiv {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    Sigma (bodySlots pattern) ≃ Fin (totalBody pattern) :=
  GroupedKernelProduct.finiteSlotsEquiv (fun role => (pattern role).val.2.val)

def inputJoint (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s)
    (word : (role : Role r s) → RoleInput security r s role) : ℝ :=
  kernel.val (fun index => word (Sum.inl index)) (fun index => word (Sum.inr index))

theorem inputJoint_energy (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    (FiniteDist.dependentIndependent (roleReference security r s)).l2Sq (inputJoint security kernel) =
      blockEnergy (primaryLaw security) (bodyReference security) kernel.val := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => Palette security)
    (fun _ : Fin s => SafePalette security)).sum_comp]
  rw [Fintype.sum_prod_type, blockEnergy_apply]
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  simp only [FiniteDist.dependentIndependent_weight, inputJoint, roleReference,
    Fintype.prod_sum_type, Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi,
    Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr, RoleInput]

def componentChannel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s) :
    (RoleInput security r s role → ℝ) →ₗ[ℝ]
      (((primarySlots pattern role → Palette security) × (bodySlots pattern role → SafePalette security)) → ℝ) :=
  (fiberLinear (primaryLaw security) (bodyReference security) order (pattern role)).comp
    (roleChannel security order horder selected role)

theorem component_primaryCentered (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s)
    (score : RoleInput security r s role → ℝ) :
    PrimaryCentered (primaryLaw security) (fun colors centers =>
      componentChannel security order horder selected pattern role score (colors, centers)) :=
  (roleChannel security order horder selected role score (pattern role)).property.1

theorem component_bodyCentered (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s)
    (score : RoleInput security r s role → ℝ) :
    BodyCentered (bodyReference security) (fun colors centers =>
      componentChannel security order horder selected pattern role score (colors, centers)) :=
  (roleChannel security order horder selected role score (pattern role)).property.2.1

def patternKernel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    canonicalKernels (primaryLaw security) (bodyReference security) (totalPrimary pattern) (totalBody pattern) :=
  canonicalTensor (primarySlots pattern) (bodySlots pattern) (primaryLaw security) (bodyReference security)
    (primaryEquiv pattern) (bodyEquiv pattern) (componentChannel security order horder selected pattern)
      (component_primaryCentered security order horder selected pattern)
      (component_bodyCentered security order horder selected pattern) (inputJoint security kernel)

def localWeight (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) : ℝ :=
  gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (pattern role).val.1.val (pattern role).val.2.val

theorem localWeight_pos (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :
    0 < localWeight security pattern role := by
  have hp := primaryFactor_pos security
  have hb := bodyFactor_pos security
  unfold localWeight gradeWeight
  positivity

theorem weight_product (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (totalPrimary pattern) (totalBody pattern) = ∏ role, localWeight security pattern role := by
  simp only [localWeight, gradeWeight, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, totalPrimary, totalBody]

theorem patternKernel_weighted_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
        (totalPrimary pattern) (totalBody pattern) *
      blockL2 (primaryLaw security) (bodyReference security) (patternKernel security order horder selected pattern kernel).val ≤
        (∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val := by
  let bounds := fun role => roleCost security selected role / localWeight security pattern role
  have hchannel (role : Role r s) (score : RoleInput security r s role → ℝ) :
      (localReference (primarySlots pattern) (bodySlots pattern) (primaryLaw security) (bodyReference security) role).l2Sq
        (componentChannel security order horder selected pattern role score) ≤
          bounds role ^ 2 * (roleReference security r s role).l2Sq score :=
    fiber_energy_le (primaryLaw security) (bodyReference security) order _ _
      (primaryFactor_pos security) (bodyFactor_pos security) _ _ _
      (roleChannel_norm security order horder hlarge selected role) (pattern role) score
  have henergy := canonicalize_tensor_energy_le (primarySlots pattern) (bodySlots pattern)
    (primaryLaw security) (bodyReference security) (primaryEquiv pattern) (bodyEquiv pattern)
    (roleReference security r s) (componentChannel security order horder selected pattern)
    bounds hchannel (inputJoint security kernel)
  change blockEnergy (primaryLaw security) (bodyReference security)
    (patternKernel security order horder selected pattern kernel).val ≤ _ at henergy
  rw [inputJoint_energy] at henergy
  have hbounds : 0 ≤ ∏ role, bounds role :=
    Finset.prod_nonneg (fun role _ => div_nonneg (roleCost_nonneg security selected role) (localWeight_pos security pattern role).le)
  have hsqrt := Real.sqrt_le_sqrt henergy
  rw [Finset.prod_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbounds] at hsqrt
  have hweight := gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le
    (totalPrimary pattern) (totalBody pattern)
  apply (mul_le_mul_of_nonneg_left hsqrt hweight).trans_eq
  change _ = _
  rw [weight_product]
  have hcancel : (∏ role, localWeight security pattern role) * (∏ role, bounds role) =
      ∏ role, roleCost security selected role := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro role _
    dsimp only [bounds]
    field_simp [(localWeight_pos security pattern role).ne']
  rw [← mul_assoc, hcancel]
  rfl

def patternFamily (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  if hdegree : totalPrimary pattern + totalBody pattern ≤ order then
    GroupedKernelProduct.embed (primaryLaw security) (bodyReference security) order hdegree
      (patternKernel security order horder selected pattern kernel)
  else 0

theorem patternFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (patternFamily security order horder selected pattern kernel) ≤
      (∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val := by
  unfold patternFamily
  split_ifs with hdegree
  · unfold GroupedKernelProduct.embed LocalRaisingBounds.coefficientNorm
    rw [BackgroundFamilies.familyNorm_single]
    exact patternKernel_weighted_norm security order horder hlarge selected pattern kernel
  · rw [LocalRaisingBounds.coefficientNorm, GradedControlStability.familyNorm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun role _ => roleCost_nonneg security selected role)) (blockL2_nonneg _ _ _)

end
end CurrentAFT.RaisingPatternKernel

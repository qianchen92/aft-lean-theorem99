import CurrentAFT.RaisingChannels
import CurrentAFT.GroupedKernelCanonical
import CurrentAFT.GroupedKernelProductFinite

/-! # Finite-degree joint tensor synthesis of family-valued local channels -/
namespace CurrentAFT.GroupedFamilyTensor
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability GradedInverseNorm BackgroundFamilies RaisingChannels GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input : Group → Type*} [∀ group, Fintype (Input group)]

def totalPrimary (pattern : Group → TruncatedArity order) : ℕ := ∑ group, (pattern group).val.1.val
def totalBody (pattern : Group → TruncatedArity order) : ℕ := ∑ group, (pattern group).val.2.val
abbrev PS (pattern : Group → TruncatedArity order) (group : Group) := Fin (pattern group).val.1.val
abbrev BS (pattern : Group → TruncatedArity order) (group : Group) := Fin (pattern group).val.2.val

def componentChannel
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (group : Group) :=
  (fiberLinear primary body order (pattern group)).comp (channels group)

def patternKernel
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    canonicalKernels primary body (totalPrimary order pattern) (totalBody order pattern) :=
  canonicalTensor (PS order pattern) (BS order pattern) primary body
    (finiteSlotsEquiv (fun group => (pattern group).val.1.val))
    (finiteSlotsEquiv (fun group => (pattern group).val.2.val))
    (componentChannel primary body order channels pattern)
    (fun group score => (channels group score (pattern group)).property.1)
    (fun group score => (channels group score (pattern group)).property.2.1) input

def patternFamily
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) : KernelFamily primary body order :=
  if hdegree : totalPrimary order pattern + totalBody order pattern ≤ order then
    embed primary body order hdegree (patternKernel primary body order channels pattern input)
  else 0

def response
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (input : ((group : Group) → Input group) → ℝ) : KernelFamily primary body order :=
  ∑ pattern, patternFamily primary body order channels pattern input

theorem patternKernel_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    gradeWeight pf bf (totalPrimary order pattern) (totalBody order pattern) *
      blockL2 primary body (patternKernel primary body order channels pattern input).val ≤
        (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) := by
  let weight := fun group => gradeWeight pf bf (pattern group).val.1.val (pattern group).val.2.val
  have hw (group : Group) : 0 < weight group := by unfold weight gradeWeight; positivity
  let bounds := fun group => cost group / weight group
  have hchannel (group : Group) (score : Input group → ℝ) :
      (localReference (PS order pattern) (BS order pattern) primary body group).l2Sq
        (componentChannel primary body order channels pattern group score) ≤
          bounds group ^ 2 * (reference group).l2Sq score :=
    fiber_energy_le primary body order pf bf hpf hbf (reference group) (channels group) (cost group)
      (hchannels group) (pattern group) score
  have henergy := canonicalize_tensor_energy_le (PS order pattern) (BS order pattern) primary body
    (finiteSlotsEquiv (fun group => (pattern group).val.1.val))
    (finiteSlotsEquiv (fun group => (pattern group).val.2.val)) reference
    (componentChannel primary body order channels pattern) bounds hchannel input
  change blockEnergy primary body (patternKernel primary body order channels pattern input).val ≤ _ at henergy
  have hbounds : 0 ≤ ∏ group, bounds group := Finset.prod_nonneg (fun group _ => div_nonneg (hcost group) (hw group).le)
  have hsqrt := Real.sqrt_le_sqrt henergy
  rw [Finset.prod_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbounds] at hsqrt
  apply (mul_le_mul_of_nonneg_left hsqrt
    (gradeWeight_nonneg pf bf hpf.le hbf.le _ _)).trans_eq
  have hweight : gradeWeight pf bf (totalPrimary order pattern) (totalBody order pattern) = ∏ group, weight group := by
    simp only [weight, gradeWeight, totalPrimary, totalBody, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hweight, ← mul_assoc]
  have hcancel : (∏ group, weight group) * (∏ group, bounds group) = ∏ group, cost group := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro group _
    dsimp only [bounds]
    field_simp [(hw group).ne']
  rw [hcancel]

theorem patternFamily_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    familyNorm primary body order pf bf (patternFamily primary body order channels pattern input) ≤
      (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) := by
  unfold patternFamily
  split_ifs
  · rw [embed, familyNorm_single]
    exact patternKernel_norm primary body order pf bf hpf hbf reference channels cost hcost hchannels pattern input
  · rw [familyNorm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun group _ => hcost group)) (Real.sqrt_nonneg _)

/-- Only the finite output-degree patterns are summed by the triangle
inequality. The color, root, and control source spaces are tensorized as
one joint Hilbert input, so their cardinalities do not enter this bound. -/
theorem response_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (input : ((group : Group) → Input group) → ℝ) :
    familyNorm primary body order pf bf (response primary body order channels input) ≤
      (Fintype.card (TruncatedArity order) : ℝ) ^ Fintype.card Group *
        ((∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input)) := by
  unfold response
  apply (familyNorm_sum_le primary body order pf bf hpf.le hbf.le Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Group → TruncatedArity order,
        (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) :=
      Finset.sum_le_sum (fun pattern _ => patternFamily_norm primary body order pf bf hpf hbf
        reference channels cost hcost hchannels pattern input)
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_pow]

end
end CurrentAFT.GroupedFamilyTensor

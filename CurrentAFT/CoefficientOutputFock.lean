import CurrentAFT.UniformTaggedOutput
import CurrentAFT.PhysicalFockHilbert

/-!
# Whole finite coefficient families satisfy the actual full physical Fock bound

The scalar baseline and every original canonical joint coefficient use
their actual independent uniform selections. The same closed cycle and
queue are retained throughout. The Hilbert triangle bound combines all
arities without a palette-size factor.
-/

namespace CurrentAFT.CoefficientOutputFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound
  TaggedOutputFock UniformTaggedOutput ControlCoordinates ControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool

theorem primary_room (security order : ℕ) (hsecurity : 2 * order ≤ security) (arity : PositiveArity order) :
    arity.val.1.val ≤ Parameters.legCount security := by
  have h := FiniteAtomMoments.current_pool_room security order hsecurity arity.val.1.val arity.val.2.val arity.property.2
  omega

theorem body_room (security order : ℕ) (hsecurity : 2 * order ≤ security) (arity : PositiveArity order) :
    arity.val.2.val ≤ BackgroundRates.ordinaryPool security := by
  have h := FiniteAtomMoments.current_pool_room security order hsecurity arity.val.1.val arity.val.2.val arity.property.2
  omega

def baselineMass (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.renamedMass (Fintype.equivFinOfCardEq (physical_card security))
    (outputLaw security layout queue permutation).weight

def familyMass (security order : ℕ) (hsecurity : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  coefficient.1 * baselineMass security layout queue permutation word +
    ∑ arity : PositiveArity order, uMass security arity.val.1.val arity.val.2.val
      (primary_room security order hsecurity arity) (body_room security order hsecurity arity)
      layout queue permutation (coefficient.2 arity).val word

def normConstant (order : ℕ) (multiple : ℝ) : ℝ :=
  Real.sqrt (32 * Real.exp 2) + ∑ arity : PositiveArity order,
    Real.sqrt (outputConstant arity.val.1.val arity.val.2.val multiple)

theorem normConstant_nonneg (order : ℕ) (multiple : ℝ) : 0 ≤ normConstant order multiple := by
  unfold normConstant
  positivity

theorem scalar_constant_le (order : ℕ) (multiple : ℝ) :
    Real.sqrt (32 * Real.exp 2) ≤ normConstant order multiple := by
  unfold normConstant
  have h : 0 ≤ ∑ arity : PositiveArity order,
      Real.sqrt (outputConstant arity.val.1.val arity.val.2.val multiple) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  linarith

theorem arity_constant_le (order : ℕ) (multiple : ℝ) (arity : PositiveArity order) :
    Real.sqrt (outputConstant arity.val.1.val arity.val.2.val multiple) ≤ normConstant order multiple := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (PositiveArity order)))
    (f := fun arity => Real.sqrt (outputConstant arity.val.1.val arity.val.2.val multiple))
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ arity)
  exact h.trans (by unfold normConstant; linarith [Real.sqrt_nonneg (32 * Real.exp 2)])

theorem inputSize_nonneg (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    0 ≤ inputSize security r s kernel := by
  unfold inputSize
  apply mul_nonneg
  · apply gradeWeight_nonneg
    · unfold BackgroundRates.primaryFactor
      positivity
    · unfold BackgroundRates.bodyFactor
      exact mul_nonneg (radius_nonneg security) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · exact blockL2_nonneg _ _ _

theorem outputConstant_nonneg (r s : ℕ) (multiple : ℝ) : 0 ≤ outputConstant r s multiple := by
  unfold outputConstant
  have := JointTaggedPhysicalFock.jointConstant_nonneg r s multiple
  positivity

/-- Every fixed coefficient order has a security-independent full Fock
operator bound. The output is the actual finite signed family of physical
responses, including the scalar baseline and both true selection laws. -/
theorem current_coefficient_fock_eventually (order : ℕ) (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ hroom : 2 * order ≤ security,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
      ∀ coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order,
      energy (uniformReference security) (familyMass security order hroom layout queue permutation coefficient)
        (multiple * BackgroundRates.radius security) ≤
        (normConstant order multiple * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
          order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) coefficient) ^ 2 := by
  obtain ⟨baselineThreshold, hbaseline⟩ := current_output_fock_eventually multiple hmultiple
  obtain ⟨taggedThreshold, htagged⟩ := current_uniform_tagged_fock_eventually multiple hmultiple
  refine ⟨max baselineThreshold taggedThreshold, ?_⟩
  intro security hsecurity hroom layout queue permutation coefficient
  let masses : Option (PositiveArity order) → (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ
    | none => baselineMass security layout queue permutation
    | some arity => uMass security arity.val.1.val arity.val.2.val
        (primary_room security order hroom arity) (body_room security order hroom arity)
        layout queue permutation (coefficient.2 arity).val
  let scalars : Option (PositiveArity order) → ℝ
    | none => coefficient.1
    | some _ => 1
  let bounds : Option (PositiveArity order) → ℝ
    | none => normConstant order multiple
    | some arity => normConstant order multiple * inputSize security arity.val.1.val arity.val.2.val (coefficient.2 arity).val
  have hb (index : Option (PositiveArity order)) : 0 ≤ bounds index := by
    cases index with
    | none => exact normConstant_nonneg order multiple
    | some arity => exact mul_nonneg (normConstant_nonneg order multiple) (inputSize_nonneg security _ _ _)
  have he (index : Option (PositiveArity order)) :
      energy (uniformReference security) (masses index) (multiple * BackgroundRates.radius security) ≤ bounds index ^ 2 := by
    cases index with
    | none =>
      change energy (uniformReference security) (baselineMass security layout queue permutation)
        (multiple * BackgroundRates.radius security) ≤ normConstant order multiple ^ 2
      unfold baselineMass
      rw [energy_renamed]
      apply (hbaseline security ((Nat.le_max_left _ _).trans hsecurity) layout queue permutation).trans
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (scalar_constant_le order multiple) 2
      rw [Real.sq_sqrt (by positivity : 0 ≤ 32 * Real.exp 2)] at h
      exact h
    | some arity =>
      have h := htagged security ((Nat.le_max_right _ _).trans hsecurity) arity.val.1.val arity.val.2.val
        (primary_room security order hroom arity) (body_room security order hroom arity)
        layout queue permutation (coefficient.2 arity)
      have hn := mul_le_mul_of_nonneg_right (arity_constant_le order multiple arity)
        (inputSize_nonneg security _ _ (coefficient.2 arity).val)
      have hs := pow_le_pow_left₀
        (mul_nonneg (Real.sqrt_nonneg _) (inputSize_nonneg security _ _ (coefficient.2 arity).val)) hn 2
      rw [mul_pow, Real.sq_sqrt (outputConstant_nonneg _ _ multiple)] at hs
      exact h.trans hs
  have h := PhysicalFockHilbert.energy_signed_sum_le (uniformReference security)
    (multiple * BackgroundRates.radius security) scalars bounds masses hb he
  have hmass : (fun word => ∑ index, scalars index * masses index word) =
      familyMass security order hroom layout queue permutation coefficient := by
    funext word
    simp only [Fintype.sum_option, scalars, masses, one_mul, familyMass]
  rw [hmass] at h
  apply h.trans_eq
  congr 1
  simp only [Fintype.sum_option, scalars, bounds, abs_one, one_mul]
  unfold coefficientNorm inputSize
  rw [mul_add, Finset.mul_sum]
  ring

end

end CurrentAFT.CoefficientOutputFock

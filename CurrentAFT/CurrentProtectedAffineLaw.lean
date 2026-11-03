import CurrentAFT.ActualAffineCompletedOutput
import CurrentAFT.FiniteProductFubini
import CurrentAFT.CurrentAffineProtectedCarry
import CurrentAFT.CurrentProtectedSourceParts
import CurrentAFT.CurrentAffinePhysicalEndpoint

/-!
# The protected source law of the actual public affine sample

The local calculation keeps the complete public chart draw outside both
hidden source coordinates, and keeps the entire cycle latent and shared
queue fixed until the final mixture.
-/

namespace CurrentAFT.CurrentProtectedAffineLaw

open AFT AffineFlagCalibration ActualAffineCompletedOutput ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock ActualBlockMean
  ProposalPrimary DiffuseProfiles PublicAuxiliaryFubini FiniteProductFubini PublicCoefficientOutput
open HistogramNormalization PhysicalSynthesis
open CurrentSourceProtection CurrentProtectedSourceParts GaussianProductProtection
open scoped BigOperators Classical

noncomputable section

local instance protectedLawFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance protectedLawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev ChartWord (security : ℕ) :=
  Fin (Parameters.legCount security) → Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))
abbrev ScalarWord (security : ℕ) := Fin (Parameters.legCount security) → AffineFlagCalibration.Scalar security

def chartProduct (security : ℕ) (core : Core security) : FiniteDist (ChartWord security) :=
  FiniteDist.independent (fun leg => completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)

def scalarProduct (security : ℕ) : FiniteDist (ScalarWord security) :=
  FiniteDist.independent (fun _ => scalarLaw security)

def rawBlockWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) (charts : ChartWord security)
    (first second : ScalarWord security) : Sigma (Slots security) → RefinedPublicOutput.Palette security
  | ⟨.inl leg, slot⟩ => evaluateTriple security
      (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg) (charts leg) (first leg) (second leg) slot
  | ⟨.inr (.inl center), _⟩ => shiftEquiv security
      (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | ⟨.inr (.inr point), _⟩ => shiftEquiv security
      (queueRoots security layout core.bodyPermutation latent point + queue.val) (core.queueBaselines point)

def conditionalChartOutput (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → RefinedPublicOutput.Palette security) :=
  (chartProduct security core).mix (fun charts => (scalarProduct security).mix (fun first =>
    (scalarProduct security).map (rawBlockWord security layout core queue latent charts first)))

def delta {State : Type*} (first second : State) : ℝ := if first = second then 1 else 0

theorem delta_block {Index Color : Type*} [Fintype Index]
    (slots : Index → Type*) (first second : Sigma slots → Color) :
    delta first second = ∏ index, delta (fun slot => first ⟨index, slot⟩) (fun slot => second ⟨index, slot⟩) := by
  exact block_delta slots first second

theorem map_delta {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (value : Input → Output) (target : Output) :
    (law.map value).weight target = law.expectation (fun input => delta (value input) target) := by
  simp only [FiniteDist.map_weight, FiniteDist.expectation, delta, mul_ite, mul_one, mul_zero]

theorem singleton_weight (security : ℕ) (root : ℤ) (center : RefinedPublicOutput.Palette security)
    (word : Fin 1 → RefinedPublicOutput.Palette security) :
    (RefinedPublicOutput.singleton security root center).weight word =
      delta (fun _ : Fin 1 => shiftEquiv security root center) word := by
  rw [RefinedPublicOutput.singleton, FixedPairedFirst.pointLaw, FiniteDist.map_map]
  simp only [FiniteDist.map_weight, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, delta]
  split_ifs <;> rfl

theorem completedTriple_weight (security : ℕ) (root : ℤ) (primary : AffineFlagCalibration.Palette security)
    (seed : LegCore security) (word : Fin 3 → RefinedPublicOutput.Palette security) :
    (completedTriple security root primary seed).weight word =
      (completionLaw security primary seed.1).expectation (fun chart =>
        (scalarLaw security).expectation (fun first => (scalarLaw security).expectation (fun second =>
          delta (evaluateTriple security root primary seed chart first second) word))) := by
  simp only [completedTriple, FiniteDist.mix_weight, map_delta, FiniteDist.expectation]

theorem conditionalChartOutput_eq (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) :
    conditionalChartOutput security layout core queue latent =
      ActualAffineCompletedOutput.conditionalLaw security layout core queue.val latent := by
  ext word
  simp only [conditionalChartOutput, FiniteDist.mix_weight, map_delta]
  change (chartProduct security core).expectation (fun charts => (scalarProduct security).expectation
    (fun first => (scalarProduct security).expectation (fun second =>
      delta (rawBlockWord security layout core queue latent charts first second) word))) = _
  simp_rw [delta_block (Slots security)]
  simp only [Fintype.prod_sum_type, rawBlockWord]
  simp_rw [FiniteDist.expectation_mul_const]
  have hprod := three_products
    (fun leg : Fin (Parameters.legCount security) =>
      completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)
    (fun _ : Fin (Parameters.legCount security) => scalarLaw security)
    (fun _ : Fin (Parameters.legCount security) => scalarLaw security)
    (fun leg chart first second =>
      delta (evaluateTriple security (attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (core.legs leg) chart first second)
          (fun slot => word ⟨.inl leg, slot⟩))
  unfold ActualAffineCompletedOutput.conditionalLaw
  simp only [FiniteDist.retype_weight, BlockProducts.blockLaw, BlockProducts.blockMass,
    Fintype.prod_sum_type, ActualAffineCompletedOutput.blocks]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · simp only [completedTriple_weight]
    exact hprod
  · simp only [singleton_weight]
    rfl

def completedPartsLaw (security : ℕ) : FiniteDist (Parts security) :=
  (FiniteDist.retype (ActualFockBound.latentLaw security)).prod
    ((scalarProduct security).prod ((scalarProduct security).prod (scalarLaw security)))

theorem protected_parts (security : ℕ) :
    (FiniteDist.retype (protectedSourceLaw security)).map (splitParts security) = completedPartsLaw security := by
  ext parts
  rw [FiniteDist.map_equiv_weight, FiniteDist.retype_weight, protected_weight_parts,
    Equiv.apply_symm_apply]
  rfl

def rawOutputWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : ChartWord security) (parts : Parts security) :
    Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security :=
  AFT.relabel (renameWord (flatten security)
    (rawBlockWord security layout core parts.2.2.2 parts.1 charts parts.2.1 parts.2.2.1)) core.endpointPermutation

theorem rawOutput_split (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : ChartWord security) (word : ProtectedWord (cutoff security)) :
    rawOutputWord security layout core charts (splitParts security word) =
      CurrentAffinePhysicalEndpoint.outputWord security layout core charts word := rfl

def protectedChartPalette (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :=
  (chartProduct security core).mix (fun charts => (FiniteDist.retype (protectedSourceLaw security)).map
    (CurrentAffinePhysicalEndpoint.outputWord security layout core charts))

theorem protected_chart_sources (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : ChartWord security) :
    (FiniteDist.retype (protectedSourceLaw security)).map
      (CurrentAffinePhysicalEndpoint.outputWord security layout core charts) =
        (completedPartsLaw security).map (rawOutputWord security layout core charts) := by
  rw [← protected_parts, FiniteDist.map_map]
  rfl

theorem prod_mix {A B O : Type*} [Fintype A] [Fintype B] [Fintype O]
    (first : FiniteDist A) (second : FiniteDist B) (kernel : A × B → FiniteDist O) :
    (first.prod second).mix kernel = first.mix (fun a => second.mix (fun b => kernel (a, b))) := by
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

theorem map_prod {A B O : Type*} [Fintype A] [Fintype B] [Fintype O]
    (first : FiniteDist A) (second : FiniteDist B) (value : A × B → O) :
    (first.prod second).map value = first.mix (fun a => second.map (fun b => value (a, b))) := by
  ext output
  simp only [FiniteDist.map_weight, FiniteDist.mix_weight, FiniteDist.prod_weight,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

theorem conditional_renamed (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : AffineFlagCalibration.Scalar security)
    (latent : BodyIndex security → Edge security) :
    (chartProduct security core).mix (fun charts => (scalarProduct security).mix (fun first =>
      (scalarProduct security).map (fun second => rawOutputWord security layout core charts
        (latent, (first, (second, queue)))))) =
      (conditionalChartOutput security layout core queue latent).map
        (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation) := by
  unfold conditionalChartOutput
  simp only [FiniteDist.map_mix, FiniteDist.map_map]
  rfl

theorem protectedChartPalette_eq (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    protectedChartPalette security layout core = ActualAffineCompletedOutput.lawGiven security layout core := by
  unfold protectedChartPalette
  simp_rw [protected_chart_sources]
  rw [mix_map_comm]
  unfold completedPartsLaw
  rw [prod_mix]
  simp_rw [prod_mix]
  simp_rw [FiniteDist.mix_comm (scalarProduct security) (scalarLaw security)]
  rw [FiniteDist.mix_comm]
  simp_rw [mix_map_comm (scalarProduct security) (chartProduct security core)]
  simp_rw [FiniteDist.mix_comm (scalarProduct security) (chartProduct security core)]
  simp_rw [conditional_renamed, conditionalChartOutput_eq]
  rfl

def protectedChartMapped (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Residue security) :=
  (protectedChartPalette security layout core).map
    (fun word index => RefinedPublicOutput.embed security (word index))

theorem protectedChartMapped_eq (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) :
    protectedChartMapped security layout core = ActualAffineCompletedOutput.mappedChannel security layout core := by
  rw [protectedChartMapped, protectedChartPalette_eq]
  rfl

end
end CurrentAFT.CurrentProtectedAffineLaw

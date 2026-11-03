import CurrentAFT.ComplementMeanMGF

/-!
# Complete signed physical output for an actual selected joint coefficient

The selected paired four-output channels and singleton body channels are
multiplied by every unselected physical block, then averaged over the same
closed protected cycle. All output degrees, including full support, remain.
-/

namespace CurrentAFT.TaggedOutputFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound TaggedSelection
  JointTaggedPhysicalFock ComplementMeanMGF ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

abbrev OutputIndex {security r s : ℕ} (selection : Selection security r s) :=
  Sigma (physicalSlots r s) ⊕ Sigma (fun index : selection.kept => Slots security index.val)

def taggedMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (Sigma (physicalSlots r s) → ActualBlockMean.Palette security) → ℝ :=
  jointMass security r s
    (fun index => centerRoots security layout permutation latent (selection.compensator index))
    (fun index => attachmentRoots security layout permutation latent (selection.primary index))
    (fun index => centerRoots security layout permutation latent (selection.body index)) kernel

def conditionalMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (OutputIndex selection → ActualBlockMean.Palette security) → ℝ :=
  BlockProducts.taggedBlockMass (fun index : selection.kept => Slots security index.val)
    (taggedMass security r s selection layout permutation latent kernel)
    (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)

def outputMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : OutputIndex selection → ActualBlockMean.Palette security) : ℝ :=
  (latentLaw security).expectation (fun latent =>
    conditionalMass security r s selection layout queue permutation latent kernel word)

def inputSize (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) : ℝ :=
  ControlNorm.gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    ControlNorm.blockL2 (primaryLaw security) (ActualControls.bodyReference security) kernel

theorem conditional_energy_le (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (multiple : ℝ) (hmultiple : 0 ≤ multiple) (hscale : normalizedScale security multiple ≤ 1)
    (hlocal : BlockProducts.CubicBlockConditions
      (fun index : selection.kept => Slots security index.val) (uniformReference security)
      (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)
      (Parameters.dimension security) (Parameters.dimension security) (multiple * BackgroundRates.radius security)) :
    energy (uniformReference security)
      (conditionalMass security r s selection layout queue permutation latent kernel.val)
      (multiple * BackgroundRates.radius security) ≤
      (jointConstant r s multiple * inputSize security r s kernel.val ^ 2) *
        (16 * Real.exp (8 * keptEnergy security r s layout queue permutation multiple selection latent)) := by
  have hcard := selection.full_output_card
  have h := BlockProducts.tagged_block_fock_energy_le
    (fun index : selection.kept => Slots security index.val) (uniformReference security)
    (taggedMass security r s selection layout permutation latent kernel.val)
    (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)
    (fun index => slots_card_le_three security index.val) (Parameters.dimension security)
    (multiple * BackgroundRates.radius security)
    (by simpa only [hcard] using hlocal.1)
    (by simpa only [hcard] using hlocal.2.1)
    (by simpa only [hcard] using hlocal.2.2)
  change energy (uniformReference security)
    (conditionalMass security r s selection layout queue permutation latent kernel.val)
    (multiple * BackgroundRates.radius security) ≤ _ at h
  rw [hcard] at h
  simp_rw [kept_linear_sum] at h
  have htag := jointMass_graded_energy_le security r s
    (fun index => centerRoots security layout permutation latent (selection.compensator index))
    (fun index => attachmentRoots security layout permutation latent (selection.primary index))
    (fun index => centerRoots security layout permutation latent (selection.body index))
    kernel multiple hmultiple hscale
  change energy (uniformReference security)
      (conditionalMass security r s selection layout queue permutation latent kernel.val)
      (multiple * BackgroundRates.radius security) ≤
      BlockProducts.taggedCoefficientEnergy (uniformReference security)
        (taggedMass security r s selection layout permutation latent kernel.val) (Parameters.dimension security)
          (multiple * BackgroundRates.radius security) *
        (16 * Real.exp (8 * keptEnergy security r s layout queue permutation multiple selection latent)) at h
  exact h.trans (mul_le_mul_of_nonneg_right htag (by positivity))

def outputConstant (r s : ℕ) (multiple : ℝ) : ℝ :=
  32 * Real.exp (2 * ((2 * r + s : ℕ) : ℝ) + 2) * jointConstant r s multiple

/-- Actual whole-root averaged conditional energy for every nonseparable
canonical coefficient. Every premise controlling a physical norm has been
discharged by the current local laws, parameters, and cycle MGF. -/
theorem current_average_tagged_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ r s : ℕ,
      ∀ selection : Selection security r s,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
      ∀ kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s,
      (latentLaw security).expectation (fun latent => energy (uniformReference security)
        (conditionalMass security r s selection layout queue permutation latent kernel.val)
        (multiple * BackgroundRates.radius security)) ≤
        outputConstant r s multiple * inputSize security r s kernel.val ^ 2 := by
  obtain ⟨localThreshold, hlocal⟩ := current_subproduct_conditions_eventually multiple hmultiple
  obtain ⟨scaleThreshold, hscale⟩ := normalizedScale_le_one_eventually multiple hmultiple
  obtain ⟨meanThreshold, hmean⟩ := current_complement_mean_mgf_eventually multiple hmultiple
  refine ⟨max localThreshold (max scaleThreshold meanThreshold), ?_⟩
  intro security hsecurity r s selection layout queue permutation kernel
  have hs := hscale security ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hsecurity))
  have hm := hmean security ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hsecurity))
    r s selection layout queue permutation
  have hc0 : 0 ≤ jointConstant r s multiple * inputSize security r s kernel.val ^ 2 :=
    mul_nonneg (jointConstant_nonneg r s multiple) (sq_nonneg _)
  calc
    _ ≤ (latentLaw security).expectation (fun latent =>
        (jointConstant r s multiple * inputSize security r s kernel.val ^ 2) *
          (16 * Real.exp (8 * keptEnergy security r s layout queue permutation multiple selection latent))) :=
      Finset.sum_le_sum (fun latent _ => mul_le_mul_of_nonneg_left
        (conditional_energy_le security r s selection layout queue permutation latent kernel multiple hmultiple hs
          (hlocal security ((Nat.le_max_left _ _).trans hsecurity)
            (attachmentRoots security layout permutation latent) (centerRoots security layout permutation latent)
            (queueRoots security layout permutation latent) queue selection.kept)) ((latentLaw security).nonneg latent))
    _ = (16 * (jointConstant r s multiple * inputSize security r s kernel.val ^ 2)) *
        (latentLaw security).expectation (fun latent => Real.exp
          (8 * keptEnergy security r s layout queue permutation multiple selection latent)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro latent _
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hc0)).trans_eq (by unfold outputConstant; ring)

/-- Full finite physical Fock bound of the actual signed averaged output
mass, including all remaining background degrees and all tagged degrees. -/
theorem current_tagged_output_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ r s : ℕ,
      ∀ selection : Selection security r s,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
      ∀ kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s,
      energy (uniformReference security) (outputMass security r s selection layout queue permutation kernel.val)
        (multiple * BackgroundRates.radius security) ≤
        outputConstant r s multiple * inputSize security r s kernel.val ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := current_average_tagged_fock_eventually multiple hmultiple
  refine ⟨threshold, ?_⟩
  intro security hsecurity r s selection layout queue permutation kernel
  exact (energy_average_le (latentLaw security) (uniformReference security)
    (fun latent => conditionalMass security r s selection layout queue permutation latent kernel.val)
    (multiple * BackgroundRates.radius security) (mul_nonneg hmultiple (radius_nonneg security))).trans
    (hthreshold security hsecurity r s selection layout queue permutation kernel)

end

end CurrentAFT.TaggedOutputFock

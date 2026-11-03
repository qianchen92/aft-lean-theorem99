import CurrentAFT.ActualBlockMean
import CurrentAFT.OmittedBlockMean
import AFT.FiniteRetype
import AFT.ReindexedCoefficients

/-!
# Complete actual physical Fock energy after averaging the closed cycle

All finite output degrees are retained. The local block conditions and the
whole-mean exponential moment are proved for the current distributions.
-/

namespace CurrentAFT.ActualFockBound

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean ConditionalHistogramMGF PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

/-- The full population-normalized real physical coefficient energy. -/
def energy {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card Slot) radius (fun degree =>
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree))

theorem energy_symmetrized {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) (radius : ℝ) :
    energy reference (HistogramNormalization.symmetrizedMass mass) radius = energy reference mass radius := by
  unfold energy HistogramTail.fockEnergy
  apply Finset.sum_congr rfl
  intro degree hdegree
  dsimp only
  rw [HistogramNormalization.degreeTensor_symmetrizedMass reference mass degree
    (Nat.le_of_lt_succ (Finset.mem_range.mp hdegree))]

theorem energy_renamed {Slot OtherSlot Color : Type*} [Fintype Slot] [Fintype OtherSlot] [Fintype Color]
    (equiv : Slot ≃ OtherSlot) (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) (radius : ℝ) :
    energy reference (HistogramNormalization.renamedMass equiv mass) radius = energy reference mass radius := by
  unfold energy HistogramTail.fockEnergy
  have hc := (Fintype.card_congr equiv).symm
  simp only [hc]
  apply Finset.sum_congr rfl
  intro degree hdegree
  dsimp only
  rw [HistogramNormalization.degreeTensor_renamedMass equiv reference mass degree
    (Nat.le_of_lt_succ (Finset.mem_range.mp hdegree))]

private theorem degree_average_energy {Sample Slot Color : Type*} [Fintype Sample]
    [Fintype Slot] [Fintype Color] (source : FiniteDist Sample) (reference : FiniteDist Color)
    (mass : Sample → (Slot → Color) → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference)
      (fun word => source.expectation (fun sample => mass sample word)) degree) ≤
      source.expectation (fun sample => BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Slot => reference) (mass sample) degree)) := by
  have hmass : (fun word => source.expectation (fun sample => mass sample word)) =
      ∑ sample, source.weight sample • mass sample := by
    funext word
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
  simp only [map_smul, LocalTensors.degreeTensorLinear_apply, BlockFock.tensorEnergy,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ word, ∑ sample, source.weight sample *
        LocalTensors.degreeTensor (fun _ : Slot => reference) (mass sample) degree word ^ 2 :=
      Finset.sum_le_sum (fun word _ => BlockFock.mean_square_le source _)
    _ = _ := by unfold FiniteDist.expectation; rw [Finset.sum_comm]; simp only [Finset.mul_sum]

/-- Averaging arbitrary signed physical masses contracts the entire finite
Fock energy, not merely one coordinate or one fixed homogeneous degree. -/
theorem energy_average_le {Sample Slot Color : Type*} [Fintype Sample] [Fintype Slot] [Fintype Color]
    (source : FiniteDist Sample) (reference : FiniteDist Color)
    (mass : Sample → (Slot → Color) → ℝ) (radius : ℝ) (hradius : 0 ≤ radius) :
    energy reference (fun word => source.expectation (fun sample => mass sample word)) radius ≤
      source.expectation (fun sample => energy reference (mass sample) radius) := by
  let factor := fun degree : ℕ => (degree.factorial : ℝ) * radius ^ (2 * degree) / (Fintype.card Slot : ℝ) ^ degree
  have hfactor (degree : ℕ) : 0 ≤ factor degree := by dsimp [factor]; positivity
  calc
    _ = ∑ degree ∈ Finset.range (Fintype.card Slot + 1), factor degree *
        BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference)
          (fun word => source.expectation (fun sample => mass sample word)) degree) := by
      unfold energy HistogramTail.fockEnergy
      apply Finset.sum_congr rfl
      intro degree _
      dsimp [factor]
      ring
    _ ≤ ∑ degree ∈ Finset.range (Fintype.card Slot + 1), factor degree *
        source.expectation (fun sample => BlockFock.tensorEnergy
          (LocalTensors.degreeTensor (fun _ : Slot => reference) (mass sample) degree)) :=
      Finset.sum_le_sum (fun degree _ => mul_le_mul_of_nonneg_left
        (degree_average_energy source reference mass degree) (hfactor degree))
    _ = _ := by
      unfold energy HistogramTail.fockEnergy FiniteDist.expectation
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sample _
      apply Finset.sum_congr rfl
      intro degree _
      dsimp [factor]
      ring

def latentLaw (security : ℕ) : FiniteDist (BodyIndex security → Edge security) :=
  FiniteDist.independent (fun _ : BodyIndex security => edgeLaw security)

/-- The actual positive output law with the whole dependent cycle averaged
outside the genuine independent local blocks. -/
def outputLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) : FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  (latentLaw security).mix (fun latent => FiniteDist.retype (BlockProducts.blockLaw (Slots security)
    (rootedLaw security layout queue permutation latent)))

theorem mean_exponential_identity_parameter (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (multiple constant : ℝ) :
    (latentLaw security).expectation (fun latent => Real.exp (constant * ∑ color,
      (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
        (rootedLaw security layout queue permutation latent) (normalizedScale security multiple) index color) ^ 2)) =
      moment security layout queue permutation ((constant * multiple ^ 2) * BackgroundRates.radius security ^ 2) := by
  rw [moment_eq_expectation]
  apply Finset.sum_congr rfl
  intro latent _
  dsimp only
  rw [normalized_first_energy]
  congr 2
  ring

theorem mean_exponential_identity (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ) :
    (latentLaw security).expectation (fun latent => Real.exp (8 * ∑ color,
      (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
        (rootedLaw security layout queue permutation latent) (normalizedScale security multiple) index color) ^ 2)) =
      moment security layout queue permutation ((8 * multiple ^ 2) * BackgroundRates.radius security ^ 2) :=
  mean_exponential_identity_parameter security layout queue permutation multiple 8

/-- Complete conditional Fock energies are averaged under the actual
closed Gaussian cycle. The bound has no final norm or tail premise. -/
theorem current_average_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
        (latentLaw security).expectation (fun latent =>
          productFockEnergy (Slots security) (uniformReference security)
            (rootedLaw security layout queue permutation latent) (multiple * BackgroundRates.radius security)) ≤
          32 * Real.exp 2 := by
  obtain ⟨blockThreshold, hblocks⟩ := current_product_fock_eventually multiple hmultiple
  obtain ⟨meanThreshold, hmean⟩ := current_whole_mean_mgf_eventually (8 * multiple ^ 2) (by positivity)
  refine ⟨max blockThreshold meanThreshold, ?_⟩
  intro security hsecurity layout queue permutation
  have hm := hmean security ((Nat.le_max_right _ _).trans hsecurity) layout queue permutation
  calc
    _ ≤ (latentLaw security).expectation (fun latent => 16 * Real.exp (8 * ∑ color,
        (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
          (rootedLaw security layout queue permutation latent) (normalizedScale security multiple) index color) ^ 2)) :=
      Finset.sum_le_sum (fun latent _ => mul_le_mul_of_nonneg_left
        (hblocks security ((Nat.le_max_left _ _).trans hsecurity)
          (attachmentRoots security layout permutation latent) (centerRoots security layout permutation latent)
          (queueRoots security layout permutation latent) queue) ((latentLaw security).nonneg latent))
    _ = 16 * moment security layout queue permutation ((8 * multiple ^ 2) * BackgroundRates.radius security ^ 2) := by
      rw [FiniteDist.expectation_const_mul, mean_exponential_identity]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

theorem current_output_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
        energy (uniformReference security) (outputLaw security layout queue permutation).weight
          (multiple * BackgroundRates.radius security) ≤ 32 * Real.exp 2 := by
  obtain ⟨threshold, hthreshold⟩ := current_average_fock_eventually multiple hmultiple
  refine ⟨threshold, ?_⟩
  intro security hsecurity layout queue permutation
  have hmass : (outputLaw security layout queue permutation).weight =
      fun word => (latentLaw security).expectation (fun latent =>
        BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) word) := rfl
  rw [hmass]
  exact (energy_average_le (latentLaw security) (uniformReference security)
    (fun latent => BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent))
    (multiple * BackgroundRates.radius security) (mul_nonneg hmultiple (radius_nonneg security))).trans
      (hthreshold security hsecurity layout queue permutation)

end

end CurrentAFT.ActualFockBound

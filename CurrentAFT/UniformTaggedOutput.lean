import CurrentAFT.TaggedOutputFock
import CurrentAFT.MomentParameters

/-! # Actual independent uniform distinct-index averages of complete physical outputs -/

namespace CurrentAFT.UniformTaggedOutput

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound TaggedSelection
  JointTaggedPhysicalFock TaggedOutputFock ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool

theorem centerCount_split (security : ℕ) :
    Parameters.legCount security + BackgroundRates.ordinaryPool security = centerCount security := by
  have := population_room security
  unfold centerCount BackgroundRates.ordinaryPool
  omega

/-- A fixed public division of center positions into compensators and
ordinary controls. Arbitrary body layouts subsequently place this division. -/
def centerSplit (security : ℕ) :
    (Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)) ≃ Fin (centerCount security) :=
  finSumFinEquiv.trans (finCongr (centerCount_split security))

def compensatorPosition (security : ℕ) : Fin (Parameters.legCount security) ↪ Fin (centerCount security) where
  toFun index := centerSplit security (.inl index)
  inj' _first _second hequal := Sum.inl.inj ((centerSplit security).injective hequal)

def ordinaryPosition (security : ℕ) : Fin (BackgroundRates.ordinaryPool security) ↪ Fin (centerCount security) where
  toFun index := centerSplit security (.inr index)
  inj' _first _second hequal := Sum.inr.inj ((centerSplit security).injective hequal)

abbrev Choice (security r s : ℕ) :=
  (Fin r ↪ Fin (Parameters.legCount security)) × (Fin s ↪ Fin (BackgroundRates.ordinaryPool security))

def selection (security r s : ℕ) (choice : Choice security r s) : Selection security r s where
  primary := choice.1
  compensator := choice.1.trans (compensatorPosition security)
  body := choice.2.trans (ordinaryPosition security)
  separated first second hequal := by
    have h := (centerSplit security).injective hequal
    cases h

def choiceLaw (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security) : FiniteDist (Choice security r s) := by
  letI : Nonempty (Fin r ↪ Fin (Parameters.legCount security)) := ⟨Fin.castLEEmb hprimary⟩
  letI : Nonempty (Fin s ↪ Fin (BackgroundRates.ordinaryPool security)) := ⟨Fin.castLEEmb hbody⟩
  exact (FiniteDist.uniform (Fin r ↪ Fin (Parameters.legCount security))).prod
    (FiniteDist.uniform (Fin s ↪ Fin (BackgroundRates.ordinaryPool security)))

/-- The exact two independent without-replacement normalizers. -/
theorem choiceLaw_weight (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security) (choice : Choice security r s) :
    (choiceLaw security r s hprimary hbody).weight choice =
      1 / (((Parameters.legCount security).descFactorial r : ℝ) *
        ((BackgroundRates.ordinaryPool security).descFactorial s : ℝ)) := by
  simp only [choiceLaw, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.card_embedding_eq, Fintype.card_fin]
  ring

def outputEquiv {security r s : ℕ} (chosen : Selection security r s) :
    OutputIndex chosen ≃ Fin (Parameters.dimension security) :=
  Fintype.equivFinOfCardEq chosen.full_output_card

def flatMass (security r s : ℕ) (chosen : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.renamedMass (outputEquiv chosen)
    (outputMass security r s chosen layout queue permutation kernel)

/-- The actual independent uniform distinct-index physical output, with
one fixed compensator placement and one common queue scalar. -/
def uMass (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (choiceLaw security r s hprimary hbody).expectation (fun choice =>
    flatMass security r s (selection security r s choice) layout queue permutation kernel word)

theorem current_uniform_tagged_fock_eventually (multiple : ℝ) (hmultiple : 0 ≤ multiple) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ r s : ℕ,
      ∀ hprimary : r ≤ Parameters.legCount security, ∀ hbody : s ≤ BackgroundRates.ordinaryPool security,
      ∀ layout : RoleIndex security ≃ BodyIndex security, ∀ queue : ℤ,
      ∀ permutation : Equiv.Perm (BodyIndex security),
      ∀ kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s,
      energy (uniformReference security) (uMass security r s hprimary hbody layout queue permutation kernel.val)
        (multiple * BackgroundRates.radius security) ≤
        outputConstant r s multiple * inputSize security r s kernel.val ^ 2 := by
  obtain ⟨threshold, hthreshold⟩ := current_tagged_output_fock_eventually multiple hmultiple
  refine ⟨threshold, ?_⟩
  intro security hsecurity r s hprimary hbody layout queue permutation kernel
  apply (energy_average_le (choiceLaw security r s hprimary hbody) (uniformReference security)
    (fun choice => flatMass security r s (selection security r s choice) layout queue permutation kernel.val)
    (multiple * BackgroundRates.radius security) (mul_nonneg hmultiple (radius_nonneg security))).trans
  calc
    _ ≤ (choiceLaw security r s hprimary hbody).expectation (fun _ =>
        outputConstant r s multiple * inputSize security r s kernel.val ^ 2) := by
      apply Finset.sum_le_sum
      intro choice _
      apply mul_le_mul_of_nonneg_left _ ((choiceLaw security r s hprimary hbody).nonneg choice)
      dsimp only
      unfold flatMass
      rw [energy_renamed]
      exact hthreshold security hsecurity r s (selection security r s choice) layout queue permutation kernel
    _ = _ := FiniteDist.expectation_const _ _

end

end CurrentAFT.UniformTaggedOutput

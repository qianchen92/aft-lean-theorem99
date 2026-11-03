import CurrentAFT.HistogramMean
import CurrentAFT.ActualCycleMeanMGF
import CurrentAFT.RoleProduct

/-! # The complete conditional first histogram is cycle fluctuation plus queue drift -/

namespace CurrentAFT.ConditionalHistogramMean

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
  UniformBodyProfiles BodyRootAverages BackgroundCertificates FringeCertificate
  BackgroundPopulationBounds HistogramMean FiniteConcentration ActualCycleMeanMGF
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev RoleIndex (security : ℕ) := RoleProduct.RoleIndex
  (freeCount security) (Parameters.modulus security) (Parameters.legCount security)

def roleOf (security : ℕ) : RoleIndex security → BodyRole :=
  Sum.elim (fun _ => .free) (Sum.elim (fun _ => .queue) (fun _ => .attachment))

def roles (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    BodyIndex security → BodyRole := fun vertex => roleOf security (layout.symm vertex)

def offBodyVector (security : ℕ) : ProfileSpace security :=
  ProfileHilbert.whiten (uniformReference security).weight
    (fun output => offBodyMean security output - 2 * uniformProfile security output)

def conditionalMean (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    ProfileSpace security :=
  NormalizedMeanAlgebra.euclideanSum (NormalizedMeanAlgebra.normalizationScale security)
    (realizedResponse security (roles security layout) queue permutation latent)
    ((Parameters.legCount security : ℝ) • offBodyVector security)

theorem response_mean (security : ℕ) (roleAssignment : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security) :
    vectorMean ((edgeLaw security).prod (edgeLaw security))
      (response security roleAssignment queue permutation vertex) =
      uniformVector security
        (rootAverage security (preRootLaw security (roleAssignment (permutation vertex)) queue)).weight := by
  symm
  exact ProfileHilbert.whiten_mixture_centered (uniformReference security) (publicBlurLaw security)
    (fun pair => (preRootLaw security (roleAssignment (permutation vertex)) queue).map
      (shiftEquiv security (pair.2.val - pair.1.val)))

private def roleVector {Hilbert : Type*} (freeCount queueCount legCount : ℕ)
    (free queue attachment : Hilbert) : RoleProduct.RoleIndex freeCount queueCount legCount → Hilbert :=
  Sum.elim (fun _ => free) (Sum.elim (fun _ => queue) (fun _ => attachment))

private theorem role_vector_sum {Vertex Hilbert : Type*} [Fintype Vertex]
    [AddCommGroup Hilbert] [Module ℝ Hilbert]
    (freeCount queueCount legCount : ℕ)
    (layout : RoleProduct.RoleIndex freeCount queueCount legCount ≃ Vertex)
    (permutation : Equiv.Perm Vertex) (free queue attachment : Hilbert)
    (value : Vertex → Hilbert)
    (hvalue : ∀ vertex, value vertex = roleVector freeCount queueCount legCount
      free queue attachment (layout.symm (permutation vertex))) :
    (∑ vertex, value vertex) = (freeCount : ℝ) • free + (queueCount : ℝ) • queue +
      (legCount : ℝ) • attachment := by
  simp_rw [hvalue]
  rw [Equiv.sum_comp permutation (fun vertex =>
    roleVector freeCount queueCount legCount free queue attachment (layout.symm vertex))]
  rw [← layout.sum_comp (fun vertex =>
    roleVector freeCount queueCount legCount free queue attachment (layout.symm vertex))]
  simp only [Equiv.symm_apply_apply, roleVector, RoleProduct.RoleIndex,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  exact (add_assoc _ _ _).symm

theorem response_mean_sum (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) :
    (∑ vertex, vectorMean ((edgeLaw security).prod (edgeLaw security))
      (response security (roles security layout) queue permutation vertex)) =
      freeMass security • uniformVector security (convolvedCenterLaw security).weight +
        (Parameters.modulus security : ℝ) • uniformVector security (queueLaw security queue).weight +
        (Parameters.legCount security : ℝ) • uniformVector security (bodyLaw security true).weight := by
  rw [← freeCount_cast]
  apply role_vector_sum (freeCount security) (Parameters.modulus security) (Parameters.legCount security)
    layout permutation
  intro vertex
  rw [response_mean]
  simp only [roles]
  generalize layout.symm (permutation vertex) = index
  rcases index with free | queueOrAttachment
  · rw [roleOf, Sum.elim_inl, role_rootAverage]
    rfl
  · rcases queueOrAttachment with queueIndex | attachmentIndex
    · rw [roleOf, Sum.elim_inr, Sum.elim_inl, role_rootAverage]
      rfl
    · rw [roleOf, Sum.elim_inr, Sum.elim_inr, role_rootAverage]
      rfl

theorem total_mean_vector (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) :
    (∑ vertex, vectorMean ((edgeLaw security).prod (edgeLaw security))
      (response security (roles security layout) queue permutation vertex)) +
      (Parameters.legCount security : ℝ) • offBodyVector security =
      ProfileHilbert.whiten (uniformReference security).weight
        (fun output => rootAveragedHistogram security queue output -
          (Parameters.dimension security : ℝ) * uniformProfile security output) := by
  rw [response_mean_sum]
  simp only [uniformVector, offBodyVector]
  rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add]
  congr 1
  funext output
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [uniformReference_weight, one_div, uniformProfile, rootAveragedHistogram, freeMass,
    Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- This is the literal normalized sum of all conditional endpoint means.
The cycle remains dependent, and the queue contributes one common drift. -/
theorem conditionalMean_decomposition_coordinate (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (output : LocalReferenceEnergy.Palette security) :
    (conditionalMean security layout queue permutation latent).ofLp output =
      (fluctuation security (roles security layout) queue permutation latent).ofLp output +
        (drift security queue).ofLp output := by
  have h := NormalizedMeanAlgebra.euclidean_decomposition
    (NormalizedMeanAlgebra.normalizationScale security)
    (realizedResponse security (roles security layout) queue permutation latent)
    (meanResponse security (roles security layout) queue permutation)
    ((Parameters.legCount security : ℝ) • offBodyVector security)
    (ProfileHilbert.whiten (uniformReference security).weight
      (fun output => rootAveragedHistogram security queue output -
        (Parameters.dimension security : ℝ) * uniformProfile security output))
    (total_mean_vector security layout queue permutation)
  simpa only [conditionalMean, fluctuation, drift, WithLp.ofLp_add] using
    congrArg (fun value : ProfileSpace security => value.ofLp output) h

theorem conditionalMean_decomposition (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) :
    conditionalMean security layout queue permutation latent =
      fluctuation security (roles security layout) queue permutation latent + drift security queue := by
  apply WithLp.ofLp_injective
  funext output
  exact conditionalMean_decomposition_coordinate security layout queue permutation latent output

end

end CurrentAFT.ConditionalHistogramMean

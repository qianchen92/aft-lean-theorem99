import CurrentAFT.ActualBlockFock
import CurrentAFT.PhysicalFockRates
import CurrentAFT.ConditionalHistogramMGF

/-! # The actual independent-block first coefficient is the complete cycle mean -/

namespace CurrentAFT.ActualBlockMean

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PositiveFirstCoefficient
  ActualBlockFock ConditionalHistogramMean ActualCycleMeanMGF UniformBodyProfiles
  HistogramMean BodyRootAverages PhysicalBlockTensors
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw scalarLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security

private theorem shared_body_marginal {Source Color : Type*} [Fintype Source] [Fintype Color]
    (source : FiniteDist Source) (pair : Source → FiniteDist (Color × Color))
    (body : FiniteDist Color) (color : Color) :
    ((sharedSourceTriple source pair (fun _ _ _ => body)).map (fun word => word 2)).weight color =
      body.weight color := by
  rw [sharedSourceTriple_body_marginal]
  have hmass (first second : Color) : BlockDensity.attachedMass source pair (fun _ _ _ => body)
      first second color = (source.mix pair).weight (first, second) * body.weight color := by
    simp only [BlockDensity.attachedMass, FiniteDist.mix_weight, Finset.sum_mul, mul_assoc]
  simp_rw [hmass]
  have hsum : (∑ first, ∑ second, (source.mix pair).weight (first, second)) = 1 := by
    simpa only [Fintype.sum_prod_type] using (source.mix pair).sum_one
  calc
    _ = (∑ first, ∑ second, (source.mix pair).weight (first, second)) * body.weight color := by
      simp only [Finset.sum_mul]
    _ = _ := by rw [hsum, one_mul]

theorem triple_histogram (security : ℕ) (root : ℤ) (scalar : FirstHistogram.Scalar security)
    (output : Palette security) :
    (∑ index : Fin 3, ((positiveTripleLaw security root scalar).map (fun word => word index)).weight output) =
      ConditionalPairMean.pairMean security scalar output + (attachmentAt security root scalar).weight output := by
  rw [Fin.sum_univ_three]
  simp only [positiveTripleLaw, sharedSourceTriple_first_marginal, sharedSourceTriple_second_marginal,
    shared_body_marginal]
  congr 1
  rw [ConditionalPairMean.pairMean_actual]
  simp only [FiniteDist.mix_weight]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun first primary =>
    (primaryLaw security).weight primary * (pairAt security primary scalar).weight (first, output))]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

theorem attachment_mixture (security : ℕ) (root : ℤ) :
    (scalarLaw security).mix (attachmentAt security root) =
      (preRootLaw security .attachment 0).map (shiftEquiv security root) := by
  rw [preRootLaw, FiniteDist.map_mix]
  congr 1
  funext scalar
  rw [attachmentAt, shiftLaw_add, add_comm root scalar.val]

theorem primary_histogram (security : ℕ) (root : ℤ) (output : Palette security) :
    (∑ index : Fin 3, ((primaryLawAt security root).map (fun word => word index)).weight output) =
      offBodyMean security output + ((preRootLaw security .attachment 0).map (shiftEquiv security root)).weight output := by
  simp only [primaryLawAt, FiniteDist.map_mix, FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, triple_histogram]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← FiniteDist.mix_weight, attachment_mixture]
  rfl

def blockVector (security : ℕ) (index : BlockIndex security)
    (law : FiniteDist (Slots security index → Palette security)) : ProfileSpace security :=
  WithLp.toLp 2 (fun output => LocalTensors.degreeTensor
    (fun _ : Slots security index => uniformReference security) law.weight 1 (fun _ => output))

private theorem one_whitened {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (reference : FiniteDist Color) (href : ∀ color, 0 < reference.weight color)
    (law : FiniteDist (Slot → Color)) :
    (WithLp.toLp 2 (fun color => LocalTensors.degreeTensor (fun _ : Slot => reference)
      law.weight 1 (fun _ => color)) : EuclideanSpace ℝ Color) =
      ProfileHilbert.whiten reference.weight (fun color =>
        (∑ slot, (law.map (fun word => word slot)).weight color) - (Fintype.card Slot : ℝ) * reference.weight color) := by
  apply WithLp.ofLp_injective
  funext color
  change LocalTensors.degreeTensor (fun _ : Slot => reference) law.weight 1 (fun _ => color) = _
  rw [ProfileHilbert.whiten_apply, LocalTensors.degreeTensor_one_whitened reference href]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem primary_vector (security : ℕ) (root : ℤ) (index : Fin (Parameters.legCount security)) :
    blockVector security (.inl index) (primaryLawAt security root) =
      offBodyVector security + uniformVector security
        ((preRootLaw security .attachment 0).map (shiftEquiv security root)).weight := by
  change (WithLp.toLp 2 (fun output => LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
    (primaryLawAt security root).weight 1 (fun _ => output)) : ProfileSpace security) = _
  rw [one_whitened (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))]
  simp only [Fintype.card_fin, primary_histogram, offBodyVector, uniformVector]
  rw [← map_add]
  congr 1
  funext output
  simp only [Pi.add_apply, uniformReference_weight, FringeCertificate.uniformProfile, one_div]
  ring

theorem singleton_vector (security : ℕ) (body : Fin (centerCount security) ⊕ Fin (Parameters.modulus security))
    (law : FiniteDist (Palette security)) :
    blockVector security (.inr body) (singletonLaw law) = uniformVector security law.weight := by
  change (WithLp.toLp 2 (fun output => LocalTensors.degreeTensor (fun _ : Fin 1 => uniformReference security)
    (singletonLaw law).weight 1 (fun _ => output)) : ProfileSpace security) = _
  rw [one_whitened (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))]
  simp only [Fintype.card_fin, Fin.sum_univ_one, singleton_marginal, Nat.cast_one, one_mul, uniformVector]

/-- The same complete cyclic difference is moved by the body permutation.
In particular the first latent vertex still reads its closing predecessor. -/
def rootAt (security : ℕ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (position : BodyIndex security) : ℤ :=
  (latent (permutation.symm position)).val -
    (latent ((finRotate (Parameters.bodySize security)).symm (permutation.symm position))).val

def attachmentRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (leg : Fin (Parameters.legCount security)) : ℤ :=
  rootAt security permutation latent (layout (.inr (.inr leg)))

def centerRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (center : Fin (centerCount security)) : ℤ :=
  rootAt security permutation latent (layout (.inl center))

def queueRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (point : Fin (Parameters.modulus security)) : ℤ :=
  rootAt security permutation latent (layout (.inr (.inl point)))

def rootedLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security) :=
  blockLawAt security (attachmentRoots security layout permutation latent)
    (centerRoots security layout permutation latent) (queueRoots security layout permutation latent) queue

def bodyVector (security : ℕ) (role : BodyRole) (queue root : ℤ) : ProfileSpace security :=
  uniformVector security ((preRootLaw security role queue).map (shiftEquiv security root)).weight

theorem body_vector_sum (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (∑ vertex, realizedResponse security (roles security layout) queue permutation latent vertex) =
      (∑ center, bodyVector security .free queue (centerRoots security layout permutation latent center)) +
      ((∑ point, bodyVector security .queue queue (queueRoots security layout permutation latent point)) +
        ∑ leg, bodyVector security .attachment queue (attachmentRoots security layout permutation latent leg)) := by
  have h := (layout.trans permutation.symm).sum_comp
    (realizedResponse security (roles security layout) queue permutation latent)
  simp only [Equiv.trans_apply, realizedResponse, response, roles, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply] at h
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  simpa only [roleOf, Sum.elim_inl, Sum.elim_inr, bodyVector, centerRoots, queueRoots,
    attachmentRoots, rootAt] using h.symm

theorem sum_block_vectors (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (∑ index, blockVector security index (rootedLaw security layout queue permutation latent index)) =
      (∑ vertex, realizedResponse security (roles security layout) queue permutation latent vertex) +
        (Parameters.legCount security : ℝ) • offBodyVector security := by
  rw [body_vector_sum]
  simp only [Fintype.sum_sum_type, rootedLaw, blockLawAt]
  simp_rw [primary_vector, singleton_vector]
  have hqueue (point : Fin (Parameters.modulus security)) :
      uniformVector security ((safeLaw security).map (shiftEquiv security
        (queueRoots security layout permutation latent point + queue))).weight =
      bodyVector security .queue queue (queueRoots security layout permutation latent point) := by
    unfold bodyVector
    rw [preRootLaw, shiftLaw_add, add_comm queue]
  simp_rw [hqueue]
  have hfree (center : Fin (centerCount security)) :
      uniformVector security ((centerLaw security).map
        (shiftEquiv security (centerRoots security layout permutation latent center))).weight =
      bodyVector security .free queue (centerRoots security layout permutation latent center) := rfl
  have hattached (leg : Fin (Parameters.legCount security)) :
      uniformVector security ((preRootLaw security .attachment 0).map
        (shiftEquiv security (attachmentRoots security layout permutation latent leg))).weight =
      bodyVector security .attachment queue (attachmentRoots security layout permutation latent leg) := rfl
  simp_rw [hfree, hattached]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  abel

theorem normalized_first_mean (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (multiple : ℝ) (output : Palette security) :
    (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
      (rootedLaw security layout queue permutation latent)
      (PhysicalFockRates.normalizedScale security multiple) index output) =
      multiple * BackgroundRates.radius security *
        (conditionalMean security layout queue permutation latent).ofLp output := by
  have hpoint := congrArg (fun value : ProfileSpace security => value.ofLp output)
    (sum_block_vectors security layout queue permutation latent)
  simp only [WithLp.ofLp_sum, WithLp.ofLp_add, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, blockVector, smul_eq_mul] at hpoint
  unfold BlockProducts.normalizedLinear BlockProducts.localCoefficient
  rw [← Finset.mul_sum, hpoint]
  simp only [conditionalMean, NormalizedMeanAlgebra.euclideanSum,
    NormalizedMeanAlgebra.normalizationScale, WithLp.ofLp_smul, WithLp.ofLp_add,
    WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    PhysicalFockRates.normalizedScale]
  ring

theorem normalized_first_energy (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (multiple : ℝ) :
    (∑ output, (∑ index, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
      (rootedLaw security layout queue permutation latent)
      (PhysicalFockRates.normalizedScale security multiple) index output) ^ 2) =
      (multiple * BackgroundRates.radius security) ^ 2 * ‖conditionalMean security layout queue permutation latent‖ ^ 2 := by
  simp_rw [normalized_first_mean]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.mul_sum]

end

end CurrentAFT.ActualBlockMean

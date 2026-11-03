import CurrentAFT.PublicOutputExperiment
import CurrentAFT.PairedKeptProduct

/-! # Exact selected and unselected public output identities -/
namespace CurrentAFT.PublicOutputBridge
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels PublicOutputExperiment ControlCoordinates
  JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

def backgroundFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (block : BlockIndex security) : ℝ :=
  (rootedLaw security layout queue permutation latent block).weight (fun slot => word ⟨block, slot⟩)

theorem independent_product_expectation {Index Color : Type*} [Fintype Index] [Fintype Color]
    [DecidableEq Index] (law : Index → FiniteDist Color) (factor : Index → Color → ℝ) :
    (FiniteDist.independent law).expectation (fun word => ∏ index, factor index (word index)) =
      ∏ index, (law index).expectation (factor index) := by
  unfold FiniteDist.expectation FiniteDist.independent
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index color => (law index).weight color * factor index color)).symm

theorem complete_packed_product (security : ℕ) (factor : BlockIndex security → ℝ) :
    (∏ index : Fin (Parameters.legCount security),
      factor (.inl index) * factor (.inr (.inl (compensatorPosition security index)))) *
      (∏ index : Fin (BackgroundRates.ordinaryPool security), factor (.inr (.inl (ordinaryPosition security index)))) *
      (∏ index : Fin (Parameters.modulus security), factor (.inr (.inr index))) = ∏ index, factor index := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rw [← (centerSplit security).prod_comp (fun center => factor (.inr (.inl center)))]
  rw [Fintype.prod_sum_type, Finset.prod_mul_distrib]
  simp only [compensatorPosition, ordinaryPosition, Function.Embedding.coeFn_mk]
  ac_rfl

theorem primary_factor_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (index : Fin (Parameters.legCount security)) :
    (SafeControlGroups.reference security).expectation
      (physicalFactor security layout permutation latent word (.inl index)) =
      backgroundFactor security layout queue permutation latent word (.inl index) *
        backgroundFactor security layout queue permutation latent word (.inr (.inl (compensatorPosition security index))) := by
  unfold physicalFactor
  simp only [FiniteDist.retype_weight]
  have h := SafeControlGroups.reference_expectation security (fun group =>
    (FiniteDist.retype (quadGiven security
      (centerRoots security layout permutation latent (compensatorPosition security index))
      (attachmentRoots security layout permutation latent index) group)).weight (pairedWord security word index))
  simp only [FiniteDist.retype_weight] at h
  rw [h, quadGiven_average]
  unfold backgroundFactor rootedLaw
  simp only [blockLawAt, singletonLaw_weight, pairedWord, Fin.cons_zero, Fin.tail_cons,
    PairedReferenceEnergy.compensatorAt, FiniteDist.map_equiv_weight]
  ring_nf
  congr! 5

theorem ordinary_factor_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (index : Fin (BackgroundRates.ordinaryPool security)) :
    (SafeControlGroups.reference security).expectation
      (physicalFactor security layout permutation latent word (.inr index)) =
      backgroundFactor security layout queue permutation latent word (.inr (.inl (ordinaryPosition security index))) := by
  unfold physicalFactor
  simp only [FiniteDist.retype_weight]
  have h := SafeControlGroups.reference_body_expectation security (fun center =>
    (FiniteDist.retype (bodyGiven security
      (centerRoots security layout permutation latent (ordinaryPosition security index)) center)).weight
        (ordinaryWord security word index))
  simp only [FiniteDist.retype_weight] at h
  rw [h, bodyGiven_average]
  unfold backgroundFactor rootedLaw
  simp only [blockLawAt, singletonLaw_weight, PairedReferenceEnergy.compensatorAt,
    ordinaryWord, FiniteDist.map_equiv_weight]

theorem placed_range {security r s : ℕ} (choice : Choice security r s) :
    Finset.univ.map (placedEmbedding choice) = Finset.univ.map (choice.1.sumMap choice.2) := by
  have huniv : (Finset.univ : Finset (Fin (r + s))).map finSumFinEquiv.symm.toEmbedding = Finset.univ := by
    ext index
    simp
  unfold placedEmbedding
  rw [← Finset.map_map, huniv]

theorem pairedWord_selected {security r s : ℕ} (choice : Choice security r s)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (index : Fin r) :
    pairedWord security word (choice.1 index) = fun slot =>
      word (gather (selection security r s choice) (.inl (primaryIndex index slot))) := by
  funext slot
  refine Fin.cases ?_ (fun slot => ?_) slot
  · simp only [pairedWord, Fin.cons_zero, gather_compensator, selection,
      Function.Embedding.trans_apply]
  · simp only [pairedWord, Fin.cons_succ, gather_primary, selection]

theorem ordinaryWord_selected {security r s : ℕ} (choice : Choice security r s)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (index : Fin s) :
    ordinaryWord security word (choice.2 index) = fun slot =>
      word (gather (selection security r s choice) (.inl (ordinaryIndex index slot))) := by
  funext slot
  simp only [ordinaryWord, gather_ordinary, selection, Function.Embedding.trans_apply]

theorem physical_factor_selected (security r s : ℕ) (choice : Choice security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (index : Fin (r + s)) (control : SafeControlGroups.SafeGroup security) :
    physicalFactor security layout permutation latent word (placedEmbedding choice index) control =
      (publicLaw security r s
        (fun slot => centerRoots security layout permutation latent ((selection security r s choice).compensator slot))
        (fun slot => attachmentRoots security layout permutation latent ((selection security r s choice).primary slot))
        (fun slot => centerRoots security layout permutation latent ((selection security r s choice).body slot))
        index control).weight
        (fun slot => word (gather (selection security r s choice) (.inl ⟨index, slot⟩))) := by
  have hrole (role : Fin r ⊕ Fin s) :
      physicalFactor security layout permutation latent word ((choice.1.sumMap choice.2) role) control =
        (roleLaw security r s
          (fun slot => centerRoots security layout permutation latent ((selection security r s choice).compensator slot))
          (fun slot => attachmentRoots security layout permutation latent ((selection security r s choice).primary slot))
          (fun slot => centerRoots security layout permutation latent ((selection security r s choice).body slot))
          role control).weight
          (fun slot => word (gather (selection security r s choice) (.inl (physicalRoleIndex r s ⟨role, slot⟩)))) := by
    cases role with
    | inl position =>
      simp only [Function.Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl,
        physicalFactor, FiniteDist.retype_weight, roleLaw, selection, Function.Embedding.trans_apply]
      rw [pairedWord_selected]
      rfl
    | inr position =>
      simp only [Function.Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr,
        physicalFactor, FiniteDist.retype_weight, roleLaw, selection, Function.Embedding.trans_apply]
      rw [ordinaryWord_selected]
      rfl
  have htag (slot : physicalSlots r s index) :
      physicalRoleIndex r s ⟨finSumFinEquiv.symm index, slot⟩ = ⟨index, slot⟩ :=
    (Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).symm_apply_apply ⟨index, slot⟩
  simp_rw [← htag]
  unfold placedEmbedding publicLaw
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
  convert hrole (finSumFinEquiv.symm index) using 1

private theorem prod_excluding {Index : Type*} [Fintype Index] [DecidableEq Index]
    (excluded : Finset Index) (factor : Index → ℝ) :
    (∏ index, if index ∉ excluded then factor index else 1) =
      ∏ index : {index // index ∉ excluded}, factor index.val := by
  rw [← Finset.prod_filter]
  exact Finset.prod_subtype _ (fun _ => by simp) _

theorem public_complement_split {security r s : ℕ} (choice : Choice security r s)
    (factor : PublicIndex security → ℝ) :
    (∏ index : {index : PublicIndex security // index ∉ Finset.univ.map (choice.1.sumMap choice.2)}, factor index.val) =
      (∏ index : {index : Fin (Parameters.legCount security) // index ∉ Finset.univ.map choice.1}, factor (.inl index.val)) *
      (∏ index : {index : Fin (BackgroundRates.ordinaryPool security) // index ∉ Finset.univ.map choice.2}, factor (.inr index.val)) := by
  have hleft (index : Fin (Parameters.legCount security)) :
      Sum.inl index ∈ Finset.univ.map (choice.1.sumMap choice.2) ↔ index ∈ Finset.univ.map choice.1 := by
    simp [Finset.mem_map, Function.Embedding.sumMap, Sum.exists]
  have hright (index : Fin (BackgroundRates.ordinaryPool security)) :
      Sum.inr index ∈ Finset.univ.map (choice.1.sumMap choice.2) ↔ index ∈ Finset.univ.map choice.2 := by
    simp [Finset.mem_map, Function.Embedding.sumMap, Sum.exists]
  rw [← prod_excluding, Fintype.prod_sum_type]
  simp only [hleft, hright]
  rw [prod_excluding, prod_excluding]

theorem unselected_factor_average (security r s : ℕ) (choice : Choice security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    (∏ index : {index : PublicIndex security // index ∉ Finset.univ.map (placedEmbedding choice)},
      (SafeControlGroups.reference security).expectation (physicalFactor security layout permutation latent word index.val)) *
      queueFactor security layout queue permutation latent word =
      ∏ index : (selection security r s choice).kept,
        backgroundFactor security layout queue permutation latent word index.val := by
  rw [placed_range]
  rw [public_complement_split choice (fun index =>
    (SafeControlGroups.reference security).expectation (physicalFactor security layout permutation latent word index))]
  simp_rw [primary_factor_average security layout queue, ordinary_factor_average security layout queue]
  exact (PairedKeptProduct.kept_product choice (backgroundFactor security layout queue permutation latent word)).symm

theorem selected_factor_average (security r s : ℕ) (choice : Choice security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (FiniteDist.independent (fun _ : Fin (r + s) => SafeControlGroups.reference security)).expectation
      (fun controls => selectedScore security r s kernel controls *
        ∏ index, physicalFactor security layout permutation latent word (placedEmbedding choice index) (controls index)) =
      TaggedOutputFock.taggedMass security r s (selection security r s choice) layout permutation latent kernel
        (fun point => word (gather (selection security r s choice) (.inl point))) := by
  simp_rw [physical_factor_selected]
  have h := jointMass_public_sum security r s
    (fun slot => centerRoots security layout permutation latent ((selection security r s choice).compensator slot))
    (fun slot => attachmentRoots security layout permutation latent ((selection security r s choice).primary slot))
    (fun slot => centerRoots security layout permutation latent ((selection security r s choice).body slot)) kernel
    (fun point => word (gather (selection security r s choice) (.inl point)))
  apply Eq.trans (TensorPublicProjection.independent_decision_expectation _ _ _ _)
  exact h.symm

/-- One literal summand of the public U-statistic produces the complete
tagged signed law together with every unselected actual background block. -/
theorem placed_weighted_mass (security r s : ℕ) (choice : Choice security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (reference security).expectation (fun controls =>
      selectedScore security r s kernel (controls ∘ placedEmbedding choice) *
        (conditionalLaw security layout queue permutation latent controls).weight word) =
      TaggedOutputFock.conditionalMass security r s (selection security r s choice) layout queue permutation latent kernel
        (word ∘ gather (selection security r s choice)) := by
  simp_rw [conditionalLaw_factor, ← mul_assoc]
  rw [FiniteDist.expectation_mul_const, placed_public_expectation, selected_factor_average,
    mul_assoc, unselected_factor_average]
  unfold TaggedOutputFock.conditionalMass BlockProducts.taggedBlockMass
  rfl

theorem positive_public_average (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    (reference security).expectation (fun controls =>
      (conditionalLaw security layout queue permutation latent controls).weight word) =
      (FiniteDist.retype (BlockProducts.blockLaw (Slots security) (rootedLaw security layout queue permutation latent))).weight word := by
  simp_rw [conditionalLaw_factor]
  rw [FiniteDist.expectation_mul_const]
  unfold reference
  rw [independent_product_expectation, Fintype.prod_sum_type]
  simp_rw [primary_factor_average security layout queue, ordinary_factor_average security layout queue]
  exact complete_packed_product security (backgroundFactor security layout queue permutation latent word)

end
end CurrentAFT.PublicOutputBridge

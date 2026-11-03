import CurrentAFT.SelectedPublicChannels
import CurrentAFT.PairedOutputProduct
import CurrentAFT.ActualWeightedFourier

/-! # The actual positive public experiment weighted by coefficientWeight -/
namespace CurrentAFT.PublicOutputExperiment
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

abbrev PublicIndex (security : ℕ) :=
  Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)
abbrev PublicWord (security : ℕ) := PublicIndex security → SafeControlGroups.SafeGroup security

/-- All public controls are drawn before the protected sources. Ordinary
controls carry an independent unused primary coordinate. -/
def reference (security : ℕ) : FiniteDist (PublicWord security) :=
  FiniteDist.independent (fun _ => SafeControlGroups.reference security)

def actualWeight (security order : ℕ) (coefficient : ActualControls.Coefficients security order)
    (controls : PublicWord security) : ℝ :=
  PhysicalSynthesis.coefficientWeight security order (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) coefficient
    (fun index => SafeControlGroups.unwrap security (controls (.inl index)))
    (fun index => (controls (.inr index)).2)

def conditionalBlocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (controls : PublicWord security) : (index : BlockIndex security) → FiniteDist (Slots security index → ActualBlockMean.Palette security)
  | .inl leg => tripleGiven security (attachmentRoots security layout permutation latent leg) (controls (.inl leg)).1
  | .inr (.inl center) => bodyGiven security (centerRoots security layout permutation latent center)
      (controls ((centerSplit security).symm center)).2
  | .inr (.inr point) => rootedLaw security layout queue permutation latent (.inr (.inr point))

def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (controls : PublicWord security) : FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (conditionalBlocks security layout queue permutation latent controls))

/-- The signed weight depends only on public controls, outside every
protected-source average. No hidden observation enters its normalization. -/
def weightedConditionalMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (conditionalLaw security layout queue permutation latent controls).weight word)

theorem actualWeight_mean (security order : ℕ) (coefficient : ActualControls.Coefficients security order) :
    (reference security).expectation (actualWeight security order coefficient) = coefficient.1 := by
  have h := (SafeControlGroups.common_expectation security (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security)
    (PhysicalSynthesis.coefficientWeight security order (Parameters.legCount security)
      (BackgroundRates.ordinaryPool security) coefficient)).trans
    (PhysicalSynthesis.coefficientWeight_mean security order (Parameters.legCount security)
      (BackgroundRates.ordinaryPool security) coefficient)
  unfold reference actualWeight
  exact (TensorPublicProjection.independent_decision_expectation _ _ _ _).trans h

theorem weightedConditionalMass_sum (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (coefficient : ActualControls.Coefficients security order) :
    (∑ word, weightedConditionalMass security order layout queue permutation latent coefficient word) = coefficient.1 := by
  unfold weightedConditionalMass FiniteDist.expectation
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  exact actualWeight_mean security order coefficient

def fullSelection (security : ℕ) : Selection security (Parameters.legCount security) (BackgroundRates.ordinaryPool security) :=
  selection security _ _ (Function.Embedding.refl _, Function.Embedding.refl _)

def pairedWord (security : ℕ) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (index : Fin (Parameters.legCount security)) : Fin 4 → ActualBlockMean.Palette security :=
  Fin.cons (word ⟨.inr (.inl (compensatorPosition security index)), (0 : Fin 1)⟩)
    (fun slot => word ⟨.inl index, slot⟩)

def ordinaryWord (security : ℕ) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (index : Fin (BackgroundRates.ordinaryPool security)) : Fin 1 → ActualBlockMean.Palette security :=
  fun slot => word ⟨.inr (.inl (ordinaryPosition security index)), slot⟩

def physicalFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    PublicIndex security → SafeControlGroups.SafeGroup security → ℝ
  | .inl index, control =>
    (FiniteDist.retype (quadGiven security (centerRoots security layout permutation latent (compensatorPosition security index))
      (attachmentRoots security layout permutation latent index) (SafeControlGroups.unwrap security control))).weight
      (pairedWord security word index)
  | .inr index, control =>
    (FiniteDist.retype (bodyGiven security (centerRoots security layout permutation latent (ordinaryPosition security index)) control.2)).weight
      (ordinaryWord security word index)

def queueFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  ∏ point : Fin (Parameters.modulus security),
    (rootedLaw security layout queue permutation latent (.inr (.inr point))).weight
      (fun slot => word ⟨.inr (.inr point), slot⟩)

def placedEmbedding {security r s : ℕ} (choice : Choice security r s) : Fin (r + s) ↪ PublicIndex security :=
  finSumFinEquiv.symm.toEmbedding.trans (choice.1.sumMap choice.2)

theorem statistic_choice_average (security r s : ℕ)
    (hprimary : r ≤ Parameters.legCount security) (hbody : s ≤ BackgroundRates.ordinaryPool security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (controls : PublicWord security) :
    twoPoolUStatistic (Parameters.legCount security) (BackgroundRates.ordinaryPool security)
      (PhysicalSynthesis.pairedKernel security r s kernel)
      (fun index => SafeControlGroups.unwrap security (controls (.inl index)))
      (fun index => (controls (.inr index)).2) =
      (choiceLaw security r s hprimary hbody).expectation (fun choice =>
        selectedScore security r s kernel (controls ∘ placedEmbedding choice)) := by
  have hpoint (choice : Choice security r s) :
      selectedScore security r s kernel (controls ∘ placedEmbedding choice) =
        PhysicalSynthesis.pairedKernel security r s kernel
          (fun index => SafeControlGroups.unwrap security (controls (.inl (choice.1 index))))
          (fun index => (controls (.inr (choice.2 index))).2) := by
    rw [selectedScore_eq_pairedKernel]
    simp only [Function.comp_apply, placedEmbedding, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, Equiv.symm_apply_apply, Function.Embedding.sumMap,
      Function.Embedding.coeFn_mk,
      Sum.map_inl, Sum.map_inr]
  simp only [twoPoolUStatistic, FiniteDist.expectation, choiceLaw_weight, hpoint,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro choice _
  simp only [Function.comp_def]
  ring

/-- The placed public expectation integrates every unselected control
against its genuine positive reference law. Both source alphabets and all
falling-factorial normalizers remain exact. -/
theorem placed_public_expectation (security r s : ℕ) (choice : Choice security r s)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (factor : PublicIndex security → SafeControlGroups.SafeGroup security → ℝ) :
    (reference security).expectation (fun controls =>
      selectedScore security r s kernel (controls ∘ placedEmbedding choice) *
        ∏ index, factor index (controls index)) =
      (FiniteDist.independent (fun _ : Fin (r + s) => SafeControlGroups.reference security)).expectation
        (fun controls => selectedScore security r s kernel controls *
          ∏ index, factor (placedEmbedding choice index) (controls index)) *
      ∏ index : {index : PublicIndex security // index ∉ Finset.univ.map (placedEmbedding choice)},
        (SafeControlGroups.reference security).expectation (factor index.val) := by
  have h := FiniteDist.expectation_placed_product (placedEmbedding choice)
    (fun _ => SafeControlGroups.reference security) (selectedScore security r s kernel) factor
  unfold reference
  apply Eq.trans (TensorPublicProjection.independent_decision_expectation _ _ _ _)
  apply Eq.trans h
  apply congrArg₂ (fun first second : ℝ => first * second)
  · exact TensorPublicProjection.independent_decision_expectation _ _ _ _
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    rfl

/-- The full positive sampler has exactly one physical factor per public
control, with the closing cycle roots fixed throughout this identity. -/
theorem conditionalLaw_factor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (controls : PublicWord security) (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    (conditionalLaw security layout queue permutation latent controls).weight word =
      (∏ index, physicalFactor security layout permutation latent word index (controls index)) *
        queueFactor security layout queue permutation latent word := by
  have hcenter := (centerSplit security).prod_comp (fun center =>
    (FiniteDist.retype (bodyGiven security (centerRoots security layout permutation latent center)
      (controls ((centerSplit security).symm center)).2)).weight
        (fun slot => word ⟨.inr (.inl center), slot⟩))
  simp only [FiniteDist.retype_weight, bodyGiven_weight] at hcenter
  unfold conditionalLaw
  simp only [FiniteDist.retype_weight, BlockProducts.blockLaw, BlockProducts.blockMass,
    Fintype.prod_sum_type, conditionalBlocks, bodyGiven_weight]
  rw [← hcenter]
  simp only [Fintype.prod_sum_type, Equiv.symm_apply_apply]
  simp only [physicalFactor, FiniteDist.retype_weight, quadGiven_weight, bodyGiven_weight, pairedWord, ordinaryWord,
    Fin.cons_zero, Fin.tail_cons, queueFactor, SafeControlGroups.unwrap,
    compensatorPosition, ordinaryPosition, Function.Embedding.coeFn_mk, Finset.prod_mul_distrib]
  ac_rfl

theorem full_kept_queue (security : ℕ) (index : (fullSelection security).kept) :
    ∃ point : Fin (Parameters.modulus security), index.val = .inr (.inr point) := by
  have hnot := (Finset.mem_sdiff.mp index.property).2
  rcases index with ⟨leg | center | point, hindex⟩
  · exfalso
    apply hnot
    exact Finset.mem_map.mpr ⟨.inl leg, Finset.mem_univ _, rfl⟩
  · rcases hequal : (centerSplit security).symm center with comp | body
    · exfalso
      apply hnot
      refine Finset.mem_map.mpr ⟨.inr (.inl comp), Finset.mem_univ _, ?_⟩
      change Sum.inr (Sum.inl (centerSplit security (.inl comp))) = Sum.inr (Sum.inl center)
      rw [← hequal, Equiv.apply_symm_apply]
    · exfalso
      apply hnot
      refine Finset.mem_map.mpr ⟨.inr (.inr body), Finset.mem_univ _, ?_⟩
      change Sum.inr (Sum.inl (centerSplit security (.inr body))) = Sum.inr (Sum.inl center)
      rw [← hequal, Equiv.apply_symm_apply]
  · exact ⟨point, rfl⟩

end
end CurrentAFT.PublicOutputExperiment

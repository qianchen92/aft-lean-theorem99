import CurrentAFT.RootTaggedPhysicalFactorization

/-! # The actual cycle component of the complete conditional output PGF -/
namespace CurrentAFT.RootConditionalComponent
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RootTaggedPhysicalFactorization RootUnselectedPhysicalLinear RootBackgroundDenominatorProduct
  RootLocalDenominators RootIndependentBackground LocalReferenceEnergy FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw

private theorem product_fintype_congr {Index Value : Type*} [CommMonoid Value]
    (first second : Fintype Index) (value : Index → Value) :
    (@Finset.univ Index first).prod value = (@Finset.univ Index second).prod value := by
  cases Subsingleton.elim first second
  rfl

private theorem inactive_product_congr {Selected Pool Value : Type*} [CommMonoid Value]
    (first second : Fintype Selected) (embedding : Selected ↪ Pool)
    (firstRest : Fintype {point : Pool // point ∉ (@Finset.univ Selected first).map embedding})
    (secondRest : Fintype {point : Pool // point ∉ (@Finset.univ Selected second).map embedding})
    (value : Pool → Value) :
    (@Finset.univ _ firstRest).prod (fun point => value point.val) =
      (@Finset.univ _ secondRest).prod (fun point => value point.val) := by
  cases Subsingleton.elim first second
  exact product_fintype_congr firstRest secondRest _

theorem positiveAt_mean (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    expectationLinear (rootReference security) (positiveAt security queue block) =
      RootUnselectedBlockChannel.positivePolynomial security queue block := by
  rcases block with leg | (center | point)
  · exact primary_root_average security
  · change (∑ root, (rootReference security).weight root •
      singleGenerating (uniformReference security).weight (RootTaggedLocal.shiftedLaw security .free 0 root).weight) = _
    rw [← singleGenerating_mix]
    rfl
  · change (∑ root, (rootReference security).weight root •
      singleGenerating (uniformReference security).weight (RootTaggedLocal.shiftedLaw security .queue queue root).weight) = _
    rw [← singleGenerating_mix]
    rfl

theorem conditionalPolynomial_active {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (roots : BlockIndex security → Root security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val =
      selectedPolynomial queue selection tagged (roots ∘ rootEmbedding selection tagged) kernel *
        ∏ index : selection.kept, positiveAt security queue index.val (roots index.val) := by
  rw [TypedTaggedPhysical.conditionalPolynomial_product]
  unfold TypedTaggedPhysical.selectedMass
  rw [TypedRolePolynomial.jointMass_generating_eq_typed, TypedRolePolynomial.typedKernel_eq_inputJoint]
  have hchannels : TypedRolePolynomial.raw security r s
      (fun i => ((roots (.inr (.inl (selection.compensator i)))).val : ℤ))
      (fun i => ((roots (.inl (selection.primary i))).val : ℤ))
      (fun i => ((roots (.inr (.inl (selection.body i)))).val : ℤ)) =
      fun role => fixedPhysical queue selection tagged (.inl role)
        (fun slot => (roots ∘ rootEmbedding selection tagged) ⟨.inl role, slot⟩) := by
    funext role
    cases role <;> rfl
  rw [hchannels]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  rw [positiveAt_eq_actual]
  congr 1
  rcases index.val with leg | (center | point) <;> rfl

def keptFactor {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (block : BlockIndex security) (root : Root security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  if block ∈ selection.kept then positiveAt security queue block root else 1

theorem keptFactor_product {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (roots : BlockIndex security → Root security) :
    (∏ block, keptFactor queue selection block (roots block)) =
      ∏ index : selection.kept, positiveAt security queue index.val (roots index.val) := by
  unfold keptFactor
  rw [← Finset.prod_filter]
  have hfilter : (Finset.univ : Finset (BlockIndex security)).filter (fun block => block ∈ selection.kept) =
      selection.kept := by ext block; simp
  rw [hfilter]
  exact Finset.prod_subtype selection.kept (fun _ => Iff.rfl) _

theorem active_keptFactor_product {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security) :
    (∏ slot, keptFactor queue selection (rootEmbedding selection tagged slot) (roots slot)) =
      hitPolynomial queue selection tagged roots := by
  rw [← (activeSlotsEquiv selection tagged).symm.prod_comp]
  rw [Fintype.prod_sum_type]
  have hselected : (∏ slot : Sigma (selectedRootSlots r s), keptFactor queue selection
      (rootEmbedding selection tagged ((activeSlotsEquiv selection tagged).symm (.inl slot)))
      (roots ((activeSlotsEquiv selection tagged).symm (.inl slot)))) = 1 := by
    apply Finset.prod_eq_one
    intro slot _
    have hroot : rootEmbedding selection tagged ((activeSlotsEquiv selection tagged).symm (.inl slot)) =
        selection.removedEmbedding (selectedRootEquiv r s slot) := by
      change activeRootEmbedding selection tagged
        ((activeSlotsEquiv selection tagged) ((activeSlotsEquiv selection tagged).symm (.inl slot))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    have hnot : rootEmbedding selection tagged ((activeSlotsEquiv selection tagged).symm (.inl slot)) ∉ selection.kept := by
      rw [hroot]
      intro hkept
      have hnotremoved : selection.removedEmbedding (selectedRootEquiv r s slot) ∉ selection.removed := by
        simpa only [Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and] using hkept
      apply hnotremoved
      exact Finset.mem_map.mpr ⟨selectedRootEquiv r s slot, Finset.mem_univ _, rfl⟩
    exact if_neg hnot
  rw [hselected, one_mul]
  apply Finset.prod_congr rfl
  intro index _
  change keptFactor queue selection index.val.val (roots ⟨.inr index, (0 : Fin 1)⟩) = _
  exact if_pos index.val.property

theorem inactive_keptFactor_product {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (∏ index : RootInactivePlacement.InactiveRoot selection tagged,
      expectationLinear (rootReference security) (keptFactor queue selection index.val)) =
      ∏ index : InactiveKept selection tagged,
        RootUnselectedBlockChannel.positivePolynomial security queue index.val.val := by
  rw [← (RootInactivePlacement.inactiveEquiv selection tagged).symm.prod_comp]
  apply Finset.prod_congr rfl
  intro index _
  have hfactor : keptFactor queue selection index.val.val = positiveAt security queue index.val.val := by
    funext root
    exact if_pos index.val.property
  change expectationLinear (rootReference security) (keptFactor queue selection index.val.val) = _
  rw [hfactor, positiveAt_mean]

/-- The complete literal tagged-cycle PGF is the true joint raw response
times exactly the inactive mean block polynomials. -/
theorem component_factorization {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    actualComponent security (tagged.map layout.toEmbedding)
      (fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
        (fun block => (roots (layout block)).val) kernel.val) =
      synthesis (ActualRootPhysicalResponse.rawPhysical queue selection tagged) (jointInput selection tagged layout kernel) *
        ∏ index : InactiveKept selection tagged,
          RootUnselectedBlockChannel.positivePolynomial security queue index.val.val := by
  refine (RootBlockReindex.actual_component_blocks selection tagged layout
    (fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val)).trans ?_
  have hsum : (∑ roots, ((FiniteDist.independent (fun _ : BlockIndex security => rootReference security)).weight roots *
      rootDensity selection tagged layout (roots ∘ rootEmbedding selection tagged)) •
        TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val) =
      expectationLinear (FiniteDist.independent (fun _ : BlockIndex security => rootReference security))
        (fun roots => (rootDensity selection tagged layout (roots ∘ rootEmbedding selection tagged) •
          selectedPolynomial queue selection tagged (roots ∘ rootEmbedding selection tagged) kernel) *
            ∏ block, keptFactor queue selection block (roots block)) := by
    simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro roots _
    rw [conditionalPolynomial_active, keptFactor_product, smul_mul_assoc, smul_smul]
  rw [hsum, RootPolynomialPlacement.placed_product (rootEmbedding selection tagged)
    (fun _ : BlockIndex security => rootReference security)
    (fun roots => rootDensity selection tagged layout roots • selectedPolynomial queue selection tagged roots kernel)
    (keptFactor queue selection)]
  apply congrArg₂ (fun first second : MvPolynomial (ActualControls.Palette security) ℝ => first * second)
  · refine Eq.trans ?_ (synthesis_raw_average queue selection tagged layout kernel).symm
    simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr (by ext word; simp)
    intro roots _
    apply congrArg₂ (fun (weight : ℝ) (value : MvPolynomial (ActualControls.Palette security) ℝ) => weight • value)
    · change (∏ slot, (rootReference security).weight (roots slot)) =
        (∏ slot, (rootReference security).weight (roots slot))
      exact Finset.prod_congr (by ext slot; simp) (fun _ _ => rfl)
    · rw [← smul_mul_assoc]
      apply congrArg (fun factor => (rootDensity selection tagged layout roots •
        selectedPolynomial queue selection tagged roots kernel) * factor)
      refine Eq.trans ?_ (active_keptFactor_product queue selection tagged roots)
      exact Finset.prod_congr (by ext slot; simp) (fun _ _ => rfl)
  · refine Eq.trans ?_ (inactive_keptFactor_product queue selection tagged)
    exact inactive_product_congr _ _ (rootEmbedding selection tagged) _ _
      (fun block => expectationLinear (rootReference security) (keptFactor queue selection block))

/-- Multiplying the actual normalized root response by the one complete
same-queue background gives the literal tagged-cycle conditional PGF. -/
theorem response_physical_background {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    BackgroundEvaluation.evaluation security order
      (ActualRootResponse.response order horder queue selection tagged layout kernel) *
        TruncatedOutput.quotientMap order (BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) =
      TruncatedOutput.quotientMap order
        (actualComponent security (tagged.map layout.toEmbedding)
          (fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
            (fun block => (roots (layout block)).val) kernel.val)) := by
  have hden : (∏ group, ActualRootPhysicalResponse.localDenominator queue selection tagged group) *
      (∏ index : InactiveKept selection tagged,
        RootUnselectedBlockChannel.positivePolynomial security queue index.val.val) =
        BackgroundPolynomialEvaluation.fixedQueueGenerating security queue := by
    refine Eq.trans ?_ (denominator_product queue selection tagged)
    apply congrArg₂ (fun first second : MvPolynomial (ActualControls.Palette security) ℝ => first * second)
    · apply Finset.prod_congr (by ext group; simp)
      intro group _
      rcases group with (primary | ordinary) | kept <;> rfl
    · exact Finset.prod_congr (by ext index; simp) (fun _ _ => rfl)
  rw [component_factorization, map_mul, ← ActualRootPhysicalResponse.response_physical_active_denominator
    order horder queue selection tagged layout kernel, mul_assoc, ← map_mul, hden]

end
end CurrentAFT.RootConditionalComponent

import CurrentAFT.RootBackgroundPolynomial

/-! Independent actual root marginals reproduce the constructed background factors. -/

namespace CurrentAFT.RootIndependentBackground

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  BackgroundPolynomialEvaluation BackgroundEndpointLaw RootBackgroundPolynomial
  CycleRootExpansion CycleRootPolynomial BodyRootAverages PairQuadraticEvaluation
  PositiveFirstCoefficient LegPolynomialEvaluation BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference

def tripleEquiv {Color : Type*} : (Fin 3 → Color) ≃ ((Color × Color) × Color) where
  toFun word := ((word 0, word 1), word 2)
  invFun word := ![word.1.1, word.1.2, word.2]
  left_inv word := by funext index; fin_cases index <;> rfl
  right_inv word := rfl

local instance finOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _
local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _
local instance blockIndexDecidableEq (security : ℕ) : DecidableEq (BlockIndex security) := Classical.decEq _

theorem finiteDist_mix_map {Input Output State : Type*} [Fintype Input] [Fintype Output] [Fintype State]
    (law : FiniteDist Input) (map : Input → Output) (kernel : Output → FiniteDist State) :
    (law.map map).mix kernel = law.mix (kernel ∘ map) := by
  ext state
  change (law.map map).expectation (fun output => (kernel output).weight state) =
    law.expectation (fun input => (kernel (map input)).weight state)
  rw [FiniteDist.expectation_map]
  rfl

theorem rootReference_shift_mix (security : ℕ) (law : FiniteDist (ActualControls.Palette security)) :
    (rootReference security).mix (fun root => law.map (shiftEquiv security (root.val : ℤ))) =
      rootAverage security law := by
  unfold rootReference ProtectedCycle.differenceLaw
  rw [finiteDist_mix_map]
  have hshift (edge : BlurSeed security) :
      shiftEquiv security
        (((((edge.1 : ℤ) : Root security) - ((edge.2 : ℤ) : Root security)).val : ℕ) : ℤ) =
        shiftEquiv security (edge.1.val - edge.2.val) := by
    apply shiftEquiv_eq_of_cast
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  ext output
  simp only [FiniteDist.mix_weight, Function.comp_apply, hshift,
    rootAverage, publicBlurLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem singleton_blockGenerating (security : ℕ) (law : FiniteDist (ActualControls.Palette security)) :
    blockGenerating security (singletonLaw law) = singleGenerating (FringeCertificate.uniformProfile security) law.weight := by
  unfold blockGenerating singletonLaw
  rw [finiteGenerating_map]
  simp only [finiteGenerating, singleGenerating, Function.comp_apply, Fin.prod_univ_one]

theorem blockGenerating_mix {Choice Slot : Type*} [Fintype Choice] [Fintype Slot]
    (security : ℕ) (law : FiniteDist Choice) (kernel : Choice → FiniteDist (Slot → ActualControls.Palette security)) :
    blockGenerating security (law.mix kernel) = ∑ choice, law.weight choice • blockGenerating security (kernel choice) := by
  unfold blockGenerating
  rw [finiteGenerating_mix]

theorem expectationLinear_independent_product {Index Color Variable : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
    (law : Index → FiniteDist Color) (polynomial : Index → Color → MvPolynomial Variable ℝ) :
    expectationLinear (FiniteDist.independent law) (fun word => ∏ index, polynomial index (word index)) =
      ∏ index, expectationLinear (law index) (polynomial index) := by
  unfold expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.independent,
    MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index color => MvPolynomial.C ((law index).weight color) * polynomial index color)).symm

theorem sum_triple_word {Color Value : Type*} [Fintype Color] [AddCommMonoid Value]
    (test : Color → Color → Color → Value) :
    (∑ word : Fin 3 → Color, test (word 0) (word 1) (word 2)) = ∑ first, ∑ second, ∑ third, test first second third := by
  simpa [tripleEquiv, Fintype.sum_prod_type] using
    ((tripleEquiv (Color := Color)).symm.sum_comp
      (fun word : Fin 3 → Color => test (word 0) (word 1) (word 2))).symm

theorem positiveTriple_generating (security : ℕ) (root : ℤ) (scalar : LocalReferenceEnergy.Scalar security) :
    blockGenerating security (positiveTripleLaw security root scalar) =
      pairGenerating (FringeCertificate.uniformProfile security)
          (fun first second => (conditionalPairLaw security scalar).weight (first, second)) *
        singleGenerating (FringeCertificate.uniformProfile security) (attachmentAt security root scalar).weight := by
  rw [← tripleGenerating_tensor]
  unfold blockGenerating finiteGenerating tripleGenerating
  simp_rw [positiveTriple_weight]
  simp only [PhysicalBlockTensors.tripleMass, tripleMassAt, Fin.prod_univ_three]
  simp_rw [← conditionalPairLaw_weight]
  rw [sum_triple_word (fun first second third =>
    MvPolynomial.C ((conditionalPairLaw security scalar).weight (first, second) *
      (attachmentAt security root scalar).weight third) *
      (centeredFactor (FringeCertificate.uniformProfile security) first *
        centeredFactor (FringeCertificate.uniformProfile security) second *
        centeredFactor (FringeCertificate.uniformProfile security) third))]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  ring

theorem singleGenerating_mix {Choice Color : Type*} [Fintype Choice] [Fintype Color]
    (reference : Color → ℝ) (law : FiniteDist Choice) (kernel : Choice → FiniteDist Color) :
    singleGenerating reference (law.mix kernel).weight =
      ∑ choice, law.weight choice • singleGenerating reference (kernel choice).weight :=
  finiteGenerating_mix law kernel (centeredFactor reference)

theorem rootReference_attachment_mix (security : ℕ) (scalar : LocalReferenceEnergy.Scalar security) :
    (rootReference security).mix (fun root => attachmentAt security root.val scalar) = attachmentLaw security scalar := by
  have happ (root : Root security) : attachmentAt security root.val scalar =
      (shiftedSafeLaw security scalar.val).map (shiftEquiv security root.val) := by
    unfold attachmentAt shiftedSafeLaw
    rw [shiftLaw_add, add_comm scalar.val]
  simp_rw [happ]
  exact rootReference_shift_mix security _

theorem average_scalar_product {Root Scalar Variable : Type*} [Fintype Root] [Fintype Scalar]
    (rootLaw : FiniteDist Root) (scalarLaw : FiniteDist Scalar)
    (pair : Scalar → MvPolynomial Variable ℝ) (body : Root → Scalar → MvPolynomial Variable ℝ) :
    (∑ root, rootLaw.weight root • (∑ scalar, scalarLaw.weight scalar • (pair scalar * body root scalar))) =
      ∑ scalar, scalarLaw.weight scalar • (pair scalar * ∑ root, rootLaw.weight root • body root scalar) := by
  simp only [Finset.smul_sum, MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro scalar _
  apply Finset.sum_congr rfl
  intro root _
  ring

theorem primary_root_average (security : ℕ) :
    (∑ root : Root security, (rootReference security).weight root • blockGenerating security (primaryLawAt security root.val)) =
      legGenerating security := by
  simp only [primaryLawAt, blockGenerating_mix, positiveTriple_generating]
  rw [average_scalar_product]
  simp_rw [← singleGenerating_mix, rootReference_attachment_mix]
  unfold legGenerating
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  rw [singleGenerating_mass_one _ _ (attachmentLaw security scalar).sum_one]
  exact (conditionalLegGenerating_factorization security scalar).symm

theorem singleton_root_average (security : ℕ) (law : FiniteDist (ActualControls.Palette security)) :
    (∑ root : Root security, (rootReference security).weight root •
      blockGenerating security (singletonLaw (law.map (shiftEquiv security root.val)))) =
      singleGenerating (FringeCertificate.uniformProfile security) (rootAverage security law).weight := by
  simp_rw [singleton_blockGenerating]
  rw [← singleGenerating_mix, rootReference_shift_mix]

def roleMeanPolynomial (security : ℕ) (queue : ℤ) : ConditionalHistogramMean.RoleIndex security → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl _ => singleGenerating (FringeCertificate.uniformProfile security) (BackgroundCertificates.convolvedCenterLaw security).weight
  | .inr (.inl _) => singleGenerating (FringeCertificate.uniformProfile security) (BackgroundPolynomialEvaluation.queueLaw security queue).weight
  | .inr (.inr _) => legGenerating security

theorem local_root_average (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ) (vertex : Vertex security) :
    expectationLinear (rootReference security) (localPolynomial security layout queue vertex) =
      roleMeanPolynomial security queue (layout.symm vertex) := by
  change (∑ root : Root security, (rootReference security).weight root •
    localPolynomial security layout queue vertex root) = _
  unfold localPolynomial localPolynomialInt roleMeanPolynomial
  generalize layout.symm vertex = role
  rcases role with free | queueOrLeg
  · rw [singleton_root_average, rootAverage_free]
  · rcases queueOrLeg with point | leg
    · have hmap (root : Root security) :
        (safeLaw security).map (shiftEquiv security ((root.val : ℤ) + queue)) =
          (shiftedSafeLaw security queue).map (shiftEquiv security root.val) := by
        unfold shiftedSafeLaw
        rw [shiftLaw_add, add_comm queue]
      simp_rw [hmap]
      exact singleton_root_average security _
    · exact primary_root_average security

theorem independent_background_generating (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
      (fun roots => ∏ vertex, localPolynomial security layout queue vertex (roots vertex)) = fixedQueueGenerating security queue := by
  rw [expectationLinear_independent_product]
  simp_rw [local_root_average]
  rw [← Equiv.prod_comp layout (fun vertex => roleMeanPolynomial security queue (layout.symm vertex))]
  simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type, roleMeanPolynomial,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold fixedQueueGenerating
  ac_rfl

theorem cycle_defect_eq (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ) :
    polynomialDefect security (localPolynomial security layout queue) =
      finiteGenerating (cycleBackgroundLaw security layout queue)
        (fun word => ∏ slot : Sigma (Slots security),
          centeredFactor (FringeCertificate.uniformProfile security) (word slot)) - fixedQueueGenerating security queue := by
  rw [polynomialDefect, independent_background_generating, ← cycleBackgroundLaw_generating]

def averagedCycleLaw (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) :
    FiniteDist (Sigma (Slots security) → ActualControls.Palette security) :=
  (scalarLaw security).mix (fun queue => cycleBackgroundLaw security layout queue.val)

def averagedRootDefect (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ queue, (scalarLaw security).weight queue • polynomialDefect security (localPolynomial security layout queue.val)

theorem averaged_cycle_generating (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) :
    finiteGenerating (averagedCycleLaw security layout)
      (fun word => ∏ slot : Sigma (Slots security),
        centeredFactor (FringeCertificate.uniformProfile security) (word slot)) =
      backgroundGenerating security + averagedRootDefect security layout := by
  have hqueue (queue : ℤ) :
      finiteGenerating (cycleBackgroundLaw security layout queue)
        (fun word => ∏ slot : Sigma (Slots security),
          centeredFactor (FringeCertificate.uniformProfile security) (word slot)) =
        fixedQueueGenerating security queue + polynomialDefect security (localPolynomial security layout queue) := by
    rw [cycle_defect_eq]
    abel
  unfold averagedCycleLaw averagedRootDefect backgroundGenerating
  rw [finiteGenerating_mix]
  simp only [hqueue, smul_add, Finset.sum_add_distrib]

theorem averaged_cycle_truncated_sources (security order : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) :
    truncate (fun _ : ActualControls.Palette security => 1) order
        (finiteGenerating (averagedCycleLaw security layout)
          (fun word => ∏ slot : Sigma (Slots security),
            centeredFactor (FringeCertificate.uniformProfile security) (word slot))) =
      truncate (fun _ : ActualControls.Palette security => 1) order (backgroundGenerating security) +
        ∑ queue, (scalarLaw security).weight queue •
          ∑ selected ∈ (Finset.univ : Finset (Finset (Vertex security))).filter
              (fun selected => 2 ≤ selected.card ∧ selected.card ≤ order),
            truncate (fun _ : ActualControls.Palette security => 1) order
              (polynomialComponent security selected (localPolynomial security layout queue.val)) := by
  rw [averaged_cycle_generating, truncate_add]
  unfold averagedRootDefect
  rw [truncate_finset_sum]
  have hsmul (scalar : ℝ) (polynomial : MvPolynomial (ActualControls.Palette security) ℝ) :
      truncate (fun _ => 1) order (scalar • polynomial) = scalar • truncate (fun _ => 1) order polynomial :=
    TruncatedOutput.cut_smul order scalar polynomial
  simp only [hsmul, actual_defect_truncated_sources]

end

end CurrentAFT.RootIndependentBackground

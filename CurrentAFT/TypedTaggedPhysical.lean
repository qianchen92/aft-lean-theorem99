import CurrentAFT.RootGroupedSourceFormula
import CurrentAFT.RootLocalDenominators
import CurrentAFT.PairedOutputProduct

/-! # Literal complete conditional tagged output polynomials

All remaining blocks stay in the product. The selected common-alphabet
score is the original kernel with only its independent unused controls added.
-/
namespace CurrentAFT.TypedTaggedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection TaggedOutputFock
  JointTaggedPhysicalFock PairedOutputPlacement LocalReferenceEnergy
  RootBackgroundPolynomial BackgroundPolynomialEvaluation RootLocalDenominators
  CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
local instance actualGroupDecidableEq (security : ℕ) :
    DecidableEq (JointTaggedPhysicalFock.Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {Index Color : Type*} [Fintype Index] [Fintype Color]

/-- The actual centered PGF factors for arbitrary signed local masses. -/
theorem signed_block_generating (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : Color → ℝ) (mass : (index : Index) → (slots index → Color) → ℝ) :
    centeredGeneratingLinear reference
      (fun word : Sigma slots → Color => ∏ index, mass index (fun slot => word ⟨index, slot⟩)) =
      ∏ index, centeredGeneratingLinear reference (mass index) := by
  have hequiv := (Equiv.piCurry (fun index (_ : slots index) => Color)).sum_comp
    (fun word => ∏ index, MvPolynomial.C (mass index (word index)) *
      ∏ slot, centeredFactor reference (word index slot))
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul,
    map_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma slots → Color,
        ∏ index, (MvPolynomial.C (mass index (fun slot => word ⟨index, slot⟩)) *
          ∏ slot, centeredFactor reference (word ⟨index, slot⟩)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → slots index → Color,
        ∏ index, (MvPolynomial.C (mass index (word index)) *
          ∏ slot, centeredFactor reference (word index slot)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : slots index → Color) =>
      MvPolynomial.C (mass index word) * ∏ slot, centeredFactor reference (word slot))).symm

theorem signed_split_generating {Left Right : Type*} [Fintype Left] [Fintype Right]
    (reference : Color → ℝ) (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ) :
    centeredGeneratingLinear reference
      (fun word : Left ⊕ Right → Color => first (word ∘ Sum.inl) * second (word ∘ Sum.inr)) =
      centeredGeneratingLinear reference first * centeredGeneratingLinear reference second := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul]
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    Fintype.prod_sum_type, Function.comp_def, Sum.elim_inl, Sum.elim_inr, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro firstWord _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondWord _
  ring

end Generic

abbrev Palette (security : ℕ) := ActualControls.Palette security

def blockLaw (security : ℕ) (queue : ℤ) (roots : BlockIndex security → ℤ) :=
  blockLawAt security (fun leg => roots (.inl leg)) (fun center => roots (.inr (.inl center)))
    (fun point => roots (.inr (.inr point))) queue

def selectedMass {security r s : ℕ} (selection : Selection security r s)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :=
  jointMass security r s
    (fun index => roots (.inr (.inl (selection.compensator index))))
    (fun index => roots (.inl (selection.primary index)))
    (fun index => roots (.inr (.inl (selection.body index)))) kernel

def conditionalMass {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    (OutputIndex selection → Palette security) → ℝ :=
  BlockProducts.taggedBlockMass (fun index : selection.kept => Slots security index.val)
    (selectedMass selection roots kernel) (fun index => blockLaw security queue roots index.val)

def conditionalPolynomial {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    MvPolynomial (Palette security) ℝ :=
  centeredGeneratingLinear (uniformReference security).weight (conditionalMass selection queue roots kernel)

theorem jointMass_generating (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    centeredGeneratingLinear (uniformReference security).weight
      (jointMass security r s compensator attachment body kernel) =
      ∑ input : Fin (r + s) → JointTaggedPhysicalFock.Group security,
        finiteKernel kernel input • ∏ index,
          centeredGeneratingLinear (uniformReference security).weight
            (physicalChannel security r s compensator attachment body index (Pi.single (input index) 1)) := by
  have hmass : jointMass security r s compensator attachment body kernel =
      ∑ input : Fin (r + s) → JointTaggedPhysicalFock.Group security,
        finiteKernel kernel input • fun word => ∏ index,
          physicalChannel security r s compensator attachment body index (Pi.single (input index) 1)
            (fun slot => word ⟨index, slot⟩) := by
    funext word
    simp only [jointMass, JointPhysicalChannel.mass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  exact signed_block_generating (physicalSlots r s) (uniformReference security).weight _

/-- The full physical product contains the complete selected response and
every kept block. No output degree has been discarded. -/
theorem conditionalPolynomial_product {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    conditionalPolynomial selection queue roots kernel =
      centeredGeneratingLinear (uniformReference security).weight (selectedMass selection roots kernel) *
        ∏ index : selection.kept, blockGenerating security (blockLaw security queue roots index.val) := by
  unfold conditionalPolynomial conditionalMass BlockProducts.taggedBlockMass
  rw [signed_split_generating]
  congr 1
  unfold BlockProducts.blockMass
  rw [signed_block_generating]
  apply Finset.prod_congr rfl
  intro index _
  exact generating_eq_block security _

/-- Literal local-product expansion of the true full conditional signed PGF.
The one joint kernel stays inside the single common-control source sum. -/
theorem conditionalPolynomial_expansion {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    conditionalPolynomial selection queue roots kernel =
      (∑ input : Fin (r + s) → JointTaggedPhysicalFock.Group security,
        finiteKernel kernel input • ∏ index,
          centeredGeneratingLinear (uniformReference security).weight
            (physicalChannel security r s
              (fun i => roots (.inr (.inl (selection.compensator i))))
              (fun i => roots (.inl (selection.primary i)))
              (fun i => roots (.inr (.inl (selection.body i)))) index (Pi.single (input index) 1))) *
        ∏ index : selection.kept, blockGenerating security (blockLaw security queue roots index.val) := by
  rw [conditionalPolynomial_product]
  unfold selectedMass
  rw [jointMass_generating]

theorem actual_component_expansion {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (queue : ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    actualComponent security (tagged.map layout.toEmbedding)
      (fun roots => conditionalPolynomial selection queue (fun block => (roots (layout block)).val) kernel) =
      ∑ roots, ((FiniteDist.independent (fun _ : Vertex security => rootReference security)).weight roots *
        selectedCoefficient security tagged.card (PairedRootInput.labels tagged layout)
          (roots ∘ PairedRootInput.labels tagged layout)) •
          ((∑ input : Fin (r + s) → JointTaggedPhysicalFock.Group security,
            finiteKernel kernel input • ∏ index,
              centeredGeneratingLinear (uniformReference security).weight
                (physicalChannel security r s
                  (fun i => (roots (layout (.inr (.inl (selection.compensator i))))).val)
                  (fun i => (roots (layout (.inl (selection.primary i)))).val)
                  (fun i => (roots (layout (.inr (.inl (selection.body i))))).val)
                  index (Pi.single (input index) 1))) *
            ∏ index : selection.kept, blockGenerating security
              (blockLaw security queue (fun block => (roots (layout block)).val) index.val)) := by
  rw [PairedRootInput.actual_component]
  simp_rw [conditionalPolynomial_expansion]

end
end CurrentAFT.TypedTaggedPhysical

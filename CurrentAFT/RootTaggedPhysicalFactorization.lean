import CurrentAFT.ActualRootPhysicalResponse
import CurrentAFT.RootPhysicalAverages
import CurrentAFT.RootPolynomialPlacement
import CurrentAFT.RootInactivePlacement
import CurrentAFT.RootBlockReindex

/-! # Full joint root/control Fubini for the actual physical block product -/
namespace CurrentAFT.RootTaggedPhysicalFactorization
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RaisingPatternBudget FinitePolynomialTensor ActualRootPhysicalResponse
  LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def unitPolynomial {Variable : Type*} (value : MvPolynomial Variable ℝ) :
    (Unit → ℝ) →ₗ[ℝ] MvPolynomial Variable ℝ where
  toFun score := score () • value
  map_add' first second := add_smul _ _ _
  map_smul' scalar score := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]

def fixedPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : (group : ActiveGroup selection tagged) →
    (groupRootSlots selection tagged group → Root security) →
    (ControlInput selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ
  | .inl (.inl _), roots => RootPhysicalAverages.primaryAt security roots
  | .inl (.inr _), roots => RootPhysicalAverages.ordinaryAt security roots
  | .inr index, roots => unitPolynomial (RootUnselectedPhysicalLinear.positiveAt security queue index.val.val (roots (0 : Fin 1)))

def rootReferenceByGroup {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    FiniteDist (groupRootSlots selection tagged group → Root security) :=
  FiniteDist.independent (fun _ => rootReference security)

theorem rawPhysical_eq_average {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    rawPhysical queue selection tagged = RootPolynomialTensor.averagedChannel
      (rootReferenceByGroup selection tagged) (fixedPhysical queue selection tagged) := by
  funext group
  rcases group with (primary | ordinary) | kept
  · exact RootPhysicalAverages.primaryRaw_eq_average security
  · exact RootPhysicalAverages.ordinaryRaw_eq_average security
  · apply LinearMap.ext
    intro score
    simp only [rawPhysical, RootUnselectedPhysicalLinear.raw, RootUnselectedPhysicalLinear.rawRoot,
      RootUnselectedGrouped.extractLinear, RootUnselectedGrouped.inputEquiv,
      RootPolynomialTensor.averagedChannel, rootReferenceByGroup, fixedPhysical, unitPolynomial,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, RootPolynomialTensor.sliceLinear,
      LinearMap.coe_mk, AddHom.coe_mk, Equiv.coe_fn_symm_mk]
    change (∑ root : Root security, ((rootReference security).weight root * score ((fun _ => root), ())) •
      RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val root) =
      ∑ roots : Fin 1 → Root security,
        (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).weight roots •
          score (roots, ()) • RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val (roots 0)
    conv_rhs => rw [← (Equiv.funUnique (Fin 1) (Root security)).symm.sum_comp
      (fun roots : Fin 1 → Root security =>
        (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).weight roots •
          score (roots, ()) • RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val (roots 0))]
    simp only [FiniteDist.independent, Fin.prod_univ_one, Equiv.funUnique_symm_apply,
      uniqueElim_const, smul_smul]
    apply Finset.sum_congr rfl
    intro root _
    have hconstant : (uniqueElim root : Fin 1 → Root security) = fun _ => root :=
      funext (uniqueElim_const root)
    rw [hconstant]
    rfl

def selectedPolynomial {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    MvPolynomial (Palette security) ℝ :=
  synthesis (fun role => fixedPhysical queue selection tagged (.inl role)
    (fun slot => roots ⟨.inl role, slot⟩)) (RaisingPatternKernel.inputJoint security kernel)

def hitPolynomial {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security) : MvPolynomial (Palette security) ℝ :=
  ∏ index : HitKept selection tagged,
    RootUnselectedPhysicalLinear.positiveAt security queue index.val.val (roots ⟨.inr index, (0 : Fin 1)⟩)

theorem fixed_synthesis {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    synthesis (fun group => fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))
      (controlKernel selection tagged kernel) =
      selectedPolynomial queue selection tagged roots kernel * hitPolynomial queue selection tagged roots := by
  unfold selectedPolynomial hitPolynomial synthesis controlKernel
  rw [← (Equiv.prodPiEquivSumPi (RoleInput security r s)
    (fun _ : HitKept selection tagged => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, fixedPhysical, unitPolynomial,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, one_smul, Fintype.sum_unique]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro controls _
  rw [smul_mul_assoc]

theorem synthesis_raw_average {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    synthesis (rawPhysical queue selection tagged) (jointInput selection tagged layout kernel) =
      expectationLinear
        (FiniteDist.independent (fun _ : Sigma (groupRootSlots selection tagged) => rootReference security))
        (fun roots => rootDensity selection tagged layout roots •
          (selectedPolynomial queue selection tagged roots kernel * hitPolynomial queue selection tagged roots)) := by
  rw [rawPhysical_eq_average, RootPolynomialTensor.synthesis_averaged]
  rw [← (Equiv.piCurry (fun group (_ : groupRootSlots selection tagged group) => Root security)).sum_comp]
  change (∑ roots : Sigma (groupRootSlots selection tagged) → Root security,
    (∏ group, (rootReferenceByGroup selection tagged group).weight (fun slot => roots ⟨group, slot⟩)) •
      synthesis (fun group => fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))
        (fun controls => jointInput selection tagged layout kernel (fun group => ((fun slot => roots ⟨group, slot⟩), controls group)))) = _
  have hinput (roots : Sigma (groupRootSlots selection tagged) → Root security) :
      (fun controls => jointInput selection tagged layout kernel (fun group => ((fun slot => roots ⟨group, slot⟩), controls group))) =
        rootDensity selection tagged layout roots • controlKernel selection tagged kernel := rfl
  simp_rw [hinput]
  unfold expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro roots _
  have hscale := (synthesisLinear
    (fun group => fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))).map_smul
      (rootDensity selection tagged layout roots) (controlKernel selection tagged kernel)
  change synthesis _ (rootDensity selection tagged layout roots • controlKernel selection tagged kernel) =
    rootDensity selection tagged layout roots • synthesis _ (controlKernel selection tagged kernel) at hscale
  rw [hscale, fixed_synthesis]
  congr 1
  simp only [rootReferenceByGroup, FiniteDist.independent, Fintype.prod_sigma]

end
end CurrentAFT.RootTaggedPhysicalFactorization

import CurrentAFT.RootUnselectedChannels
import AFT.SignedFirstCoefficient

/-! Exact first/higher coefficient split of the actual root-centered unselected leg. -/
namespace CurrentAFT.RootLegFirstCoefficient
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegNormalized RootLegReciprocal LocalRaisingFirst BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem completeFamily_no_body (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (arity : TruncatedArity order) (hbody : 0 < arity.val.2.val) :
    completeFamily security order mass arity = 0 := complete_primaryOnly security order mass arity hbody

theorem selectedDensity_singleton (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (slot : Fin 3) (hdegree : Fintype.card ({slot} : Finset (Fin 3)) = 1) (color : Palette security) :
    selectedDensity security 1 mass {slot} hdegree (fun _ => color) =
      ((∑ word, if word slot = color then mass word else 0) -
        (LocalReferenceEnergy.uniformReference security).weight color * ∑ word, mass word) /
          (primaryLaw security).weight color := by
  unfold selectedDensity
  rw [LocalTensors.referenceRestrictedComponent_singleton]
  rfl

theorem tensorInverse_one (security : ℕ) (density : (Fin 1 → Palette security) → ℝ)
    (color : Palette security) :
    PrimaryTensorInverse.tensorInverse security 1 density (fun _ => color) =
      PrimaryTensorInverse.densityInverse security (fun input => density (fun _ => input)) color := by
  change PrimaryTensorInverse.densityInverse security (fun input => density (Fin.cons input Fin.elim0)) color = _
  have hfun : (fun input => density (Fin.cons input Fin.elim0)) =
      (fun input => density (fun _ => input)) := by
    funext input
    congr 1
    funext index
    have hi : index = 0 := Fin.eq_zero index
    subst index
    rfl
  exact congrArg (fun f => PrimaryTensorInverse.densityInverse security f color) hfun

theorem selectedKernel_one (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = 1)
    (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security) :
    (selectedKernel security 1 mass selected hdegree).val colors centers =
      normalizedSelectedDensity security 1 mass selected hdegree colors := by
  change symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
    normalizedSelectedDensity security 1 mass selected hdegree colors) colors centers = _
  rw [symmetrize_of_symmetric]
  intro primaryOrder bodyOrder input _
  congr 1
  funext index
  have hi : primaryOrder index = index := Subsingleton.elim _ _
  simp only [Function.comp_apply, hi]

theorem selectedFamily_singleton_primary (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → Palette security) → ℝ) (slot : Fin 3) (color : Palette security) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass {slot}) color =
      PrimaryTensorInverse.densityInverse security (fun input =>
        ((∑ word, if word slot = input then mass word else 0) -
          (LocalReferenceEnergy.uniformReference security).weight input * ∑ word, mass word) /
            (primaryLaw security).weight input) color := by
  have hsingle : selectedFamily security order mass {slot} =
      Pi.single (primaryArity order horder) (selectedKernel security 1 mass {slot} (by simp)) := by
    unfold selectedFamily
    rw [dif_pos (by simpa using horder)]
    unfold selectedArity primaryArity
    rfl
  rw [hsingle]
  unfold primaryCoefficient
  rw [Pi.single_eq_same]
  rw [selectedKernel_one]
  unfold normalizedSelectedDensity
  change PrimaryTensorInverse.densityInverse security
    (fun input => selectedDensity security 1 mass {slot} _ (Fin.cons input Fin.elim0)) color = _
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  have hword : Fin.cons input Fin.elim0 = (fun _ : Fin 1 => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword]
  exact selectedDensity_singleton security mass slot _ input

theorem selectedFamily_primary_nonone (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3)) (hcard : selected.card ≠ 1) :
    primaryProjection (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass selected) = 0 := by
  funext color
  unfold primaryProjection primaryCoefficient selectedFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    · rfl
    · intro hequal
      have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
      exact hcard h.symm
  · rfl

private theorem sum_nonempty_singletons {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (term : Finset Slot → ℝ) (hzero : ∀ selected, selected.card ≠ 1 → term selected = 0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected) =
      ∑ slot, term {slot} := by
  let singles := (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card = 1)
  have hsubset : singles ⊆ (Finset.univ : Finset (Finset Slot)).erase ∅ := by
    intro selected hselected
    apply Finset.mem_erase.mpr
    constructor
    · intro hequal
      have hcard := (Finset.mem_filter.mp hselected).2
      rw [hequal, Finset.card_empty] at hcard
      omega
    · exact Finset.mem_univ _
  have hreduce : (∑ selected ∈ singles, term selected) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected := by
    apply Finset.sum_subset hsubset
    intro selected _ hnot
    apply hzero
    intro hcard
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
  rw [← hreduce]
  symm
  apply Finset.sum_bij (fun slot _ => ({slot} : Finset Slot))
  · intro slot _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton _⟩
  · intro first _ second _ hequal
    exact Finset.singleton_injective hequal
  · intro selected hselected
    obtain ⟨slot, hequal⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hselected).2
    exact ⟨slot, Finset.mem_univ _, hequal.symm⟩
  · intro slot _
    rfl

theorem completeFamily_primary_centered (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (completeFamily security order mass) =
        PrimaryTensorInverse.densityInverse security
          (fun color => LocalTensors.signedColorCount mass color / (primaryLaw security).weight color) := by
  change primaryProjection (primaryLaw security) (bodyReference security) order horder
    (completeFamily security order mass) = _
  unfold completeFamily
  rw [map_add, map_smul, primaryProjection_one, smul_zero, zero_add, map_sum]
  funext color
  simp only [Finset.sum_apply]
  rw [sum_nonempty_singletons _ (fun selected hcard =>
    congrFun (selectedFamily_primary_nonone security order horder mass selected hcard) color)]
  simp only [primaryProjection, LinearMap.coe_mk, AddHom.coe_mk, selectedFamily_singleton_primary,
    hmass, mul_zero, sub_zero]
  have hsum : (∑ slot : Fin 3, PrimaryTensorInverse.densityInverse security
      (fun input => (∑ word, if word slot = input then mass word else 0) /
        (primaryLaw security).weight input) color) =
      PrimaryTensorInverse.densityInverse security
        (∑ slot : Fin 3, fun input => (∑ word, if word slot = input then mass word else 0) /
          (primaryLaw security).weight input) color := by
    rw [map_sum]
    simp only [Finset.sum_apply]
  rw [hsum]
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  simp only [Finset.sum_apply, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  unfold LocalTensors.signedColorCount
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  split_ifs <;> simp

def firstScore (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) : Palette security → ℝ :=
  primaryCoefficient (primaryLaw security) (bodyReference security) order horder (completeFamily security order mass)

theorem firstScore_centered (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) :
    (primaryLaw security).expectation (firstScore security order horder mass) = 0 := by
  let color : Palette security := ⟨0, (Parameters.modulus_spec security).2.pos⟩
  let kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 :=
    completeFamily security order mass (primaryArity order horder)
  have h := kernel.property.1 (0 : Fin 1) (fun _ => color) Fin.elim0
  have hupdate (input : Palette security) : Function.update (fun _ : Fin 1 => color) 0 input = (fun _ => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    exact Function.update_self _ _ _
  simp only [hupdate] at h
  exact h

def firstFamily (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) : Family security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder (firstScore security order horder mass)
    (firstScore_centered security order horder mass)

theorem complete_sub_first_raises (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (completeFamily security order mass - firstFamily security order horder mass) := by
  intro arity hsmall
  change completeFamily security order mass arity - firstFamily security order horder mass arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [completeFamily_no_body security order mass arity hb]
    unfold firstFamily primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [completeFamily_zeroArity, hmass, zero_smul]
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      rfl

theorem complete_eq_first_add_higher (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    completeFamily security order mass = firstFamily security order horder mass + higherFamily security order mass := by
  funext arity
  change completeFamily security order mass arity = firstFamily security order horder mass arity + higherFamily security order mass arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [higherFamily_vanishesBelow security order mass arity hsmall, add_zero]
    exact sub_eq_zero.mp (complete_sub_first_raises security order horder mass hmass arity hsmall)
  · have hfirst : firstFamily security order horder mass arity = 0 := by
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hfirst, zero_add]
    unfold completeFamily higherFamily
    simp only [hmass, zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl


theorem signedColorCount_law {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (law : FiniteDist (Slot → Color)) (color : Color) :
    LocalTensors.signedColorCount law.weight color =
      ∑ slot, (law.map (fun word => word slot)).weight color := by
  unfold LocalTensors.signedColorCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  rw [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> simp

theorem signedColorCount_rawMass (security : ℕ) (input : CycleRootExpansion.Root security → ℝ) (color : Palette security) :
    LocalTensors.signedColorCount (RootTaggedLegHigher.rawMassLinear security input) color =
      ∑ root, (CycleRootExpansion.rootReference security).weight root * input root *
        RootTaggedLegFirst.legHistogram security root color := by
  unfold LocalTensors.signedColorCount RootTaggedLegHigher.rawMassLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  have hhist := signedColorCount_law (ActualBlockFock.primaryLawAt security root.val) color
  unfold RootTaggedLegFirst.legHistogram
  rw [← hhist]
  unfold LocalTensors.signedColorCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem signedColorCount_rootMass (security : ℕ) (input : CycleRootExpansion.Root security → ℝ) :
    LocalTensors.signedColorCount (RootTaggedLegHigher.massLinear security input) =
      RootTaggedLocal.rootMass security .attachment 0 input := by
  funext color
  change LocalTensors.signedColorCount (RootTaggedLegHigher.rawMassLinear security
    (TensorChannel.center (CycleRootExpansion.rootReference security) input)) color = _
  rw [signedColorCount_rawMass]
  rw [← RootTaggedLegFirst.legFirstMass_eq_rootMass]
  simp only [TensorChannel.center_apply, RootTaggedLegFirst.legFirstMass, LinearMap.coe_mk, AddHom.coe_mk,
    RootTaggedLegFirst.meanLegHistogram, FiniteDist.expectation, mul_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  ring

theorem actual_firstScore (security order : ℕ) (horder : 1 ≤ order) (input : CycleRootExpansion.Root security → ℝ) :
    firstScore security order horder (RootTaggedLegHigher.massLinear security input) =
      RootTaggedLocal.rootLift security .attachment 0 input := by
  unfold firstScore
  rw [completeFamily_primary_centered security order horder _ (RootTaggedLegHigher.massLinear_mass security input),
    signedColorCount_rootMass, RootTaggedLocal.rootLift_apply]
  congr 1
  funext color
  exact (RootTaggedLocal.profileDensity_apply security _ color).symm

theorem actual_firstFamily (security order : ℕ) (horder : 1 ≤ order) (input : CycleRootExpansion.Root security → ℝ) :
    firstFamily security order horder (RootTaggedLegHigher.massLinear security input) =
      RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 input := by
  unfold firstFamily
  rw [RootTaggedFamilies.rootFamilyLinear_apply]
  have hscore := actual_firstScore security order horder input
  funext arity
  by_cases hequal : arity = primaryArity order horder
  · subst arity
    simp only [primaryFamily, Pi.single_eq_same]
    apply Subtype.ext
    change (fun colors : Fin 1 → Palette security => fun _ : Fin 0 → SafePalette security =>
      firstScore security order horder (RootTaggedLegHigher.massLinear security input) (colors 0)) =
        (fun colors : Fin 1 → Palette security => fun _ : Fin 0 → SafePalette security =>
          RootTaggedLocal.rootLift security .attachment 0 input (colors 0))
    funext colors centers
    exact congrFun hscore (colors 0)
  · simp only [primaryFamily, Pi.single_eq_of_ne hequal]

theorem actual_completeFamily (security order : ℕ) (horder : 1 ≤ order) (input : CycleRootExpansion.Root security → ℝ) :
    completeFamily security order (RootTaggedLegHigher.massLinear security input) =
      RootUnselectedChannels.legNumeratorLinear security order horder input := by
  rw [complete_eq_first_add_higher security order horder _ (RootTaggedLegHigher.massLinear_mass security input), actual_firstFamily]
  rw [RootUnselectedChannels.legNumeratorLinear, LinearMap.add_apply, RootLegCoefficientLinear.rootHigherLinear_apply]
  rfl

theorem actual_legChannel_physical (security order : ℕ) (horder : 1 ≤ order) (input : CycleRootExpansion.Root security → ℝ) :
    BackgroundEvaluation.evaluation security order (RootUnselectedChannels.legChannel security order horder input) *
      TruncatedOutput.quotientMap order (LegPolynomialEvaluation.legGenerating security) =
      TruncatedOutput.quotientMap order
        (AFT.RepresentedPolynomial.centeredGeneratingLinear (uniformReference security).weight
          (RootTaggedLegHigher.massLinear security input)) := by
  rw [← RootLegReciprocal.positive_image, ← map_mul, RootUnselectedChannels.legChannel_mul_positive,
    ← actual_completeFamily]
  exact completeFamily_image security order _ _ _

end
end CurrentAFT.RootLegFirstCoefficient

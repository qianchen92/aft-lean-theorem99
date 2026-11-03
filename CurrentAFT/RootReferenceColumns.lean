import CurrentAFT.ActualRootProjectionData
import CurrentAFT.RootMassColumns

/-! # Actual unprojected columns and their root reference factors

These identities expose the root mass as a multiplier in canonical
coefficient data. In particular they can be combined with the signed
root-mass program without inverting a root atom.
-/
namespace CurrentAFT.RootReferenceColumns
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference

theorem primary_delta_fiber (security : ℕ) (source : RootPrimaryGroupedChannel.Input security) :
    RootTaggedSelectedChannel.curryLinear security
      (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
        RootMassColumns.fiber (RootPrimaryGroupedChannel.pairEquiv security source.1) (Pi.single source.2 1) := by
  funext roots primaryColor
  change (Pi.single (M := fun _ : RootPrimaryGroupedChannel.Input security => ℝ) source (1 : ℝ))
    ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = _
  have hroot : (RootPrimaryGroupedChannel.pairEquiv security).symm roots = source.1 ↔
      roots = RootPrimaryGroupedChannel.pairEquiv security source.1 := by
    constructor
    · intro h
      simpa using congrArg (RootPrimaryGroupedChannel.pairEquiv security) h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  by_cases hr : roots = RootPrimaryGroupedChannel.pairEquiv security source.1
  · have hpair : ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) = source ↔
        primaryColor = source.2 := by
      constructor
      · exact congrArg Prod.snd
      · intro hp
        exact Prod.ext (hroot.mpr hr) hp
    simp only [RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair]
  · have hpair : ((RootPrimaryGroupedChannel.pairEquiv security).symm roots, primaryColor) ≠ source := by
      intro h
      exact hr (hroot.mp (congrArg Prod.fst h))
    simp only [RootMassColumns.fiber, if_neg hr, Pi.single_eq_of_ne hpair, Pi.zero_apply]

theorem primary_center_fiber (security : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : Palette security → ℝ) :
    RootTaggedSelectedChannel.controlCenterLinear security (RootMassColumns.fiber roots score) =
      RootMassColumns.fiber roots (centerLinear (primaryLaw security) score) := by
  funext other primaryColor
  change centerLinear (primaryLaw security) (RootMassColumns.fiber roots score other) primaryColor = _
  by_cases hequal : other = roots
  · subst other
    simp [RootMassColumns.fiber]
  · simp [RootMassColumns.fiber, hequal, map_zero]

def primaryAt (security order : ℕ) (roots : RootTaggedSelected.RootPair security) (primaryColor : Palette security) :
    LocalCoefficientFamily.Family security order :=
  RootMassColumns.primaryResponseAt security order roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1))

theorem primary_column (security order : ℕ) (source : RootPrimaryGroupedChannel.Input security) :
    RootTaggedSelectedChannel.channel security order
      (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)) =
      ((rootReference security).weight (source.1 0) * (rootReference security).weight (source.1 1)) •
        primaryAt security order (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2 := by
  change RootTaggedSelectedChannel.responseLinear security order
    (RootTaggedSelectedChannel.controlCenterLinear security
      (RootTaggedSelectedChannel.curryLinear security
        (RootPrimaryGroupedChannel.pairLinear security (Pi.single source 1)))) = _
  rw [primary_delta_fiber, primary_center_fiber, RootMassColumns.primary_response_fiber,
    RootMassColumns.primary_roots_weight]
  rfl

def ordinaryFiber (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.Input security → ℝ :=
  fun sample => RootMassColumns.fiber root score sample.1 sample.2

theorem ordinary_center_fiber (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.controlCenterLinear security (ordinaryFiber security root score) =
      ordinaryFiber security root (centerLinear (bodyReference security) score) := by
  funext sample
  change centerLinear (bodyReference security) (RootMassColumns.fiber root score sample.1) sample.2 = _
  by_cases hequal : sample.1 = root
  · simp [RootMassColumns.fiber, ordinaryFiber, hequal]
  · simp [RootMassColumns.fiber, ordinaryFiber, hequal, map_zero]

def ordinaryDensityAt (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    Palette security → ℝ :=
  PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security (RootMassColumns.ordinaryMassAt security root
      (centerLinear (bodyReference security) score)))

theorem ordinaryDensityAt_mean (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    (primaryLaw security).expectation (ordinaryDensityAt security root score) = 0 := by
  rw [ordinaryDensityAt, PrimaryTensorInverse.densityInverse_mean, RootTaggedLocal.profileDensity_mean]
  have h := SelectedOrdinaryRoot.push_test (bodyReference security) (SelectedOrdinaryRoot.rootEmbedding security root)
    (centerLinear (bodyReference security) score) (fun _ => 1)
  simp only [mul_one] at h
  change (∑ color, RootMassColumns.ordinaryMassAt security root (centerLinear (bodyReference security) score) color) = _ at h
  rw [h, center_mean, mul_zero]

theorem ordinary_density_fiber (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.densityLinear security (ordinaryFiber security root score) =
      (rootReference security).weight root • ordinaryDensityAt security root score := by
  change PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security
      (SelectedOrdinaryRoot.rawMassLinear security
        (SelectedOrdinaryRoot.controlCenterLinear security (ordinaryFiber security root score)))) = _
  rw [ordinary_center_fiber]
  unfold ordinaryFiber
  rw [RootMassColumns.ordinary_mass_fiber, map_smul, map_smul]
  rfl

def ordinaryAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) : LocalCoefficientFamily.Family security order :=
  LocalRaisingLinear.primaryEmbeddingLinear security order horder
    ⟨ordinaryDensityAt security root score, ordinaryDensityAt_mean security root score⟩ *
      OrdinaryRaising.positiveInverse security order horder

theorem ordinary_channel_fiber (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.channel security order horder (ordinaryFiber security root score) =
      (rootReference security).weight root • ordinaryAt security order horder root score := by
  have hcentered : SelectedOrdinaryRoot.centeredDensityLinear security (ordinaryFiber security root score) =
      (rootReference security).weight root •
        (⟨ordinaryDensityAt security root score, ordinaryDensityAt_mean security root score⟩ :
          LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact ordinary_density_fiber security root score
  change LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (SelectedOrdinaryRoot.centeredDensityLinear security (ordinaryFiber security root score)) * _ = _
  rw [hcentered, map_smul, smul_mul_assoc]
  rfl

theorem ordinary_mean_fiber (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    SelectedOrdinaryMean.rootMean security (ordinaryFiber security root score) =
      (rootReference security).weight root • score := by
  funext centerColor
  simp [SelectedOrdinaryMean.rootMean, ordinaryFiber, RootMassColumns.fiber, FiniteDist.expectation, ite_apply]

theorem ordinary_constant_expansion (security : ℕ) (score : SafePalette security → ℝ) :
    SelectedOrdinaryMean.constantRoot security score = ∑ root, ordinaryFiber security root score := by
  funext sample
  simp [SelectedOrdinaryMean.constantRoot, ordinaryFiber, RootMassColumns.fiber, ite_apply]

theorem ordinary_constant_channel (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    SelectedOrdinaryRoot.channel security order horder (SelectedOrdinaryMean.constantRoot security score) =
      ∑ root, (rootReference security).weight root • ordinaryAt security order horder root score := by
  rw [ordinary_constant_expansion, map_sum]
  simp only [ordinary_channel_fiber]

def hybridAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) : LocalCoefficientFamily.Family security order :=
  SelectedOrdinaryHybrid.independentChannel security order horder score +
    ordinaryAt security order horder root score -
      ∑ other, (rootReference security).weight other • ordinaryAt security order horder other score

/-- The retained body leading term and the root-centered primary term
have one common root-reference factor, including at zero atoms. -/
theorem hybrid_column_fiber (security order : ℕ) (horder : 1 ≤ order) (root : Root security)
    (score : SafePalette security → ℝ) :
    SelectedOrdinaryHybrid.channel security order horder (ordinaryFiber security root score) =
      (rootReference security).weight root • hybridAt security order horder root score := by
  have hcenter : SelectedOrdinaryMean.rootCenter security (ordinaryFiber security root score) =
      ordinaryFiber security root score - SelectedOrdinaryMean.constantRoot security
        ((rootReference security).weight root • score) := by
    change ordinaryFiber security root score - SelectedOrdinaryMean.constantRoot security
      (SelectedOrdinaryMean.rootMean security (ordinaryFiber security root score)) = _
    rw [ordinary_mean_fiber]
  rw [SelectedOrdinaryHybrid.channel_apply, hcenter, ordinary_mean_fiber, map_smul]
  rw [map_sub, map_smul, map_smul, ordinary_channel_fiber, ordinary_constant_channel]
  unfold hybridAt
  rw [smul_sub, smul_add]
  abel

def singletonDensityAt (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    Palette security → ℝ :=
  PrimaryTensorInverse.densityInverse security
    (RootTaggedLocal.profileDensity security (RootTaggedLocal.deviationProfile security role queue root))

theorem singletonDensityAt_mean (security : ℕ) (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    (primaryLaw security).expectation (singletonDensityAt security role queue root) = 0 := by
  rw [singletonDensityAt, PrimaryTensorInverse.densityInverse_mean, RootTaggedLocal.profileDensity_mean,
    RootTaggedLocal.deviationProfile_mass, mul_zero]

def singletonFirstAt (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
    (singletonDensityAt security role queue root) (singletonDensityAt_mean security role queue root)

theorem singleton_first_column (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonFirstAt security order horder role queue root := by
  have hlift : RootTaggedLocal.rootLift security role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonDensityAt security role queue root := by
    rw [RootTaggedLocal.rootLift_apply, RootMassColumns.singleton_mass_column, map_smul, map_smul]
    rfl
  have hs : (⟨RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : LocalRaisingLinear.centeredScores security) =
      (rootReference security).weight root •
        (⟨singletonDensityAt security role queue root, singletonDensityAt_mean security role queue root⟩ :
          LocalRaisingLinear.centeredScores security) := by
    apply Subtype.ext
    exact hlift
  rw [RootTaggedFamilies.rootFamilyLinear_apply]
  change LocalRaisingLinear.primaryEmbeddingLinear security order horder
    (⟨RootTaggedLocal.rootLift security role queue (Pi.single root 1),
      RootTaggedLocal.rootLift_mean security role queue (Pi.single root 1)⟩ : LocalRaisingLinear.centeredScores security) = _
  rw [hs, map_smul]
  rfl

def singletonAt (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  singletonFirstAt security order horder role queue root * RootMeanPrimary.positiveInverse security order horder role queue

theorem singleton_column (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (root : Root security) :
    RootUnselectedChannels.singletonChannel security order horder role queue (Pi.single root 1) =
      (rootReference security).weight root • singletonAt security order horder role queue root := by
  change RootTaggedFamilies.rootFamilyLinear security order horder role queue (Pi.single root 1) * _ = _
  rw [singleton_first_column, smul_mul_assoc]
  rfl

def legHigherAt (security order : ℕ) (root : Root security) : LocalCoefficientFamily.Family security order :=
  RootLegCoefficientLinear.higherFamilyLinear security order
    ((ActualBlockFock.primaryLawAt security root.val).weight - RootTaggedLegHigher.rawMassLinear security (fun _ => 1))

theorem leg_higher_column (security order : ℕ) (root : Root security) :
    RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1) =
      (rootReference security).weight root • legHigherAt security order root := by
  change RootLegCoefficientLinear.higherFamilyLinear security order
    (RootTaggedLegHigher.massLinear security (Pi.single root 1)) = _
  rw [RootMassColumns.leg_mass_column, map_smul]
  rfl

def legAt (security order : ℕ) (horder : 1 ≤ order) (root : Root security) : LocalCoefficientFamily.Family security order :=
  (singletonFirstAt security order horder .attachment 0 root + legHigherAt security order root) *
    RootLegReciprocal.reciprocal security order

theorem leg_column (security order : ℕ) (horder : 1 ≤ order) (root : Root security) :
    RootUnselectedChannels.legChannel security order horder (Pi.single root 1) =
      (rootReference security).weight root • legAt security order horder root := by
  change (RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (Pi.single root 1) +
    RootLegCoefficientLinear.rootHigherLinear security order (Pi.single root 1)) * _ = _
  rw [singleton_first_column, leg_higher_column, ← smul_add, smul_mul_assoc]
  rfl

def unselectedAt (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (root : Root security) : LocalCoefficientFamily.Family security order :=
  match block with
  | .inl _ => legAt security order horder root
  | .inr (.inl _) => singletonAt security order horder .free 0 root
  | .inr (.inr _) => singletonAt security order horder .queue queue root

theorem unselected_column (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (root : Root security) :
    RootUnselectedBlockChannel.channel security order horder queue block (Pi.single root 1) =
      (rootReference security).weight root • unselectedAt security order horder queue block root := by
  rcases block with leg | single
  · exact leg_column security order horder root
  · rcases single with center | point
    · exact singleton_column security order horder .free 0 root
    · exact singleton_column security order horder .queue queue root

theorem ordinary_delta_fiber (security : ℕ) (source : RootOrdinaryGroupedChannel.Input security) :
    RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1) =
      ordinaryFiber security (source.1 0) (Pi.single source.2 1) := by
  funext sample
  change (Pi.single (M := fun _ : RootOrdinaryGroupedChannel.Input security => ℝ) source 1)
    ((fun _ => sample.1), sample.2) = _
  have hroots : (fun _ : Fin 1 => sample.1) = source.1 ↔ sample.1 = source.1 0 := by
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext index
      rw [Fin.eq_zero index]
      exact h
  have hpair : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔
      sample.1 = source.1 0 ∧ sample.2 = source.2 := by
    rw [Prod.ext_iff, hroots]
  by_cases hr : sample.1 = source.1 0
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) = source ↔ sample.2 = source.2 := by
      constructor
      · intro h
        exact (hpair.mp h).2
      · intro h
        exact hpair.mpr ⟨hr, h⟩
    simp only [ordinaryFiber, RootMassColumns.fiber, if_pos hr, Pi.single_apply, hpair']
  · have hpair' : ((fun _ : Fin 1 => sample.1), sample.2) ≠ source := fun h => hr (hpair.mp h).1
    simp only [ordinaryFiber, RootMassColumns.fiber, if_neg hr, Pi.zero_apply, Pi.single_eq_of_ne hpair']

theorem ordinary_column (security order : ℕ) (horder : 1 ≤ order) (source : RootOrdinaryGroupedChannel.Input security) :
    SelectedOrdinaryHybrid.channel security order horder
      (RootOrdinaryGroupedChannel.toRaw security (Pi.single source 1)) =
      (rootReference security).weight (source.1 0) •
        hybridAt security order horder (source.1 0) (Pi.single source.2 1) := by
  rw [ordinary_delta_fiber]
  exact hybrid_column_fiber security order horder _ _

theorem unselected_extract_delta (security : ℕ) (source : RootUnselectedGrouped.Input security) :
    RootUnselectedGrouped.extractLinear security (Pi.single source 1) = Pi.single (source.1 0) 1 := by
  funext root
  change (Pi.single (M := fun _ : RootUnselectedGrouped.Input security => ℝ) source 1)
    ((RootUnselectedGrouped.inputEquiv security).symm root) = _
  have hequal : (RootUnselectedGrouped.inputEquiv security).symm root = source ↔ root = source.1 0 := by
    constructor
    · intro h
      have h' := congrArg (RootUnselectedGrouped.inputEquiv security) h
      simpa using h'
    · intro h
      change _ = _
      rw [show source.1 0 = RootUnselectedGrouped.inputEquiv security source from rfl] at h
      rw [h, Equiv.symm_apply_apply]
  simp only [Pi.single_apply, hequal]

theorem unselected_group_column (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : ActualBlockFock.BlockIndex security) (source : RootUnselectedGrouped.Input security) :
    RootUnselectedGrouped.channel security order horder queue block (Pi.single source 1) =
      (rootReference security).weight (source.1 0) • unselectedAt security order horder queue block (source.1 0) := by
  change RootUnselectedBlockChannel.channel security order horder queue block
    (RootUnselectedGrouped.extractLinear security (Pi.single source 1)) = _
  rw [unselected_extract_delta]
  exact unselected_column security order horder queue block _

def reducedColumn {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security)) :
    (group : PairedRootPlacement.ActiveGroup selection tagged) →
      ActualRootGroupedChannel.Input selection tagged group → LocalCoefficientFamily.Family security order
  | .inl (.inl _), source => primaryAt security order (RootPrimaryGroupedChannel.pairEquiv security source.1) source.2
  | .inl (.inr _), source => hybridAt security order horder (source.1 (0 : Fin 1)) (Pi.single source.2 1)
  | .inr index, source => unselectedAt security order horder queue index.val.val (source.1 (0 : Fin 1))

/-- Every local root slot contributes exactly one reference multiplier.
This is the coefficient-level cancellation needed by sparse root mass evaluation. -/
theorem unprojected_column {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : TaggedSelection.Selection security r s) (tagged : Finset (ActualBlockFock.BlockIndex security))
    (group : PairedRootPlacement.ActiveGroup selection tagged)
    (source : ActualRootGroupedChannel.Input selection tagged group) :
    ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group (Pi.single source 1) =
      (∏ slot, (rootReference security).weight (source.1 slot)) •
        reducedColumn order horder queue selection tagged group source := by
  rcases group with (primary | ordinary) | kept
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 2)) * (rootReference security).weight (source.1 (1 : Fin 2)) := by
      calc
        _ = ∏ slot : Fin 2, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_two _
    rw [hprod]
    exact primary_column security order source
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    exact ordinary_column security order horder source
  · have hprod : (∏ slot, (rootReference security).weight (source.1 slot)) =
        (rootReference security).weight (source.1 (0 : Fin 1)) := by
      calc
        _ = ∏ slot : Fin 1, (rootReference security).weight (source.1 slot) :=
          Finset.prod_congr (by
            ext index
            have hi : (index : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance index 0
            subst index
            simp) (fun _ _ => rfl)
        _ = _ := Fin.prod_univ_one _
    rw [hprod]
    have hdelta : (Pi.single (M := fun _ : ActualRootGroupedChannel.Input selection tagged (.inr kept) => ℝ) source 1) =
        (Pi.single (M := fun _ : RootUnselectedGrouped.Input security => ℝ) source 1) := by
      funext word
      by_cases hequal : word = source <;> simp only [Pi.single_apply, hequal, if_true, if_false]
    rw [hdelta]
    exact unselected_group_column security order horder queue kept.val.val source

end
end CurrentAFT.RootReferenceColumns

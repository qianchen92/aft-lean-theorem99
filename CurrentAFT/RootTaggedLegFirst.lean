import CurrentAFT.RootTaggedFamilies

/-! The root-tagged first coefficient of the full actual unselected leg. -/

namespace CurrentAFT.RootTaggedLegFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF UniformBodyProfiles HistogramMean
  CycleRootExpansion RootTaggedLocal RootTaggedFamilies BackgroundEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _

def legHistogram (security : ℕ) (root : Root security) (color : ActualControls.Palette security) : ℝ :=
  ∑ coordinate : Fin 3, ((primaryLawAt security root.val).map (fun word => word coordinate)).weight color

def meanLegHistogram (security : ℕ) (color : ActualControls.Palette security) : ℝ :=
  (rootReference security).expectation (fun root => legHistogram security root color)

theorem legHistogram_formula (security : ℕ) (root : Root security) (color : ActualControls.Palette security) :
    legHistogram security root color =
      offBodyMean security color + (shiftedLaw security .attachment 0 root).weight color :=
  primary_histogram security root.val color

theorem meanLegHistogram_formula (security : ℕ) (color : ActualControls.Palette security) :
    meanLegHistogram security color = offBodyMean security color + (meanLaw security .attachment 0).weight color := by
  simp only [meanLegHistogram, legHistogram_formula, meanLaw, FiniteDist.mix_weight,
    FiniteDist.expectation, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem centered_legHistogram (security : ℕ) (root : Root security) (color : ActualControls.Palette security) :
    legHistogram security root color - meanLegHistogram security color =
      deviationProfile security .attachment 0 root color := by
  rw [legHistogram_formula, meanLegHistogram_formula]
  simp only [deviationProfile, Pi.sub_apply]
  ring

def legFirstMass (security : ℕ) : (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) where
  toFun input := fun color => ∑ root, (rootReference security).weight root * input root *
    (legHistogram security root color - meanLegHistogram security color)
  map_add' first second := by
    funext color
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

theorem legFirstMass_eq_rootMass (security : ℕ) : legFirstMass security = rootMass security .attachment 0 := by
  apply LinearMap.ext
  intro input
  funext color
  simp only [legFirstMass, rootMass, LinearMap.coe_mk, AddHom.coe_mk, centered_legHistogram]

theorem legFirstMass_physical (security : ℕ) (input : Root security → ℝ)
    (hcentered : (rootReference security).expectation input = 0) (color : ActualControls.Palette security) :
    legFirstMass security input color =
      ∑ root, (rootReference security).weight root * input root * legHistogram security root color := by
  change (∑ root, (rootReference security).weight root * input root *
    (legHistogram security root color - meanLegHistogram security color)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ - (rootReference security).expectation input * _ = _
  rw [hcentered, zero_mul, sub_zero]

theorem legFirstMass_energy (security : ℕ) (input : Root security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (legFirstMass security input) ≤
      8 * deviation security ^ 2 * (rootReference security).l2Sq input := by
  rw [legFirstMass_eq_rootMass]
  exact rootMass_energy security .attachment 0 input

theorem legFirstFamily_image (security order : ℕ) (horder : 1 ≤ order) (input : Root security → ℝ) :
    evaluation security order (rootFamilyLinear security order horder .attachment 0 input) =
      TruncatedOutput.quotientMap order (AFT.RepresentedPolynomial.profileForm (legFirstMass security input)) := by
  rw [legFirstMass_eq_rootMass]
  exact rootFamily_image security order horder .attachment 0 input

end

end CurrentAFT.RootTaggedLegFirst

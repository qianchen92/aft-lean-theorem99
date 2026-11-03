import AFT.RootSubsetMarginal
import AFT.CanonicalVariance
import AFT.ActualRootResponse

/-! # Arbitrary actual root-set energies, with exact prefix identification -/
namespace AFT.RootSlice
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootSubsetNormFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Source Slot : Type*} [Fintype Source] [Fintype Slot]
local instance rootSubsetNormSlotDecEq : DecidableEq Slot := Classical.decEq _
local instance rootSubsetNormSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- Restricting an actual signed coefficient to its selected root arguments
commutes with taking the canonical coefficient of the genuine marginal. -/
theorem densityComponent_subsetPrefix (reference : FiniteDist Source) (law : FiniteDist (Slot → Source))
    (selected : Finset Slot) (word : Slot → Source) :
    Hoeffding.densityComponent (fun _ : Slot => reference) law.weight selected word =
      Hoeffding.densityComponent (fun _ : Fin selected.card => reference)
        (law.map (subsetPrefix selected)).weight Finset.univ (subsetPrefix selected word) := by
  have hh := law.expectation_map (subsetPrefix selected)
    (fun input => ∏ index : Fin selected.card,
      Hoeffding.centeredAtom reference (input index) (subsetPrefix selected word index))
  change (∑ input,(law.map (subsetPrefix selected)).weight input *
      ∏ index : Fin selected.card,Hoeffding.centeredAtom reference (input index) (subsetPrefix selected word index)) = _ at hh
  unfold Hoeffding.densityComponent
  rw [hh]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  simp only [subsetPrefix_apply,Function.comp_apply]
  have he := (subsetEnumeration selected).prod_comp
    (fun index : selected => Hoeffding.centeredAtom reference (input index) (word index))
  exact (Finset.prod_coe_sort selected _).symm.trans he.symm

/-- The independent ambient coordinates integrate out exactly. -/
theorem independent_subsetPrefix_expectation (reference : FiniteDist Source)
    (selected : Finset Slot) (function : (Fin selected.card → Source) → ℝ) :
    (FiniteDist.independent (fun _ : Slot => reference)).expectation
      (fun word => function (subsetPrefix selected word)) =
      (FiniteDist.independent (fun _ : Fin selected.card => reference)).expectation function := by
  have hfirst := LocalTensors.independent_restriction_expectation (fun _ : Slot => reference) selected
    (fun chosen => function (fun index => chosen (subsetEnumeration selected index)))
  simp only [← subsetPrefix_apply] at hfirst
  have hsecond := CanonicalMoments.independent_equiv_expectation (subsetEnumeration selected)
    reference function
  apply hfirst.trans
  convert hsecond using 1
  unfold FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- Exact equality of ambient subset energy and the fully canonical
coefficient of the selected marginal. No exchangeability bound is assumed. -/
theorem densityComponent_subsetPrefix_l2Sq (reference : FiniteDist Source) (law : FiniteDist (Slot → Source))
    (selected : Finset Slot) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (Hoeffding.densityComponent (fun _ : Slot => reference) law.weight selected) =
      (FiniteDist.independent (fun _ : Fin selected.card => reference)).l2Sq
        (Hoeffding.densityComponent (fun _ : Fin selected.card => reference)
          (law.map (subsetPrefix selected)).weight Finset.univ) := by
  unfold FiniteDist.l2Sq
  simp_rw [densityComponent_subsetPrefix reference law selected]
  exact independent_subsetPrefix_expectation reference selected
    (fun word => Hoeffding.densityComponent (fun _ : Fin selected.card => reference)
      (law.map (subsetPrefix selected)).weight Finset.univ word ^ 2)

/-- With positive references, the density projection is the same concrete
coefficient; normalization cancels pointwise inside the finite sum. -/
theorem densityComponent_full_projection (reference : FiniteDist Source)
    (hp : ∀ source,0<reference.weight source) (law : FiniteDist (Slot → Source)) :
    Hoeffding.densityComponent (fun _ : Slot => reference) law.weight Finset.univ =
      Hoeffding.projection (fun _ : Slot => reference) Finset.univ
        (fun word => law.weight word/(FiniteDist.independent (fun _ : Slot => reference)).weight word) := by
  have he : (fun word => (FiniteDist.independent (fun _ : Slot => reference)).weight word*
      (law.weight word/(FiniteDist.independent (fun _ : Slot => reference)).weight word))=law.weight := by
    funext word
    exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos fun slot _ => hp (word slot)))
  change _=Hoeffding.densityComponent _ _ Finset.univ
  rw [he]

end
end AFT.RootSlice

namespace AFT.V7Calibration
open GaussianSource RootSlice Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootSubsetNormFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Every actual root subset has exactly the prefix ANOVA energy already
estimated analytically. The full conditioned law is identified first. -/
theorem actualRootResponseCoefficient_l2Sq (n : ℕ) (selected : Finset (Fin (Parameters.bodies n))) :
    (actualIndependentRoots n).l2Sq (actualRootResponseCoefficient n selected)=
      v7RootKernelSq selected.card n := by
  change (FiniteDist.independent (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)).l2Sq
    (Hoeffding.densityComponent (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
      (actualRootConditionLaw n).weight selected)=_
  rw [densityComponent_subsetPrefix_l2Sq]
  have hprefix : (actualRootConditionLaw n).map (subsetPrefix selected)=
      prefixLaw (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun root => (root : ℤ))
        selected.card (Parameters.bodies n-selected.card)
        (window_root_probability_positive (v7RootWidth n) (v7RootCutoff n)
          (selected.card+(Parameters.bodies n-selected.card))) := by
    have hh := law_subsetPrefix (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun root => (root : ℤ))
      selected (window_root_probability_positive (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n))
      (by simpa only [Fintype.card_fin] using (window_root_probability_positive (v7RootWidth n) (v7RootCutoff n)
            (selected.card+(Parameters.bodies n-selected.card))))
    simpa only [Fintype.card_fin] using hh
  rw [hprefix,densityComponent_full_projection _ (bodyRootReference_positive n)]
  have hcard : selected.card+(Parameters.bodies n-selected.card)=Parameters.bodies n := by
    have hh := selected.card_le_univ
    simp only [Fintype.card_fin] at hh
    omega
  have href (hn : 0<selected.card+(Parameters.bodies n-selected.card)) :
      rootMarginal (v7RootWidth n) (v7RootCutoff n)
        (selected.card+(Parameters.bodies n-selected.card)) hn=bodyRootReference n := by
    simp only [hcard,bodyRootReference]
  dsimp only [v7RootKernelSq]
  unfold rootPrefixDensity
  simp only [href]

/-- The analytic half-order estimate now applies uniformly to every
literal source set of a fixed cardinality, without a prefix assumption. -/
theorem actualRootResponseCoefficient_decay (order : ℕ) (horder : 0<order) :
    ∀ᶠ n in atTop, ∀ selected : Finset (Fin (Parameters.bodies n)),selected.card=order →
      (actualIndependentRoots n).l2Sq (actualRootResponseCoefficient n selected) ≤
        rootANOVAConstant order/(Parameters.bodies n : ℝ)^(2*((order+1)/2)) := by
  filter_upwards [v7RootKernelSq_decay order horder] with n hbound selected hselected
  rw [actualRootResponseCoefficient_l2Sq,hselected]
  exact hbound

end
end AFT.V7Calibration

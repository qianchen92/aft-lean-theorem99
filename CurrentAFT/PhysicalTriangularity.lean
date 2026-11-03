import CurrentAFT.PhysicalSynthesis
import AFT.TensorMatrixCanonical

/-!
# Centering and triangularity of each physical distinct-group summand

The paired channel preserves conditional centering of an arbitrary joint
kernel in every primary slot. Ordinary-body slots remain centered as well.
Each selected group is distinct. A test omitting any one of those groups
therefore integrates to zero, before averaging over selections. This is the
triangularity mechanism, independent of any subsequent response norm bound.
-/

namespace CurrentAFT.PhysicalTriangularity

open AFT DiffuseProfiles ProposalPrimary ControlCoordinates PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pairedMatrix (security : ℕ) (color : Palette security) (group : Group security) : ℝ :=
  pairedChannel security (Pi.single color 1) group

theorem pairedMatrix_mean (security : ℕ) (color : Palette security) :
    (groupLaw security).expectation (pairedMatrix security color) =
      (1 - activation security) * (primaryLaw security).weight color := by
  change (groupLaw security).expectation (pairedChannel security (Pi.single color 1)) = _
  rw [pairedChannel_mean]
  simp [FiniteDist.expectation, Pi.single_apply]

theorem pairedKernel_formula (security r s : ℕ)
    (kernel : DensityKernel (Primary := Palette security)
      (Body := ActualControls.SafePalette security) r s)
    (groups : Fin r → Group security) (centers : Fin s → ActualControls.SafePalette security) :
    pairedKernel security r s kernel groups centers =
      MixedKernel.matrixApply (fun _ => pairedMatrix security) (fun colors => kernel colors centers) groups := by
  exact TensorChannel.apply_formula_instance r (fun _ => pairedChannel security)
    (fun colors => kernel colors centers) groups

theorem pairedKernel_primary_canonical (security r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (centers : Fin s → ActualControls.SafePalette security) :
    Hoeffding.Canonical (fun _ : Fin r => groupLaw security) Finset.univ
      (fun groups => pairedKernel security r s kernel.val groups centers) := by
  have hinput : Hoeffding.Canonical (fun _ : Fin r => primaryLaw security) Finset.univ
      (fun colors => kernel.val colors centers) := by
    constructor
    · intro first second hequal
      have heq : first = second := funext (fun index => hequal index (Finset.mem_univ _))
      rw [heq]
    · intro index _ colors
      exact kernel.property.1 index colors centers
  have houtput := MixedKernel.matrixApply_canonical (fun _ : Fin r => primaryLaw security)
    (fun _ => groupLaw security) (fun _ => pairedMatrix security) (fun _ => 1 - activation security)
    (fun _ => pairedMatrix_mean security) (fun colors => kernel.val colors centers) hinput
  have heq : (fun groups => pairedKernel security r s kernel.val groups centers) =
      MixedKernel.matrixApply (fun _ : Fin r => pairedMatrix security) (fun colors => kernel.val colors centers) := by
    funext groups
    exact pairedKernel_formula security r s kernel.val groups centers
  rw [heq]
  exact houtput

theorem pairedKernel_body_centered (security r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (index : Fin s) (groups : Fin r → Group security)
    (centers : Fin s → ActualControls.SafePalette security) :
    (∑ center, (ActualControls.bodyReference security).weight center *
      pairedKernel security r s kernel.val groups (Function.update centers index center)) = 0 := by
  have hmove := TensorChannel.apply_expectation (ActualControls.bodyReference security) r
    (fun _ => pairedChannel security)
    (fun center colors => kernel.val colors (Function.update centers index center)) groups
  have hzero : (fun colors => (ActualControls.bodyReference security).expectation
      (fun center => kernel.val colors (Function.update centers index center))) = 0 := by
    funext colors
    exact kernel.property.2.1 index colors centers
  rw [hzero] at hmove
  have hmapzero : TensorChannel.apply r (fun _ => pairedChannel security) 0 groups = 0 :=
    congrFun (map_zero (TensorChannel.applyLinear r (fun _ => pairedChannel security))) groups
  rw [hmapzero] at hmove
  exact hmove.symm

theorem pairedKernel_body_canonical (security r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (groups : Fin r → Group security) :
    Hoeffding.Canonical (fun _ : Fin s => ActualControls.bodyReference security) Finset.univ
      (pairedKernel security r s kernel.val groups) := by
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ _))
    rw [heq]
  · intro index _ centers
    exact pairedKernel_body_centered security r s kernel index groups centers

theorem selected_primary_omission (security r s primaryPool : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (selection : Fin r ↪ Fin primaryPool) (centers : Fin s → ActualControls.SafePalette security)
    (scope : Finset (Fin primaryPool)) (omitted : Fin r) (homitted : selection omitted ∉ scope)
    (test : (Fin primaryPool → Group security) → ℝ) (htest : Hoeffding.DependsOn scope test) :
    (FiniteDist.independent (fun _ : Fin primaryPool => groupLaw security)).expectation
      (fun groups => pairedKernel security r s kernel.val (groups ∘ selection) centers * test groups) = 0 := by
  have hcanonical := CanonicalMoments.placedKernel_canonical (groupLaw security)
    (fun groups => pairedKernel security r s kernel.val groups centers)
    (pairedKernel_primary_canonical security r s kernel centers) selection
  exact Hoeffding.orthogonal_of_centered (fun _ : Fin primaryPool => groupLaw security) scope
    (selection omitted) homitted _ test
    (hcanonical.2 (selection omitted) (Finset.mem_map.mpr ⟨omitted, Finset.mem_univ _, rfl⟩)) htest

theorem selected_body_omission (security r s bodyPool : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (selection : Fin s ↪ Fin bodyPool) (groups : Fin r → Group security)
    (scope : Finset (Fin bodyPool)) (omitted : Fin s) (homitted : selection omitted ∉ scope)
    (test : (Fin bodyPool → ActualControls.SafePalette security) → ℝ)
    (htest : Hoeffding.DependsOn scope test) :
    (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security)).expectation
      (fun centers => pairedKernel security r s kernel.val groups (centers ∘ selection) * test centers) = 0 := by
  have hcanonical := CanonicalMoments.placedKernel_canonical (ActualControls.bodyReference security)
    (pairedKernel security r s kernel.val groups)
    (pairedKernel_body_canonical security r s kernel groups) selection
  exact Hoeffding.orthogonal_of_centered (fun _ : Fin bodyPool => ActualControls.bodyReference security) scope
    (selection omitted) homitted _ test
    (hcanonical.2 (selection omitted) (Finset.mem_map.mpr ⟨omitted, Finset.mem_univ _, rfl⟩)) htest

/-- A low-support test omits at least one group in each actual selection.
Its two scopes may be chosen after fixing any hidden-source values. -/
theorem selectedKernel_low_support (security r s primaryPool bodyPool : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (primarySelection : Fin r ↪ Fin primaryPool) (bodySelection : Fin s ↪ Fin bodyPool)
    (primaryScope : Finset (Fin primaryPool)) (bodyScope : Finset (Fin bodyPool))
    (hdegree : primaryScope.card + bodyScope.card < r + s)
    (test : (Fin primaryPool → Group security) →
      (Fin bodyPool → ActualControls.SafePalette security) → ℝ)
    (hprimary : ∀ centers, Hoeffding.DependsOn primaryScope (fun groups => test groups centers))
    (hbody : ∀ groups, Hoeffding.DependsOn bodyScope (test groups)) :
    kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (fun groups centers => pairedKernel security r s kernel.val
        (groups ∘ primarySelection) (centers ∘ bodySelection) * test groups centers) = 0 := by
  by_cases hmissing : ∃ omitted, primarySelection omitted ∉ primaryScope
  · obtain ⟨omitted, homitted⟩ := hmissing
    rw [kernelMean_iterated_reverse]
    have hzero (centers : Fin bodyPool → ActualControls.SafePalette security) :
        (FiniteDist.independent (fun _ : Fin primaryPool => groupLaw security)).expectation
          (fun groups => pairedKernel security r s kernel.val
            (groups ∘ primarySelection) (centers ∘ bodySelection) * test groups centers) = 0 :=
      selected_primary_omission security r s primaryPool kernel primarySelection
        (centers ∘ bodySelection) primaryScope omitted homitted _ (hprimary centers)
    simp_rw [hzero]
    exact FiniteDist.expectation_const _ 0
  · have hprimaryCard : r ≤ primaryScope.card := by
      have hsubset : Finset.univ.map primarySelection ⊆ primaryScope := by
        intro index hindex
        obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hindex
        by_contra hnot
        exact hmissing ⟨slot, hnot⟩
      simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset
    have hmissingBody : ∃ omitted, bodySelection omitted ∉ bodyScope := by
      by_contra hnone
      have hsubset : Finset.univ.map bodySelection ⊆ bodyScope := by
        intro index hindex
        obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hindex
        by_contra hnot
        exact hnone ⟨slot, hnot⟩
      have hbodyCard : s ≤ bodyScope.card := by
        simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset
      omega
    obtain ⟨omitted, homitted⟩ := hmissingBody
    rw [kernelMean_iterated]
    have hzero (groups : Fin primaryPool → Group security) :
        (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security)).expectation
          (fun centers => pairedKernel security r s kernel.val
            (groups ∘ primarySelection) (centers ∘ bodySelection) * test groups centers) = 0 :=
      selected_body_omission security r s bodyPool kernel bodySelection
        (groups ∘ primarySelection) bodyScope omitted homitted _ (hbody groups)
    simp_rw [hzero]
    exact FiniteDist.expectation_const _ 0

/-- Only after proving the cancellation for every distinct selection do
we average over the two independent selection sets. -/
theorem twoPool_low_support (security r s primaryPool bodyPool : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s)
    (primaryScope : Finset (Fin primaryPool)) (bodyScope : Finset (Fin bodyPool))
    (hdegree : primaryScope.card + bodyScope.card < r + s)
    (test : (Fin primaryPool → Group security) →
      (Fin bodyPool → ActualControls.SafePalette security) → ℝ)
    (hprimary : ∀ centers, Hoeffding.DependsOn primaryScope (fun groups => test groups centers))
    (hbody : ∀ groups, Hoeffding.DependsOn bodyScope (test groups)) :
    kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (fun groups centers => twoPoolUStatistic primaryPool bodyPool
        (pairedKernel security r s kernel.val) groups centers * test groups centers) = 0 := by
  let law := (FiniteDist.independent (fun _ : Fin primaryPool => groupLaw security)).prod
    (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security))
  have hterm (selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool)) :
      law.expectation (fun inputs => pairedKernel security r s kernel.val
        (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2) * test inputs.1 inputs.2) = 0 :=
    selectedKernel_low_support security r s primaryPool bodyPool kernel selection.1 selection.2
      primaryScope bodyScope hdegree test hprimary hbody
  have hformula (groups : Fin primaryPool → Group security)
      (centers : Fin bodyPool → ActualControls.SafePalette security) :
      twoPoolUStatistic primaryPool bodyPool (pairedKernel security r s kernel.val) groups centers * test groups centers =
        (∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
          pairedKernel security r s kernel.val (groups ∘ selection.1) (centers ∘ selection.2) * test groups centers) /
            ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ)) := by
    unfold twoPoolUStatistic
    rw [← Finset.sum_mul]
    ring
  change law.expectation _ = 0
  simp_rw [hformula]
  have hdivide (function : ((Fin primaryPool → Group security) ×
      (Fin bodyPool → ActualControls.SafePalette security)) → ℝ) (denominator : ℝ) :
      law.expectation (fun inputs => function inputs / denominator) =
        law.expectation function / denominator := by
    simp only [FiniteDist.expectation, mul_div_assoc, Finset.sum_div]
  rw [hdivide]
  have hsum : law.expectation (fun inputs => ∑ selection :
      (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool), pairedKernel security r s kernel.val
        (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2) * test inputs.1 inputs.2) =
      ∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
        law.expectation (fun inputs => pairedKernel security r s kernel.val
          (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2) * test inputs.1 inputs.2) := by
    unfold FiniteDist.expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp only [hterm, Finset.sum_const_zero, zero_div]

end

end CurrentAFT.PhysicalTriangularity

import CurrentAFT.PhysicalTriangularity
import CurrentAFT.ControlNorm
import AFT.IndependentConditioning
import AFT.FiniteJointExpectation
import AFT.TwoPoolCanonical

/-!
# Actual safe control groups for finite-atom moment bounds

The compensator alphabet contains only the safe colors. No positive lower
bound is asserted at forbidden center atoms. Ordinary-body coordinates may
be augmented by an independent unused primary; this gives the same positive
group alphabet in the two independent pools without changing any weight.
-/

namespace CurrentAFT.SafeControlGroups

open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw centerLaw

private theorem independent_sum_expectation {Left Right Color : Type*}
    [Fintype Left] [Fintype Right] [Fintype Color]
    (first : Left → FiniteDist Color) (second : Right → FiniteDist Color)
    (test : (Left ⊕ Right → Color) → ℝ) :
    (FiniteDist.independent (Sum.elim first second)).expectation test =
      (FiniteDist.independent first).expectation (fun left =>
        (FiniteDist.independent second).expectation (fun right => test (Sum.elim left right))) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring

abbrev SafeGroup (security : ℕ) := Palette security × ActualControls.SafePalette security

def reference (security : ℕ) : FiniteDist (SafeGroup security) :=
  (primaryLaw security).prod (ActualControls.bodyReference security)

def unwrap (security : ℕ) (group : SafeGroup security) : Group security := (group.1, group.2.val)

theorem bodyReference_expectation (security : ℕ) (test : Palette security → ℝ) :
    (ActualControls.bodyReference security).expectation (fun center => test center.val) =
      (centerLaw security).expectation test := by
  exact ActualControls.supportedLaw_expectation (centerLaw security) (InwardAnchor.SafeColor security)
    (fun color hunsafe => by
      simpa only [centerLaw] using centerProfile_zero_outside security color hunsafe) test

theorem reference_expectation (security : ℕ) (test : Group security → ℝ) :
    (reference security).expectation (fun group => test (unwrap security group)) =
      (groupLaw security).expectation test := by
  rw [reference, groupLaw, FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  congr 1
  funext primary
  exact bodyReference_expectation security (fun center => test (primary, center))

theorem reference_body_expectation (security : ℕ) (test : ActualControls.SafePalette security → ℝ) :
    (reference security).expectation (fun group => test group.2) =
      (ActualControls.bodyReference security).expectation test := by
  rw [reference, FiniteDist.expectation_prod]
  exact FiniteDist.expectation_const (primaryLaw security)
    ((ActualControls.bodyReference security).expectation test)

theorem reference_lower (security : ℕ) (group : SafeGroup security) :
    1 / (4 * (Parameters.modulus security : ℝ) ^ 2) ≤ (reference security).weight group := by
  have hq := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight group.1 := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security group.1
  have hb := ActualControls.bodyReference_lower security group.2
  calc
    _ = (1 / (2 * (Parameters.modulus security : ℝ))) *
        (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
    _ ≤ (primaryLaw security).weight group.1 * (ActualControls.bodyReference security).weight group.2 :=
      mul_le_mul hp hb (by positivity) ((primaryLaw security).nonneg _)
    _ = _ := rfl

theorem reference_positive (security : ℕ) (group : SafeGroup security) :
    0 < (reference security).weight group :=
  mul_pos (ActualControls.primaryReference_positive security group.1)
    (ActualControls.bodyReference_positive security group.2)

theorem reference_map_unwrap (security : ℕ) :
    (reference security).map (unwrap security) = groupLaw security := by
  ext output
  have h := reference_expectation security (fun group => if group = output then 1 else 0)
  have hmap := FiniteDist.expectation_map (reference security) (unwrap security)
    (fun group => if group = output then 1 else 0)
  have hh := hmap.trans h
  simpa only [FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hh

theorem reference_map_body (security : ℕ) :
    (reference security).map Prod.snd = ActualControls.bodyReference security := by
  ext output
  have h := reference_body_expectation security (fun center => if center = output then 1 else 0)
  have hmap := FiniteDist.expectation_map (reference security) Prod.snd
    (fun center => if center = output then 1 else 0)
  have hh := hmap.trans h
  simpa only [FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hh

/-- The common-alphabet kernel used by two-pool moment estimates. The
ordinary-body primary coordinate is independent and unused. -/
def kernel (security r s : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s)
    (word : (Fin r ⊕ Fin s) → SafeGroup security) : ℝ :=
  pairedKernel security r s input.val
    (fun index => unwrap security (word (Sum.inl index)))
    (fun index => (word (Sum.inr index)).2)

theorem kernel_canonical (security r s : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s) :
    Hoeffding.Canonical (fun _ : Fin r ⊕ Fin s => reference security) Finset.univ
      (kernel security r s input) := by
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ _))
    rw [heq]
  · intro index _ word
    cases index with
    | inl index =>
      have hupdate (group : SafeGroup security) : kernel security r s input
          (Function.update word (Sum.inl index) group) =
          pairedKernel security r s input.val
            (Function.update (fun slot => unwrap security (word (Sum.inl slot))) index (unwrap security group))
            (fun slot => (word (Sum.inr slot)).2) := by
        unfold kernel
        congr 1
        · funext slot
          by_cases heq : slot = index <;> simp [heq, Function.update]
        · funext slot
          simp [Function.update]
      simp_rw [hupdate]
      change (reference security).expectation (fun group => pairedKernel security r s input.val
        (Function.update (fun slot => unwrap security (word (Sum.inl slot))) index (unwrap security group))
        (fun slot => (word (Sum.inr slot)).2)) = 0
      rw [reference_expectation security (fun group => pairedKernel security r s input.val
        (Function.update (fun slot => unwrap security (word (Sum.inl slot))) index group)
        (fun slot => (word (Sum.inr slot)).2))]
      exact (PhysicalTriangularity.pairedKernel_primary_canonical security r s input
        (fun slot => (word (Sum.inr slot)).2)).2 index (Finset.mem_univ _) _
    | inr index =>
      have hupdate (group : SafeGroup security) : kernel security r s input
          (Function.update word (Sum.inr index) group) =
          pairedKernel security r s input.val
            (fun slot => unwrap security (word (Sum.inl slot)))
            (Function.update (fun slot => (word (Sum.inr slot)).2) index group.2) := by
        unfold kernel
        congr 1
        · funext slot
          simp [Function.update]
        · funext slot
          by_cases heq : slot = index <;> simp [heq, Function.update]
      simp_rw [hupdate]
      change (reference security).expectation (fun group => pairedKernel security r s input.val
        (fun slot => unwrap security (word (Sum.inl slot)))
        (Function.update (fun slot => (word (Sum.inr slot)).2) index group.2)) = 0
      rw [reference_body_expectation security (fun center => pairedKernel security r s input.val
        (fun slot => unwrap security (word (Sum.inl slot)))
        (Function.update (fun slot => (word (Sum.inr slot)).2) index center))]
      exact PhysicalTriangularity.pairedKernel_body_centered security r s input index _ _

theorem independent_reference_expectation {Slot : Type*} [Fintype Slot]
    (security : ℕ) (test : (Slot → Group security) → ℝ) :
    (FiniteDist.independent (fun _ : Slot => reference security)).expectation
      (fun word => test (fun slot => unwrap security (word slot))) =
        (FiniteDist.independent (fun _ : Slot => groupLaw security)).expectation test := by
  have hmap := FiniteDist.independent_map_coordinates (fun _ : Slot => reference security)
    (fun _ => unwrap security)
  simp only [reference_map_unwrap] at hmap
  have h := FiniteDist.expectation_map (FiniteDist.independent (fun _ : Slot => reference security))
    (fun word slot => unwrap security (word slot)) test
  rw [hmap] at h
  exact h.symm

theorem independent_body_expectation {Slot : Type*} [Fintype Slot]
    (security : ℕ) (test : (Slot → ActualControls.SafePalette security) → ℝ) :
    (FiniteDist.independent (fun _ : Slot => reference security)).expectation
      (fun word => test (fun slot => (word slot).2)) =
        (FiniteDist.independent (fun _ : Slot => ActualControls.bodyReference security)).expectation test := by
  have hmap := FiniteDist.independent_map_coordinates (fun _ : Slot => reference security)
    (fun _ => Prod.snd)
  simp only [reference_map_body] at hmap
  have h := FiniteDist.expectation_map (FiniteDist.independent (fun _ : Slot => reference security))
    (fun word slot => (word slot).2) test
  rw [hmap] at h
  exact h.symm

/-- Independent unused primary coordinates in the body pool disappear
exactly, and unsafe compensator atoms were discarded only at zero mass. -/
theorem common_expectation (security primaryPool bodyPool : ℕ)
    (test : (Fin primaryPool → Group security) →
      (Fin bodyPool → ActualControls.SafePalette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin primaryPool ⊕ Fin bodyPool => reference security)).expectation
      (fun word => test (fun index => unwrap security (word (Sum.inl index)))
        (fun index => (word (Sum.inr index)).2)) =
      ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security) test := by
  rw [ControlCoordinates.kernelMean_iterated]
  have hreference : (fun _ : Fin primaryPool ⊕ Fin bodyPool => reference security) =
      Sum.elim (fun _ : Fin primaryPool => reference security) (fun _ : Fin bodyPool => reference security) := by
    funext index
    cases index <;> rfl
  rw [hreference]
  rw [independent_sum_expectation]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hbody (groups : Fin primaryPool → SafeGroup security) :
      (FiniteDist.independent (fun _ : Fin bodyPool => reference security)).expectation
        (fun centers => test (fun index => unwrap security (groups index)) (fun index => (centers index).2)) =
      (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security)).expectation
        (fun centers => test (fun index => unwrap security (groups index)) centers) :=
    independent_body_expectation security (test (fun index => unwrap security (groups index)))
  simp_rw [hbody]
  exact independent_reference_expectation security (fun groups =>
    (FiniteDist.independent (fun _ : Fin bodyPool => ActualControls.bodyReference security)).expectation (test groups))

theorem kernel_energy_le (security r s : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s) :
    (FiniteDist.independent (fun _ : Fin r ⊕ Fin s => reference security)).l2Sq
      (kernel security r s input) ≤
        258 ^ r * ControlNorm.blockEnergy (primaryLaw security) (ActualControls.bodyReference security) input.val := by
  change (FiniteDist.independent (fun _ : Fin r ⊕ Fin s => reference security)).expectation
    (fun word => pairedKernel security r s input.val
      (fun index => unwrap security (word (Sum.inl index))) (fun index => (word (Sum.inr index)).2) ^ 2) ≤ _
  rw [common_expectation security r s (fun groups centers => pairedKernel security r s input.val groups centers ^ 2)]
  have heq : ControlNorm.blockEnergy (primaryLaw security) (ActualControls.bodyReference security) input.val =
      ControlCoordinates.kernelMean (primaryLaw security) (ActualControls.bodyReference security)
        (fun colors centers => input.val colors centers ^ 2) := rfl
  rw [heq, ControlCoordinates.kernelMean_iterated_reverse, ControlCoordinates.kernelMean_iterated_reverse]
  calc
    _ ≤ (FiniteDist.independent (fun _ : Fin s => ActualControls.bodyReference security)).expectation
        (fun centers => 258 ^ r *
          (FiniteDist.independent (fun _ : Fin r => primaryLaw security)).l2Sq
            (fun colors => input.val colors centers)) := by
      unfold FiniteDist.expectation
      apply Finset.sum_le_sum
      intro centers _
      exact mul_le_mul_of_nonneg_left (pairedKernel_energy_le security r s input.val centers)
        ((FiniteDist.independent (fun _ : Fin s => ActualControls.bodyReference security)).nonneg centers)
    _ = _ := by rw [FiniteDist.expectation_const_mul]; rfl

theorem statistic_formula (security r s primaryPool bodyPool : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s)
    (word : (Fin primaryPool ⊕ Fin bodyPool) → SafeGroup security) :
    CanonicalMoments.twoPoolStatistic (kernel security r s input) word =
      ControlCoordinates.twoPoolUStatistic primaryPool bodyPool (pairedKernel security r s input.val)
        (fun index => unwrap security (word (Sum.inl index))) (fun index => (word (Sum.inr index)).2) := by
  unfold CanonicalMoments.twoPoolStatistic ControlCoordinates.twoPoolUStatistic
  simp only [Fintype.card_fin]
  congr 1

theorem statistic_moment_eq (security r s primaryPool bodyPool power : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s) :
    (FiniteDist.independent (fun _ : Fin primaryPool ⊕ Fin bodyPool => reference security)).expectation
      (fun word => |CanonicalMoments.twoPoolStatistic (kernel security r s input) word| ^ power) =
      ControlCoordinates.kernelMean (groupLaw security) (ActualControls.bodyReference security)
        (fun groups centers => |ControlCoordinates.twoPoolUStatistic primaryPool bodyPool
          (pairedKernel security r s input.val) groups centers| ^ power) := by
  simp_rw [statistic_formula]
  exact common_expectation security primaryPool bodyPool (fun groups centers =>
    |ControlCoordinates.twoPoolUStatistic primaryPool bodyPool (pairedKernel security r s input.val) groups centers| ^ power)

end

end CurrentAFT.SafeControlGroups

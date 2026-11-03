import CurrentAFT.SafeControlGroups
import CurrentAFT.MomentParameters

/-!
# Fixed high moments of the actual signed public coefficient weight

The true paired kernel is centered before its distinct-index average.
Its common safe-group alphabet has a proved atom lower bound, and each
pool keeps its own collision normalizer. The complete coefficient family
is then summed by finite Minkowski in the genuine public reference law.
-/

namespace CurrentAFT.PhysicalMoments

open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis ControlCoordinates ControlNorm
  BackgroundRates FiniteAtomMoments
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference SafeControlGroups.reference SafeControlGroups.kernel

/-- A fixed kernel's moment constant includes the proved tensor energy
cost `258^r≤17^(2r)`. It has no public-parameter dependence. -/
def blockFactor (primaryOrder bodyOrder moment : ℕ) : ℝ :=
  momentFactor primaryOrder bodyOrder moment 262144 * 17 ^ primaryOrder

theorem blockFactor_nonneg (primaryOrder bodyOrder moment : ℕ) :
    0 ≤ blockFactor primaryOrder bodyOrder moment :=
  mul_nonneg (momentFactor_nonneg _ _ _ _ (by norm_num)) (by positivity)

/-- An order-only common constant for the finite family of all arities. -/
def coefficientFactor (order moment : ℕ) : ℝ :=
  1 + ∑ arity : PositiveArity order, blockFactor arity.val.1.val arity.val.2.val moment

theorem coefficientFactor_positive (order moment : ℕ) : 0 < coefficientFactor order moment := by
  unfold coefficientFactor
  have hsum : 0 ≤ ∑ arity : PositiveArity order,
      blockFactor arity.val.1.val arity.val.2.val moment :=
    Finset.sum_nonneg fun arity _ => blockFactor_nonneg _ _ _
  linarith

theorem blockFactor_le_coefficientFactor (order moment : ℕ) (arity : PositiveArity order) :
    blockFactor arity.val.1.val arity.val.2.val moment ≤ coefficientFactor order moment := by
  have h := Finset.single_le_sum
    (fun arity (_ : arity ∈ (Finset.univ : Finset (PositiveArity order))) => blockFactor_nonneg arity.val.1.val arity.val.2.val moment)
    (Finset.mem_univ arity)
  unfold coefficientFactor
  linarith

theorem radius_ge_one (security : ℕ) : 1 ≤ radius security := by
  apply Real.one_le_rpow
  · exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  · norm_num

theorem plain_grade_le_public_grade (security r s : ℕ) :
    (1 / Real.sqrt (Parameters.legCount security : ℝ)) ^ r *
        (1 / Real.sqrt (ordinaryPool security : ℝ)) ^ s ≤
      gradeWeight (primaryFactor security) (bodyFactor security) r s := by
  have hbodyRate : 1 / Real.sqrt (ordinaryPool security : ℝ) ≤ bodyFactor security := by
    have h := mul_le_mul_of_nonneg_right (radius_ge_one security)
      (inv_nonneg.mpr (Real.sqrt_nonneg (ordinaryPool security : ℝ)))
    simpa only [bodyFactor, one_div, one_mul] using h
  unfold gradeWeight primaryFactor
  simp only [one_div]
  have hbodyPower : (Real.sqrt (ordinaryPool security : ℝ))⁻¹ ^ s ≤ bodyFactor security ^ s := by
    simpa only [one_div] using pow_le_pow_left₀ (by positivity) hbodyRate s
  exact mul_le_mul_of_nonneg_left
    hbodyPower (by positivity)

/-- Actual whole common-kernel energy supplies the L2 input to the
finite-atom moment theorem. No factorization of the joint kernel is used. -/
theorem safe_kernel_norm_le (security r s : ℕ)
    (input : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin r ⊕ Fin s => SafeControlGroups.reference security)).l2Sq
      (SafeControlGroups.kernel security r s input)) ≤
      17 ^ r * blockL2 (primaryLaw security) (ActualControls.bodyReference security) input.val := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by positivity) (blockL2_nonneg _ _ _)
  · have hpower : (258 : ℝ) ^ r ≤ ((17 : ℝ) ^ r) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    calc
      _ ≤ 258 ^ r * blockEnergy (primaryLaw security) (ActualControls.bodyReference security) input.val :=
        SafeControlGroups.kernel_energy_le security r s input
      _ ≤ (17 ^ r) ^ 2 * blockEnergy (primaryLaw security) (ActualControls.bodyReference security) input.val :=
        mul_le_mul_of_nonneg_right hpower (blockEnergy_nonneg _ _ _)
      _ = _ := by rw [mul_pow, blockL2_sq]

/-- Complete fixed even moment of one actual paired distinct-group
summand under the original two independent public-control pools. -/
theorem block_even_moment_le (security r s moment : ℕ) (hmoment : 1 ≤ moment)
    (hprimaryRoom : 2 * r ≤ Parameters.legCount security)
    (hbodyRoom : 2 * s ≤ ordinaryPool security)
    (input : canonicalKernels (primaryLaw security) (ActualControls.bodyReference security) r s) :
    kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (fun groups centers => |twoPoolUStatistic (Parameters.legCount security) (ordinaryPool security)
        (pairedKernel security r s input.val) groups centers| ^ (2 * moment)) ≤
      (blockFactor r s moment * gradeWeight (primaryFactor security) (bodyFactor security) r s *
        blockL2 (primaryLaw security) (ActualControls.bodyReference security) input.val) ^ (2 * moment) := by
  have hinput : Sum.elim (fun _ : Fin r => SafeControlGroups.reference security)
      (fun _ : Fin s => SafeControlGroups.reference security) =
        (fun _ : Fin r ⊕ Fin s => SafeControlGroups.reference security) := by funext slot; cases slot <;> rfl
  have hpool : Sum.elim (fun _ : Fin (Parameters.legCount security) => SafeControlGroups.reference security)
      (fun _ : Fin (ordinaryPool security) => SafeControlGroups.reference security) =
        (fun _ : Fin (Parameters.legCount security) ⊕ Fin (ordinaryPool security) => SafeControlGroups.reference security) := by
    funext slot
    cases slot <;> rfl
  have hcanonical : Hoeffding.Canonical
      (Sum.elim (fun _ : Fin r => SafeControlGroups.reference security)
        (fun _ : Fin s => SafeControlGroups.reference security)) Finset.univ
      (SafeControlGroups.kernel security r s input) := by
    rw [hinput]
    exact SafeControlGroups.kernel_canonical security r s input
  have h := twoPool_even_moment_le_energy
    (PS := Fin r) (BS := Fin s) (PP := Fin (Parameters.legCount security)) (BP := Fin (ordinaryPool security))
    (SafeControlGroups.reference security) (SafeControlGroups.reference security)
    (SafeControlGroups.kernel security r s input) hcanonical (currentAtomLower security)
    (currentAtomLower_positive security) (SafeControlGroups.reference_lower security)
    (SafeControlGroups.reference_lower security) 262144 (by norm_num)
    (by simpa only [Fintype.card_fin] using current_primary_atom_ratio security)
    (by simpa only [Fintype.card_fin] using current_body_atom_ratio security) moment hmoment
    (by simpa only [Fintype.card_fin, Parameters.legCount_eq] using pow_pos (Parameters.base_pos security) 128)
    (by simpa only [Fintype.card_fin] using ordinaryPool_pos security)
    (by simpa only [Fintype.card_fin] using hprimaryRoom) (by simpa only [Fintype.card_fin] using hbodyRoom)
  rw [hinput, hpool, SafeControlGroups.statistic_moment_eq] at h
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply pow_le_pow_left₀
  · exact mul_nonneg (mul_nonneg (momentFactor_nonneg _ _ _ _ (by norm_num)) (by positivity)) (Real.sqrt_nonneg _)
  · have hnorm := safe_kernel_norm_le security r s input
    have hscaleNonneg : 0 ≤ momentFactor r s moment 262144 *
        ((1 / Real.sqrt (Parameters.legCount security : ℝ)) ^ r *
          (1 / Real.sqrt (ordinaryPool security : ℝ)) ^ s) :=
      mul_nonneg (momentFactor_nonneg _ _ _ _ (by norm_num)) (by positivity)
    have hnormScaled := mul_le_mul_of_nonneg_left hnorm
      hscaleNonneg
    apply hnormScaled.trans
    have hgrade := mul_le_mul_of_nonneg_left (plain_grade_le_public_grade security r s)
      (blockFactor_nonneg r s moment)
    have hh := mul_le_mul_of_nonneg_right hgrade (blockL2_nonneg (primaryLaw security)
      (ActualControls.bodyReference security) input.val)
    convert hh using 1
    unfold blockFactor
    ring

/-- The complete actual public weight, after subtracting only its scalar
coordinate, has every fixed high moment controlled by the nonconstant
coefficient norm. Constants depend only on calibration and moment orders. -/
theorem coefficientWeight_even_moment_le (security order moment : ℕ) (hmoment : 1 ≤ moment)
    (hsecurity : 2 * order ≤ security) (coefficient : ActualControls.Coefficients security order) :
    kernelMean (groupLaw security) (ActualControls.bodyReference security)
      (fun groups centers => |coefficientWeight security order (Parameters.legCount security)
        (ordinaryPool security) coefficient groups centers - coefficient.1| ^ (2 * moment)) ≤
      (coefficientFactor order moment * coefficientNorm (primaryLaw security) (ActualControls.bodyReference security)
        order (primaryFactor security) (bodyFactor security) (0, coefficient.2)) ^ (2 * moment) := by
  let law := (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => groupLaw security)).prod
    (FiniteDist.independent (fun _ : Fin (ordinaryPool security) => ActualControls.bodyReference security))
  let summand := fun (arity : PositiveArity order)
      (inputs : (Fin (Parameters.legCount security) → Group security) ×
        (Fin (ordinaryPool security) → ActualControls.SafePalette security)) =>
    twoPoolUStatistic (Parameters.legCount security) (ordinaryPool security)
      (pairedKernel security arity.val.1.val arity.val.2.val (coefficient.2 arity).val) inputs.1 inputs.2
  let size := fun arity : PositiveArity order =>
    gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
      blockL2 (primaryLaw security) (ActualControls.bodyReference security) (coefficient.2 arity).val
  have hsize (arity : PositiveArity order) : 0 ≤ size arity :=
    mul_nonneg (gradeWeight_nonneg _ _ (by unfold primaryFactor; positivity)
      (by unfold bodyFactor radius; positivity) _ _) (blockL2_nonneg _ _ _)
  have hterm (arity : PositiveArity order) :
      law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤
        (coefficientFactor order moment * size arity) ^ (2 * moment) := by
    have hroom := current_pool_room security order hsecurity _ _ arity.property.2
    have h := block_even_moment_le security _ _ moment hmoment hroom.1 hroom.2 (coefficient.2 arity)
    change law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤ _ at h
    rw [mul_assoc] at h
    change law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤
      (blockFactor arity.val.1.val arity.val.2.val moment * size arity) ^ (2 * moment) at h
    apply h.trans
    apply pow_le_pow_left₀ (mul_nonneg (blockFactor_nonneg _ _ _) (hsize arity))
    exact mul_le_mul_of_nonneg_right (blockFactor_le_coefficientFactor order moment arity) (hsize arity)
  have hsum := FiniteDist.expectation_abs_sum_pow_le law summand
    (fun arity => coefficientFactor order moment * size arity)
    (fun arity => mul_nonneg (coefficientFactor_positive order moment).le (hsize arity))
    (2 * moment) (by omega) hterm
  have hweight (inputs : (Fin (Parameters.legCount security) → Group security) ×
      (Fin (ordinaryPool security) → ActualControls.SafePalette security)) :
      coefficientWeight security order (Parameters.legCount security) (ordinaryPool security)
        coefficient inputs.1 inputs.2 - coefficient.1 = ∑ arity, summand arity inputs := by
    unfold coefficientWeight
    ring
  change law.expectation _ ≤ _
  simp_rw [hweight]
  apply hsum.trans_eq
  rw [← Finset.mul_sum]
  congr 2
  unfold coefficientNorm
  simp only [abs_zero, zero_add]
  rfl

end

end CurrentAFT.PhysicalMoments

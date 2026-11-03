import CurrentAFT.GradedControlNorm

/-!
# Stability in the actual finite graded coefficient norm

Triangle, absolute homogeneity, and separation follow from the genuine
weighted finite block sums. The finite-dimensional inverse argument is then
stated for an actual linear map on the coefficient family, using a pointwise
defect estimate in this same norm. This avoids installing an unrelated
ambient norm or assuming a normed algebra.

The construction must still prove the displayed defect estimate for its
complete response. Positive reference atoms and positive population/radius
factors are explicit; the actual safe-control instance discharges them.
-/

namespace CurrentAFT.GradedControlStability

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem familyNorm_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) : familyNorm primary body order primaryFactor bodyFactor 0 = 0 := by
  simp only [familyNorm, Pi.zero_apply, Submodule.coe_zero, blockL2, blockEnergy_apply,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]

theorem familyNorm_add_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (first second : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (first + second) ≤
      familyNorm primary body order primaryFactor bodyFactor first +
        familyNorm primary body order primaryFactor bodyFactor second := by
  simp only [familyNorm, Pi.add_apply, Submodule.coe_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro arity _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (blockL2_add_le primary body _ _)
    (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)

theorem familyNorm_smul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor scalar : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (scalar • family) =
      |scalar| * familyNorm primary body order primaryFactor bodyFactor family := by
  simp only [familyNorm, Pi.smul_apply, Submodule.coe_smul, blockL2_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro arity _
  ring

theorem familyNorm_neg (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (-family) =
      familyNorm primary body order primaryFactor bodyFactor family := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
    familyNorm_smul primary body order primaryFactor bodyFactor (-1) family

theorem familyNorm_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family = 0 ↔ family = 0 := by
  constructor
  · intro hzero
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun arity _ => mul_nonneg
      (gradeWeight_nonneg primaryFactor bodyFactor hprimary.le hbody.le _ _) (blockL2_nonneg primary body _))).mp hzero
    funext arity
    have hweight : 0 < gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val :=
      mul_pos (pow_pos hprimary _) (pow_pos hbody _)
    have hblock : blockL2 primary body (family arity).val = 0 :=
      (mul_eq_zero.mp (hterms arity (Finset.mem_univ _))).resolve_left (ne_of_gt hweight)
    apply Subtype.ext
    exact (blockL2_eq_zero_iff primary body hprimaryLaw hbodyLaw _).mp hblock
  · intro hzero
    rw [hzero, familyNorm_zero]

/-- A pointwise small defect in the actual norm gives the lower norm bound
used for stable inversion. No continuity or topological operator norm is an
input assumption. -/
theorem family_operator_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family ≤
      familyNorm primary body order primaryFactor bodyFactor (operator family) / (1 - theta) := by
  have htriangle := familyNorm_add_le primary body order primaryFactor bodyFactor hprimary hbody
    (operator family) (family - operator family)
  have hequal : operator family + (family - operator family) = family := by abel
  rw [hequal] at htriangle
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith [hdefect family]

theorem family_operator_injective (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family) :
    Function.Injective operator := by
  intro first second hequal
  have hbound := family_operator_norm_le primary body order primaryFactor bodyFactor hprimary.le hbody.le
    operator theta hgap hdefect (first - second)
  have hoperator : operator (first - second) = 0 := by rw [map_sub, hequal, sub_self]
  rw [hoperator, familyNorm_zero, zero_div] at hbound
  have hnorm : familyNorm primary body order primaryFactor bodyFactor (first - second) = 0 :=
    le_antisymm hbound (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary.le hbody.le _)
  exact sub_eq_zero.mp ((familyNorm_eq_zero_iff primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody _).mp hnorm)

/-- Finite-dimensionality supplies surjectivity only after injectivity has
been proved from the actual norm and pointwise defect estimate. -/
theorem family_operator_bijective (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family) :
    Function.Bijective operator := by
  have hinjective := family_operator_injective primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody operator theta hgap hdefect
  exact ⟨hinjective, LinearMap.surjective_of_injective hinjective⟩

/-- The finite calibration solve in the actual coefficient space, including
the correction bound relative to any reference coefficient. The full physical
response's defect estimate remains an explicit construction obligation. -/
theorem family_calibration_existsUnique (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family)
    (target : KernelFamily primary body order) :
    ∃ coefficient, operator coefficient = target ∧
      (∀ other, operator other = target → other = coefficient) ∧
      ∀ reference, familyNorm primary body order primaryFactor bodyFactor (coefficient - reference) ≤
        familyNorm primary body order primaryFactor bodyFactor (target - operator reference) / (1 - theta) := by
  have hbijective := family_operator_bijective primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody operator theta hgap hdefect
  obtain ⟨coefficient, hcoefficient⟩ := hbijective.2 target
  refine ⟨coefficient, hcoefficient, fun other hother => hbijective.1 (hother.trans hcoefficient.symm), ?_⟩
  intro reference
  simpa only [map_sub, hcoefficient] using family_operator_norm_le primary body order
    primaryFactor bodyFactor hprimary.le hbody.le operator theta hgap hdefect (coefficient - reference)

end

end CurrentAFT.GradedControlStability

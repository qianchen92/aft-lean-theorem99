import CurrentAFT.BackgroundRates
import CurrentAFT.ActualControls
import CurrentAFT.GradedControlStability

/-!
# Actual free and translated certificates in the finite graded algebra

The density coefficients are the concrete certificates already constructed
from the current proposal. Body coefficients are restricted to the actual
safe alphabet, on which the reference law is strictly positive. Each atom
is inserted into its genuine degree-one fiber of the finite family.
-/

namespace CurrentAFT.BackgroundFamilies

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary FringeCertificate
  BackgroundCertificates BackgroundTranslations BackgroundRates ActualControls
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw
  ProposalPrimary.centerLaw InwardAnchor.smoothedAnchorLaw

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def primaryKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    canonicalKernels primary body 1 0 := by
  refine ⟨fun colors _ => density (colors 0), ?_, ?_, ?_⟩
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hcenter
  · intro index
    exact Fin.elim0 index
  · intro primaryOrder bodyOrder colors centers
    have hi : primaryOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hi]

def bodyKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    canonicalKernels primary body 0 1 := by
  refine ⟨fun _ centers => density (centers 0), ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hcenter
  · intro primaryOrder bodyOrder colors centers
    have hi : bodyOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hi]

theorem primaryKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    blockL2 primary body (primaryKernel primary body density hcenter).val =
      Real.sqrt (∑ color, primary.weight color * density color ^ 2) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [primaryKernel, Fin.prod_univ_zero, mul_one,
    Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  change (∑ colors : Fin 1 → Primary, primary.weight (colors 0) * density (colors 0) ^ 2) = _
  exact ((Equiv.funUnique (Fin 1) Primary).symm.sum_comp
    (fun colors => primary.weight (colors 0) * density (colors 0) ^ 2)).symm

theorem bodyKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    blockL2 primary body (bodyKernel primary body density hcenter).val =
      Real.sqrt (∑ color, body.weight color * density color ^ 2) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [bodyKernel, Fin.prod_univ_zero, one_mul,
    Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  change (∑ colors : Fin 1 → Body, body.weight (colors 0) * density (colors 0) ^ 2) = _
  exact ((Equiv.funUnique (Fin 1) Body).symm.sum_comp
    (fun colors => body.weight (colors 0) * density (colors 0) ^ 2)).symm

def primaryArity (order : ℕ) (horder : 1 ≤ order) : TruncatedArity order :=
  ⟨(⟨1, by omega⟩, 0), by simpa⟩

def bodyArity (order : ℕ) (horder : 1 ≤ order) : TruncatedArity order :=
  ⟨(0, ⟨1, by omega⟩), by simpa⟩

def primaryFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    KernelFamily primary body order :=
  Pi.single (primaryArity order horder) (primaryKernel primary body density hcenter)

def bodyFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    KernelFamily primary body order :=
  Pi.single (bodyArity order horder) (bodyKernel primary body density hcenter)

theorem familyNorm_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (arity : TruncatedArity order)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    familyNorm primary body order primaryFactor bodyFactor (Pi.single arity kernel) =
      gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
        blockL2 primary body kernel.val := by
  unfold familyNorm
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hne
    rw [Pi.single_eq_of_ne hne]
    simp only [Submodule.coe_zero, blockL2, blockEnergy_apply, Pi.zero_apply,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
  · intro hout
    exact (hout (Finset.mem_univ arity)).elim

theorem primaryFamily_norm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (primaryFactor bodyFactor : ℝ) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    familyNorm primary body order primaryFactor bodyFactor
      (primaryFamily primary body order horder density hcenter) =
        primaryFactor * Real.sqrt (∑ color, primary.weight color * density color ^ 2) := by
  rw [primaryFamily, familyNorm_single, primaryKernel_blockL2]
  simp [primaryArity, gradeWeight]

theorem bodyFamily_norm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (primaryFactor bodyFactor : ℝ) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    familyNorm primary body order primaryFactor bodyFactor
      (bodyFamily primary body order horder density hcenter) =
        bodyFactor * Real.sqrt (∑ color, body.weight color * density color ^ 2) := by
  rw [bodyFamily, familyNorm_single, bodyKernel_blockL2]
  simp [bodyArity, gradeWeight]

theorem safe_centered (security : ℕ) (density : ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (centerLaw security).weight color * density color = 0) :
    ∑ color, (bodyReference security).weight color * density color.val = 0 := by
  exact (supportedLaw_expectation (centerLaw security) (InwardAnchor.SafeColor security)
    _ density).trans hcenter

theorem safe_square (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    (∑ color, (bodyReference security).weight color * density color.val ^ 2) =
      ∑ color, (centerLaw security).weight color * density color ^ 2 :=
  supportedLaw_expectation (centerLaw security) (InwardAnchor.SafeColor security) _
    (fun color => density color ^ 2)

abbrev ActualFamily (security order : ℕ) :=
  KernelFamily (primaryLaw security) (bodyReference security) order

def freeCertificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder
      (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
    bodyFamily (primaryLaw security) (bodyReference security) order horder
      (fun color => bodyCertificateDensity security color.val)
        (safe_centered security _ (bodyCertificateDensity_centered security))

def translationCertificate (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    ActualFamily security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder
      (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
    primaryFamily (primaryLaw security) (bodyReference security) order horder
      (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift) +
    bodyFamily (primaryLaw security) (bodyReference security) order horder
      (fun color => safeSeedDensity security shift color.val)
        (safe_centered security _ (safeSeedDensity_centered security shift))

attribute [local irreducible] primaryFamily bodyFamily ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor BackgroundRates.radius
  primaryCertificateDensity bodyCertificateDensity residualCertificateDensity safeSeedDensity

theorem freeCertificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (freeCertificate security order horder) ≤
        freeAtomEnvelope security := by
  have hprimary : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbody : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_add_le _ _ _ _ _ hprimary hbody _ _).trans_eq
  rw [primaryFamily_norm, bodyFamily_norm, safe_square]
  rfl

theorem translationCertificate_norm (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (translationCertificate security order horder shift) ≤
        translationAtomEnvelope security shift := by
  have hprimary : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbody : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have h1 := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hprimary hbody
    (primaryFamily _ _ order horder (primaryCertificateDensity security) (primaryCertificateDensity_centered security))
    (primaryFamily _ _ order horder (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift))
  have h2 := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hprimary hbody
    (primaryFamily _ _ order horder (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
      primaryFamily _ _ order horder (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift))
    (bodyFamily _ _ order horder (fun color => safeSeedDensity security shift color.val)
      (safe_centered security _ (safeSeedDensity_centered security shift)))
  apply h2.trans
  apply (add_le_add h1 le_rfl).trans_eq
  rw [primaryFamily_norm, primaryFamily_norm, bodyFamily_norm, safe_square]
  unfold translationAtomEnvelope
  ring

theorem primaryArity_ne_bodyArity (order : ℕ) (horder : 1 ≤ order) :
    primaryArity order horder ≠ bodyArity order horder := by
  intro hequal
  have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
  change 1 = 0 at h
  omega

def primaryCoefficient (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (family : KernelFamily primary body order) : Primary → ℝ :=
  fun color => (family (primaryArity order horder)).val (fun _ => color) Fin.elim0

def bodyCoefficient (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (family : KernelFamily primary body order) : Body → ℝ :=
  fun center => (family (bodyArity order horder)).val Fin.elim0 (fun _ => center)

theorem primaryCoefficient_primaryFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    primaryCoefficient primary body order horder (primaryFamily primary body order horder density hcenter) = density := by
  funext color
  simp only [primaryCoefficient, primaryFamily, Pi.single_eq_same, primaryKernel]

theorem bodyCoefficient_bodyFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    bodyCoefficient primary body order horder (bodyFamily primary body order horder density hcenter) = density := by
  funext center
  simp only [bodyCoefficient, bodyFamily, Pi.single_eq_same, bodyKernel]

theorem primaryCoefficient_bodyFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    primaryCoefficient primary body order horder (bodyFamily primary body order horder density hcenter) = 0 := by
  funext color
  simp only [primaryCoefficient, bodyFamily,
    Pi.single_eq_of_ne (primaryArity_ne_bodyArity order horder), Submodule.coe_zero, Pi.zero_apply]

theorem bodyCoefficient_primaryFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    bodyCoefficient primary body order horder (primaryFamily primary body order horder density hcenter) = 0 := by
  funext center
  simp only [bodyCoefficient, primaryFamily,
    Pi.single_eq_of_ne (primaryArity_ne_bodyArity order horder).symm, Submodule.coe_zero, Pi.zero_apply]

theorem primaryCoefficient_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (first second : KernelFamily primary body order) :
    primaryCoefficient primary body order horder (first + second) =
      primaryCoefficient primary body order horder first + primaryCoefficient primary body order horder second := rfl

theorem bodyCoefficient_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (first second : KernelFamily primary body order) :
    bodyCoefficient primary body order horder (first + second) =
      bodyCoefficient primary body order horder first + bodyCoefficient primary body order horder second := rfl

/-- These are the actual coefficient values, rather than an existence claim
about some family with a prescribed evaluation. -/
theorem freeCertificate_coefficients (security order : ℕ) (horder : 1 ≤ order) :
    primaryCoefficient _ _ order horder (freeCertificate security order horder) = primaryCertificateDensity security ∧
    bodyCoefficient _ _ order horder (freeCertificate security order horder) =
      fun center => bodyCertificateDensity security center.val := by
  constructor
  · rw [freeCertificate, primaryCoefficient_add, primaryCoefficient_primaryFamily,
      primaryCoefficient_bodyFamily, add_zero]
  · rw [freeCertificate, bodyCoefficient_add, bodyCoefficient_primaryFamily,
      bodyCoefficient_bodyFamily, zero_add]

theorem translationCertificate_coefficients (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    primaryCoefficient _ _ order horder (translationCertificate security order horder shift) =
      primaryCertificateDensity security + residualCertificateDensity security shift ∧
    bodyCoefficient _ _ order horder (translationCertificate security order horder shift) =
      fun center => safeSeedDensity security shift center.val := by
  constructor
  · rw [translationCertificate, primaryCoefficient_add, primaryCoefficient_add,
      primaryCoefficient_primaryFamily, primaryCoefficient_primaryFamily,
      primaryCoefficient_bodyFamily, add_zero]
  · rw [translationCertificate, bodyCoefficient_add, bodyCoefficient_add,
      bodyCoefficient_primaryFamily, bodyCoefficient_primaryFamily,
      bodyCoefficient_bodyFamily, zero_add, zero_add]

theorem freeCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (freeCertificate security order horder) ≤
        84 / (Parameters.base security : ℝ) ^ 110 :=
  (freeCertificate_norm security order horder).trans (freeAtomEnvelope_decay security)

theorem translationCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (translationCertificate security order horder shift) ≤
        56 / (Parameters.base security : ℝ) ^ 79 :=
  (translationCertificate_norm security order horder shift).trans (translationAtomEnvelope_decay security shift)

end

end CurrentAFT.BackgroundFamilies

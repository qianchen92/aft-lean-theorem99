import CurrentAFT.PrimaryTensorInverse
import CurrentAFT.BackgroundFamilies

/-! Actual canonical family coefficients obtained from the primary tensor inverse. -/

namespace CurrentAFT.PrimaryMassFamilies

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  DiffuseProfiles ProposalPrimary ActualControls PrimaryTensorInverse BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  PrimaryTensorInverse.massLift

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def oneWordProfile {Color : Type*} (profile : Color → ℝ) (word : Fin 1 → Color) : ℝ := profile (word 0)

theorem oneWordProfile_centered {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (hzero : ∑ color, profile color = 0) : MassCentered 1 (oneWordProfile profile) := by
  intro index word
  have hi : index = 0 := Subsingleton.elim _ _
  subst index
  simpa only [oneWordProfile, Function.update_self] using hzero

theorem oneWordProfile_symmetric {Color : Type*} (profile : Color → ℝ)
    (permutation : Equiv.Perm (Fin 1)) (word : Fin 1 → Color) :
    oneWordProfile profile (word ∘ permutation) = oneWordProfile profile word := by
  have hi : permutation 0 = 0 := Subsingleton.elim _ _
  simp only [oneWordProfile, Function.comp_apply, hi]

theorem oneWordProfile_energy {Color : Type*} [Fintype Color] (reference : Color → ℝ) (profile : Color → ℝ) :
    (∑ word : Fin 1 → Color, oneWordProfile profile word ^ 2 /
      (∏ index, reference (word index))) = profileSquareNorm reference profile := by
  simp only [oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp (fun word : Fin 1 → Color =>
    profile (word 0) ^ 2 / reference (word 0))).symm

def pairWordProfile {Color : Type*} (profile : Color → Color → ℝ) (word : Fin 2 → Color) : ℝ :=
  profile (word 0) (word 1)

theorem pairWordProfile_symmetric {Color : Type*} (profile : Color → Color → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first)
    (permutation : Equiv.Perm (Fin 2)) (word : Fin 2 → Color) :
    pairWordProfile profile (word ∘ permutation) = pairWordProfile profile word := by
  have hne : (permutation 0).val ≠ (permutation 1).val := by
    intro hequal
    have h := permutation.injective (Fin.ext hequal)
    have hv := congrArg Fin.val h
    norm_num at hv
  have hzero := (permutation 0).isLt
  have hone := (permutation 1).isLt
  have hcases : ((permutation 0).val = 0 ∧ (permutation 1).val = 1) ∨
      ((permutation 0).val = 1 ∧ (permutation 1).val = 0) := by omega
  rcases hcases with hcases | hcases
  · have h0 : permutation 0 = 0 := Fin.ext hcases.1
    have h1 : permutation 1 = 1 := Fin.ext hcases.2
    simp only [pairWordProfile, Function.comp_apply, h0, h1]
  · have h0 : permutation 0 = 1 := Fin.ext hcases.1
    have h1 : permutation 1 = 0 := Fin.ext hcases.2
    simpa only [pairWordProfile, Function.comp_apply, h0, h1] using hsymmetric (word 1) (word 0)

theorem pairWordProfile_energy {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (profile : Color → Color → ℝ) :
    (∑ word : Fin 2 → Color, pairWordProfile profile word ^ 2 /
      (∏ index, reference (word index))) = BlockDensity.pairEnergy reference reference profile := by
  rw [← (finTwoArrowEquiv Color).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pairWordProfile, Fin.prod_univ_two, finTwoArrowEquiv,
    Equiv.coe_fn_symm_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    BlockDensity.pairEnergy]

def massLiftKernel (security degree : ℕ)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    canonicalKernels (primaryLaw security) (bodyReference security) degree 0 := by
  refine ⟨fun colors _ => massLift security degree profile colors, ?_, ?_, ?_⟩
  · intro index colors centers
    exact (massLift_canonical security degree profile hcentered).2 index (Finset.mem_univ index) colors
  · intro index
    exact Fin.elim0 index
  · intro primaryOrder bodyOrder colors centers
    exact massLift_symmetric security degree profile hsymmetric primaryOrder colors

theorem massLiftKernel_blockL2 (security degree : ℕ)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    blockL2 (primaryLaw security) (bodyReference security) (massLiftKernel security degree profile hcentered hsymmetric).val =
      Real.sqrt ((FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
        (massLift security degree profile)) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [massLiftKernel, Fin.prod_univ_zero, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rfl

def primaryArity (order degree : ℕ) (hdegree : degree ≤ order) : TruncatedArity order :=
  ⟨(⟨degree, by omega⟩, 0), by simpa⟩

def massCertificateFamily (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    ActualFamily security order :=
  Pi.single (primaryArity order degree hdegree) (massLiftKernel security degree profile hcentered hsymmetric)

theorem massCertificateFamily_norm (security order degree : ℕ) (hdegree : degree ≤ order)
    (primaryFactor bodyFactor : ℝ) (hfactor : 0 ≤ primaryFactor)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (massCertificateFamily security order degree hdegree profile hcentered hsymmetric) ≤
        primaryFactor ^ degree * (2 / activation security) ^ degree * Real.sqrt (massEnergy security degree profile) := by
  rw [massCertificateFamily, familyNorm_single, massLiftKernel_blockL2]
  have hnorm := mul_le_mul_of_nonneg_left (massLift_norm security degree profile) (pow_nonneg hfactor degree)
  simpa only [primaryArity, gradeWeight, Fin.val_zero, pow_zero, mul_one, mul_assoc] using hnorm

theorem massCertificateFamily_stored_density (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    (fun colors => ((massCertificateFamily security order degree hdegree profile hcentered hsymmetric)
      (primaryArity order degree hdegree)).val colors Fin.elim0) = massLift security degree profile := by
  funext colors
  simp only [massCertificateFamily, Pi.single_eq_same, massLiftKernel]

theorem massCertificateFamily_leading (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    massLeading security degree (fun colors => ((massCertificateFamily security order degree hdegree profile hcentered hsymmetric)
      (primaryArity order degree hdegree)).val colors Fin.elim0) = profile := by
  exact (congrArg (massLeading security degree)
    (massCertificateFamily_stored_density security order degree hdegree profile hcentered hsymmetric)).trans
      (massLift_leading security degree profile)

end

end CurrentAFT.PrimaryMassFamilies

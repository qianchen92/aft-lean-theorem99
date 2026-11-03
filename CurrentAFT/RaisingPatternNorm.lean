import CurrentAFT.RaisingPatternKernel

/-! # Finite-degree counting for the actual mixed-role Hilbert patterns -/
namespace CurrentAFT.RaisingPatternNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily LocalRaisingBounds RaisingPatternBudget RaisingPatternKernel
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

private theorem norm_sum_le {Index : Type*} (security order : ℕ) (terms : Finset Index)
    (families : Index → Family security order) :
    LocalRaisingBounds.coefficientNorm security order (∑ index ∈ terms, families index) ≤
      ∑ index ∈ terms, LocalRaisingBounds.coefficientNorm security order (families index) :=
  familyNorm_sum_le _ _ order _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le terms families

def patternCorrection (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ pattern : Role r s → TruncatedArity order, patternFamily security order horder selected pattern kernel

theorem patternCorrection_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (patternCorrection security order horder selected kernel) ≤
      (Fintype.card (TruncatedArity order) : ℝ) ^ (r + s) *
        ((∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  unfold patternCorrection
  apply (norm_sum_le security order Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Role r s → TruncatedArity order,
        ((∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val) :=
      Finset.sum_le_sum (fun pattern _ => patternFamily_norm security order horder hlarge selected pattern kernel)
    _ = _ := by simp [Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

def homogeneousCorrection (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅,
    patternCorrection security order horder selected kernel

theorem homogeneousCorrection_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (homogeneousCorrection security order horder r s kernel) ≤
      (2 * (Fintype.card (TruncatedArity order) : ℝ)) ^ (r + s) * relativeBudget security *
        (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  let count := (Fintype.card (TruncatedArity order) : ℝ) ^ (r + s)
  let inputNorm := gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    blockL2 (primaryLaw security) (bodyReference security) kernel.val
  have hcount : 0 ≤ count := by unfold count; positivity
  have hinput : 0 ≤ inputNorm := mul_nonneg
    (gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le _ _) (blockL2_nonneg _ _ _)
  have hselection (selected : Finset (Role r s)) (hselected : selected ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅) :
      LocalRaisingBounds.coefficientNorm security order (patternCorrection security order horder selected kernel) ≤
        count * (relativeBudget security * inputNorm) := by
    apply (patternCorrection_norm security order horder hlarge selected kernel).trans
    apply mul_le_mul_of_nonneg_left _ hcount
    apply (mul_le_mul_of_nonneg_right (nonempty_roleCost_product security selected
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1) hsmall) (blockL2_nonneg _ _ _)).trans_eq
    unfold inputNorm
    ring
  unfold homogeneousCorrection
  apply (norm_sum_le security order _ _).trans
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅,
        count * (relativeBudget security * inputNorm) := Finset.sum_le_sum (fun selected hselected => hselection selected hselected)
    _ = (((Finset.univ : Finset (Finset (Role r s))).erase ∅).card : ℝ) *
        (count * (relativeBudget security * inputNorm)) := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (r + s) * (count * (relativeBudget security * inputNorm)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hcount (mul_nonneg (relativeBudget_nonneg security) hinput))
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Role r s))).erase ∅).card ≤ 2 ^ (r + s) by
        calc
          _ ≤ Fintype.card (Finset (Role r s)) := Finset.card_le_univ _
          _ = _ := by simp [Fintype.card_sum])
    _ = _ := by unfold count inputNorm; rw [mul_pow]; ring

def degreeConstant (order : ℕ) : ℝ := (2 * (Fintype.card (TruncatedArity order) : ℝ)) ^ order

theorem degreeConstant_nonneg (order : ℕ) : 0 ≤ degreeConstant order := by unfold degreeConstant; positivity

theorem homogeneousCorrection_norm_order (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (r s : ℕ) (hdegree : r + s ≤ order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (homogeneousCorrection security order horder r s kernel) ≤
      degreeConstant order * relativeBudget security *
        (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  have hcard : 0 < Fintype.card (TruncatedArity order) := Fintype.card_pos_iff.mpr ⟨zeroArity order⟩
  have hbase : (1 : ℝ) ≤ 2 * (Fintype.card (TruncatedArity order) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * Fintype.card (TruncatedArity order) by omega)
  have hbound := pow_le_pow_right₀ hbase hdegree
  have hweight := gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le r s
  exact (homogeneousCorrection_norm security order horder hlarge hsmall r s kernel).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (relativeBudget_nonneg security))
      (mul_nonneg hweight (blockL2_nonneg _ _ _)))

def assembledRaising (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) : Family security order :=
  ∑ arity : TruncatedArity order,
    homogeneousCorrection security order horder arity.val.1.val arity.val.2.val (family arity)

theorem assembledRaising_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (assembledRaising security order horder family) ≤
      degreeConstant order * relativeBudget security * LocalRaisingBounds.coefficientNorm security order family := by
  unfold assembledRaising
  apply (norm_sum_le security order Finset.univ _).trans
  unfold LocalRaisingBounds.coefficientNorm familyNorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun arity _ => homogeneousCorrection_norm_order security order horder hlarge hsmall
    arity.val.1.val arity.val.2.val arity.property (family arity))

def stabilityConstant (order : ℕ) : ℝ := degreeConstant order * (raisingConstant + 80)

theorem assembledRaising_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (assembledRaising security order horder family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ) ^ 38) *
          LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold, relativeBudget_small_eventually] with security hsecurity hsmall family
  have hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  exact (assembledRaising_norm security order horder hlarge hsmall family).trans_eq (by unfold stabilityConstant relativeBudget; ring)

end
end CurrentAFT.RaisingPatternNorm

import CurrentAFT.RaisingPatternKernel
import CurrentAFT.GroupedKernelLinear

/-! # Exact arity decomposition of the actual mixed-role raising response -/
namespace CurrentAFT.CompleteRaisingPatternIdentity
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily CompleteRaising
  RaisingPatternBudget RaisingPatternKernel GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

def columnKernel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role) :
    canonicalKernels (primaryLaw security) (bodyReference security) (totalPrimary pattern) (totalBody pattern) :=
  finiteProduct (primaryLaw security) (bodyReference security)
    (fun role => (pattern role).val.1.val) (fun role => (pattern role).val.2.val)
    (fun role => roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))

theorem patternKernel_column_formula (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    patternKernel security order horder selected pattern kernel =
      ∑ input, inputJoint security kernel input • columnKernel security order horder selected pattern input := by
  apply Subtype.ext
  change canonicalize (primarySlots pattern) (bodySlots pattern) (primaryEquiv pattern) (bodyEquiv pattern)
    (DependentTensorChannel.apply (componentChannel security order horder selected pattern)
      (inputJoint security kernel)) = _
  rw [canonicalize_tensor_formula]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  rw [columnKernel, finiteProduct_val]
  rfl

theorem column_product_retained (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role)
    (hdegree : totalPrimary pattern + totalBody pattern ≤ order) :
    (∏ role : Role r s, Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) =
      embed (primaryLaw security) (bodyReference security) order hdegree
        (columnKernel security order horder selected pattern input) := by
  exact finite_product_embed (primaryLaw security) (bodyReference security) order
    (fun role => (pattern role).val.1.val) (fun role => (pattern role).val.2.val)
    (fun role => roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))
    hdegree (fun role => (pattern role).property)

theorem column_product_dropped (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role)
    (hdegree : order < totalPrimary pattern + totalBody pattern) :
    (∏ role : Role r s, Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) =
      (0 : Family security order) := by
  have h := GlobalRaising.vanishesBelow_prod (primaryLaw security) (bodyReference security) order
    (Finset.univ : Finset (Role r s)) (fun role => (pattern role).val.1.val + (pattern role).val.2.val)
    (fun role => Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) (by
        intro role _ output hsmall
        dsimp only
        rw [Pi.single_eq_of_ne]
        intro hequal
        subst output
        dsimp only at hsmall
        omega)
  rw [Finset.sum_add_distrib] at h
  funext output
  exact h output (by have := output.property; unfold totalPrimary totalBody at hdegree; omega)

theorem patternFamily_column_formula (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    patternFamily security order horder selected pattern kernel =
      ∑ input, inputJoint security kernel input •
        (∏ role : Role r s, (Pi.single (pattern role)
          (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role)) :
            Family security order)) := by
  unfold patternFamily
  split_ifs with hdegree
  · simp_rw [column_product_retained security order horder selected pattern _ hdegree]
    rw [patternKernel_column_formula]
    unfold embed
    funext output
    by_cases hequal : output = embedArity order (totalPrimary pattern) (totalBody pattern) hdegree
    · subst output
      simp
    · simp [Pi.single_eq_of_ne hequal]
  · simp_rw [column_product_dropped security order horder selected pattern _ (Nat.lt_of_not_ge hdegree),
      smul_zero, Finset.sum_const_zero]

/-- Summing finite arity patterns reconstructs the original tensor of
local family-valued channels exactly, before any norm inequality. -/
theorem sum_patternFamily (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    (∑ pattern, patternFamily security order horder selected pattern kernel) =
      ∑ input, inputJoint security kernel input •
        ∏ role : Role r s, roleChannel security order horder selected role (Pi.single (input role) 1) := by
  simp_rw [patternFamily_column_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.smul_sum, ← product_family_arity_expansion]

/-- The Hilbert-friendly arity bundles are exactly the originally defined
actual correction, including both reference weights and both control roles. -/
theorem selectedCorrection_eq_sum_patterns (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    CompleteRaising.selectedCorrection security order horder selected kernel =
      ∑ pattern, patternFamily security order horder selected pattern kernel := by
  rw [sum_patternFamily]
  simp_rw [roleChannel_single, Finset.prod_smul, smul_smul]
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
    (fun _ : Fin s => SafePalette security)).sum_comp, Fintype.sum_prod_type]
  unfold CompleteRaising.selectedCorrection
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  have hweights : (∏ role : Role r s, (roleReference security r s role).weight
      ((Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
        (fun _ : Fin s => SafePalette security)) (colors, centers) role)) =
      (∏ index, (primaryLaw security).weight (colors index)) *
        ∏ index, (bodyReference security).weight (centers index) := by
    simp only [Fintype.prod_sum_type, roleReference, Equiv.prodPiEquivSumPi,
      Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr, RoleInput]
  rw [hweights]
  have hproduct : (∏ role : Role r s, rolePoint security order horder selected role
      ((Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
        (fun _ : Fin s => SafePalette security)) (colors, centers) role)) =
      CompleteRaising.selectedPointProduct security order horder selected colors centers := by
    apply Finset.prod_congr rfl
    intro role _
    cases role <;>
      simp only [rolePoint, CompleteRaising.slotRaised, CompleteRaising.slotLeading,
        Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
        Sum.elim_inl, Sum.elim_inr]
  rw [hproduct]
  congr 1
  change _ = kernel.val colors centers * _
  ring

end
end CurrentAFT.CompleteRaisingPatternIdentity

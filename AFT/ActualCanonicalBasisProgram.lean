import AFT.CanonicalPointBasis
import AFT.ActualPairedMatrixProgram
import AFT.NumericalPairedScore

/-! # Computable canonical columns for the actual primary/body laws -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualInputProbabilityProgram (constant n : ℕ) (beta : ℚ) (primary : Bool) (color : ℕ) : ℚ :=
  probabilityClamp (if primary then actualPrimaryProgram constant n beta color
    else actualBodyCenterProgram constant n beta color)

def actualCanonicalBasisProgram (constant n : ℕ) (beta : ℚ) {colors p b : ℕ}
    (point word : (Fin p ⊕ Fin b) → Fin colors) : ℚ :=
  ∏ slot,((if word slot=point slot then 1 else 0)-
    actualInputProbabilityProgram constant n beta (Sum.elim (fun _ => true) (fun _ => false) slot) (point slot).val)

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

def actualInputProbabilityProgramError (n : ℕ) : ℝ :=
  actualPrimaryProgramError n+actualBodyCenterProgramError n

theorem actualInputProbabilityProgramError_negligible : Negligible actualInputProbabilityProgramError :=
  actualPrimaryProgramError_negligible.add actualBodyCenterProgramError_negligible

theorem actual_input_probability_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ (role : Bool) (color : Fin (Parameters.modulus n)),
      |(actualInputProbabilityProgram constant n (beta n) role color.val : ℝ)-
        (if role then actualPrimaryLaw constant n (beta n) else actualBodyLaw constant n (beta n)).weight color| ≤
        actualInputProbabilityProgramError n := by
  filter_upwards [actual_primary_program_eventually constant hc,actual_body_center_program_eventually constant hc beta hbeta,
    actual_reference_laws_eventually (constant : ℝ) (by exact_mod_cast hc) (fun n => beta n) hbeta,hbeta]
    with n hp hb hl ht role color
  have hp0 : 0 ≤ actualPrimaryProgramError n := (abs_nonneg _).trans (hp (beta n) ht.1 color)
  have hb0 : 0 ≤ actualBodyCenterProgramError n := (abs_nonneg _).trans (hb color)
  let law := if role then actualPrimaryLaw constant n (beta n) else actualBodyLaw constant n (beta n)
  have hl0 : 0 ≤ law.weight color := law.nonneg color
  have hl1 : law.weight color ≤ 1 := by
    simpa only [law.sum_one] using Finset.single_le_sum
      (fun point (_ : point∈Finset.univ) => law.nonneg point) (Finset.mem_univ color)
  apply (probabilityClamp_error _ _ hl0 hl1).trans
  cases role
  · simp only [Bool.false_eq_true,if_false,law]
    change |(actualBodyCenterProgram constant n (beta n) color.val : ℝ)-
      (actualBodyLaw constant n (beta n)).weight color| ≤ _
    rw [hl.2.1]
    exact (hb color).trans (le_add_of_nonneg_left hp0)
  · simp only [law,if_true]
    rw [hl.1]
    exact (hp (beta n) ht.1 color).trans (le_add_of_nonneg_right hb0)

/-- Explicit finite columns avoid testing a real kernel for canonicality.
The exact columns span every actual canonical input, and all their stored
entries have a uniform negligible numerical error in each fixed degree. -/
theorem actual_canonical_basis_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ p b : ℕ,∀ point word : (Fin p ⊕ Fin b) → Fin (Parameters.modulus n),
      |(actualCanonicalBasisProgram constant n (beta n) point word : ℝ)-
        MixedKernel.canonicalPointBasis
          (Sum.elim (fun _ => actualPrimaryLaw constant n (beta n)) (fun _ => actualBodyLaw constant n (beta n))) point word| ≤
        (p+b : ℕ)*actualInputProbabilityProgramError n := by
  filter_upwards [actual_input_probability_program_eventually constant hc beta hbeta]
    with n he p b point word
  let law : (Fin p ⊕ Fin b) → FiniteDist (Fin (Parameters.modulus n)) :=
    Sum.elim (fun _ => actualPrimaryLaw constant n (beta n)) (fun _ => actualBodyLaw constant n (beta n))
  let role : (Fin p ⊕ Fin b) → Bool := Sum.elim (fun _ => true) (fun _ => false)
  have herror : 0 ≤ actualInputProbabilityProgramError n := (abs_nonneg _).trans
    (he true ⟨0,(Parameters.modulus_prime n).pos⟩)
  have hprob (slot) : 0 ≤ (law slot).weight (point slot) ∧ (law slot).weight (point slot) ≤ 1 := by
    refine ⟨(law slot).nonneg _,?_⟩
    simpa only [(law slot).sum_one] using Finset.single_le_sum
      (fun color (_ : color∈Finset.univ) => (law slot).nonneg color) (Finset.mem_univ (point slot))
  have happrox (slot) : 0 ≤ (actualInputProbabilityProgram constant n (beta n) (role slot) (point slot).val : ℝ) ∧
      (actualInputProbabilityProgram constant n (beta n) (role slot) (point slot).val : ℝ) ≤ 1 :=
    probabilityClamp_bounds _
  have hdelta (slot) (value : ℝ) (hv : 0 ≤ value ∧ value ≤ 1) :
      |(if word slot=point slot then 1 else 0)-value| ≤ 1 := by
    split_ifs <;> exact abs_le.mpr (by constructor <;> linarith [hv.1,hv.2])
  have hlocal (slot) : |((if word slot=point slot then 1 else 0)-
      (actualInputProbabilityProgram constant n (beta n) (role slot) (point slot).val : ℝ))-
      ((if word slot=point slot then 1 else 0)-(law slot).weight (point slot))| ≤ actualInputProbabilityProgramError n := by
    rw [sub_sub_sub_cancel_left,abs_sub_comm]
    cases slot <;> exact he _ _
  have hh := abs_prod_sub_prod_le Finset.univ
    (fun slot => (if word slot=point slot then 1 else 0)-
      (actualInputProbabilityProgram constant n (beta n) (role slot) (point slot).val : ℝ))
    (fun slot => (if word slot=point slot then 1 else 0)-(law slot).weight (point slot))
    1 (actualInputProbabilityProgramError n) (by norm_num) herror
    (fun slot _ => hdelta slot _ (happrox slot)) (fun slot _ => hdelta slot _ (hprob slot)) (fun slot _ => hlocal slot)
  have hcast : (actualCanonicalBasisProgram constant n (beta n) point word : ℝ)=
      ∏ slot,((if word slot=point slot then 1 else 0)-
        (actualInputProbabilityProgram constant n (beta n) (role slot) (point slot).val : ℝ)) := by
    simp only [actualCanonicalBasisProgram,Rat.cast_prod,Rat.cast_sub]
    apply Finset.prod_congr rfl
    intro slot _
    split_ifs <;> simp only [Rat.cast_one,Rat.cast_zero,role]
  have hbasis : MixedKernel.canonicalPointBasis law point word =
      ∏ slot, ((if word slot = point slot then 1 else 0) - (law slot).weight (point slot)) := by
    unfold MixedKernel.canonicalPointBasis
    apply Finset.prod_congr rfl
    intro slot _
    split_ifs <;> rfl
  rw [hcast, hbasis]
  simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin,
    one_pow,mul_one] using hh

end
end AFT.V7Calibration

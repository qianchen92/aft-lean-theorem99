import AFT.ActualReferenceAtomProgram
import AFT.NumericalPairedScore

/-! # Finite computation of actual selected centered coefficients -/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- The input mass can be a signed joint channel; no product assumption
is made, and only the requested selected output coordinates are stored. -/
def rationalSelectedCoefficient (constant n : ℕ) (beta : ℚ) {colors slots : ℕ}
    (mass : (Fin slots → Fin colors) → ℚ) (selected : Finset (Fin slots))
    (output : selected → Fin colors) : ℚ :=
  ∑ input,mass input*∏ slot : selected,
    V7Calibration.actualReferenceAtomProgram constant n beta (input slot).val (output slot).val

noncomputable section
open V7Calibration Filter
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000

/-- A finite signed sum of selected products is stable uniformly in all
unselected coordinates. -/
theorem finite_sum_product_perturbation {Input Slot : Type*} [Fintype Input] [Fintype Slot]
    (mass approximateMass : Input → ℝ) (atom approximateAtom : Input → Slot → ℝ)
    (bound massBound atomError massError : ℝ)
    (hb : 1 ≤ bound) (hm : 0 ≤ massBound) (ha : 0 ≤ atomError) (he : 0 ≤ massError)
    (hvalue : ∀ input,|mass input| ≤ massBound) (herror : ∀ input,|approximateMass input-mass input| ≤ massError)
    (htrue : ∀ input slot,|atom input slot| ≤ bound)
    (happrox : ∀ input slot,|approximateAtom input slot| ≤ bound)
    (hatom : ∀ input slot,|approximateAtom input slot-atom input slot| ≤ atomError) :
    |(∑ input,approximateMass input*∏ slot,approximateAtom input slot)-
      (∑ input,mass input*∏ slot,atom input slot)| ≤ 
      (Fintype.card Input : ℝ)*(massError+massBound*Fintype.card Slot*atomError)*bound^Fintype.card Slot := by
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _  ≤  ∑ _input : Input,(massError+massBound*Fintype.card Slot*atomError)*bound^Fintype.card Slot := by
      apply Finset.sum_le_sum
      intro input _
      have hp := abs_prod_le_power Finset.univ (approximateAtom input) bound (zero_le_one.trans hb)
        (fun slot _ => happrox input slot)
      have hd := abs_prod_sub_prod_le Finset.univ (approximateAtom input) (atom input) bound atomError hb ha
        (fun slot _ => happrox input slot) (fun slot _ => htrue input slot) (fun slot _ => hatom input slot)
      simp only [Finset.card_univ] at hp hd
      rw [show approximateMass input*(∏ slot,approximateAtom input slot)-mass input*(∏ slot,atom input slot)=
        (approximateMass input-mass input)*(∏ slot,approximateAtom input slot)+
          mass input*((∏ slot,approximateAtom input slot)-(∏ slot,atom input slot)) by ring]
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      exact (add_le_add (mul_le_mul (herror input) hp (abs_nonneg _) he)
        (mul_le_mul (hvalue input) hd (abs_nonneg _) hm)).trans_eq (by ring)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

/-- Every atom and denominator estimate is instantiated with the actual
model; only the supplied local mass approximation remains to be composed. -/
theorem actual_selected_coefficient_program_eventually (constant : ℕ) (hc : 1 ≤ constant) (beta : ℕ → ℚ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ (beta n : ℝ) ∧
      (beta n : ℝ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ slots : ℕ,
      ∀ mass : (Fin slots → Fin (Parameters.modulus n)) → ℝ,
      ∀ approximateMass : (Fin slots → Fin (Parameters.modulus n)) → ℚ,
      ∀ massBound massError : ℝ,0 ≤ massBound →0 ≤ massError →
      (∀ input,|mass input| ≤ massBound) →
      (∀ input,|(approximateMass input : ℝ)-mass input| ≤ massError) →
      ∀ (selected : Finset (Fin slots)) (output : selected → Fin (Parameters.modulus n)),
      |(rationalSelectedCoefficient constant n (beta n) approximateMass selected output : ℝ)-
        LocalTensors.referenceRestrictedComponent
          (fun _ : Fin slots => actualPrimaryLaw constant n (beta n))
          (fun _ : Fin slots => actualReferenceLaw constant n (beta n)) mass selected output| ≤ 
        (Parameters.modulus n : ℝ)^slots*
          (massError+massBound*selected.card*actualPrimaryReciprocalProgramError n)*
          (16*(n : ℝ)^40)^selected.card := by
  filter_upwards [actual_reference_atom_program_eventually constant hc beta hbeta,eventually_ge_atTop 2]
    with n hatoms hn slots mass approximateMass massBound massError hm he hvalue herror selected output
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hb : 1 ≤ 16*(n : ℝ)^40 := by have hh := one_le_pow₀ hn1 (n:=40);linarith only [hh]
  have ha : 0 ≤ actualPrimaryReciprocalProgramError n := (abs_nonneg _).trans
    (hatoms ⟨0,(Parameters.modulus_prime n).pos⟩ ⟨0,(Parameters.modulus_prime n).pos⟩).2.2
  simp only [rationalSelectedCoefficient,Rat.cast_sum,Rat.cast_mul,Rat.cast_prod,
    LocalTensors.referenceRestrictedComponent]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow] using
    finite_sum_product_perturbation mass (fun input => (approximateMass input : ℝ))
      (fun input (slot : selected) => MixedKernel.referenceAtom (actualPrimaryLaw constant n (beta n))
        (actualReferenceLaw constant n (beta n)) (input slot) (output slot))
      (fun input (slot : selected) => (actualReferenceAtomProgram constant n (beta n)
        (input slot).val (output slot).val : ℝ))
      (16*(n : ℝ)^40) massBound (actualPrimaryReciprocalProgramError n) massError hb hm ha he hvalue herror
      (fun input slot => (hatoms (input slot) (output slot)).1)
      (fun input slot => (hatoms (input slot) (output slot)).2.1)
      (fun input slot => (hatoms (input slot) (output slot)).2.2)

end
end AFT.RationalNumerics

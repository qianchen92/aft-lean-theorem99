import CurrentAFT.LocalCoefficientEvaluation
import CurrentAFT.IndependentPairedReference

/-!
# Actual finite normalization of a complete local paired polynomial

The positive and signed coefficients are extracted from the concrete
four-output laws. Their quotient is formed inside the current truncated
canonical algebra by its proved finite background inverse. Evaluation is
the actual polynomial algebra homomorphism, so the quotient identity is
an exact physical PGF identity modulo the stated degree cutoff.
-/

namespace CurrentAFT.NormalizedLocalPolynomial

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

def completeFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  (∑ word, mass word) • (1 : Family security order) +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      selectedFamily security order mass selected

theorem completeFamily_zeroArity (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    completeFamily security order mass (zeroArity order) =
      (∑ word, mass word) • (1 : Family security order) (zeroArity order) := by
  have hselected (selected : Finset (Fin 4)) (hnonempty : selected ≠ ∅) :
      selectedFamily security order mass selected (zeroArity order) = 0 := by
    unfold selectedFamily
    split_ifs with hdegree
    · rw [Pi.single_eq_of_ne]
      intro hequal
      have hcard := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
      change 0 = selected.card at hcard
      exact hnonempty (Finset.card_eq_zero.mp hcard.symm)
    · rfl
  unfold completeFamily
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  have hzero : (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      selectedFamily security order mass selected (zeroArity order)) = 0 := by
    apply Finset.sum_eq_zero
    intro selected hselectedmem
    exact hselected selected (Finset.mem_erase.mp hselectedmem).1
  rw [hzero, add_zero]

theorem completeFamily_image (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (completeFamily security order mass) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight mass) := by
  unfold completeFamily
  simp only [map_add, map_smul, map_one, map_sum, selectedFamily_image]
  have hexpand := RepresentedPolynomial.centeredGeneratingLinear_reference_expansion (primaryLaw security)
    (LocalReferenceEnergy.uniformReference security) (primaryReference_positive security) mass
  rw [hexpand]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin 4)))
    (RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
      (LocalReferenceEnergy.uniformReference security) mass) (Finset.mem_univ ∅)
  rw [RepresentedPolynomial.referenceCoefficientForm_empty] at hsplit
  rw [← hsplit, map_add, map_sum]
  have hconstant : TruncatedOutput.quotientMap order (MvPolynomial.C (∑ word, mass word)) =
      (∑ word, mass word) • (1 : TruncatedOutput.Polynomial (Palette security) order) := by
    rw [Algebra.smul_def, mul_one]
    exact (TruncatedOutput.quotientMap order).commutes _
  rw [hconstant, add_comm]

def positiveFamily (security order : ℕ) (law : FiniteDist (Fin 4 → Palette security)) : Family security order :=
  completeFamily security order law.weight

theorem positiveFamily_zeroArity (security order : ℕ) (law : FiniteDist (Fin 4 → Palette security)) :
    positiveFamily security order law (zeroArity order) = (1 : Family security order) (zeroArity order) := by
  rw [positiveFamily, completeFamily_zeroArity, law.sum_one, one_smul]

def normalizedFamily (security order : ℕ) (positive : FiniteDist (Fin 4 → Palette security))
    (signed : (Fin 4 → Palette security) → ℝ) : Family security order :=
  completeFamily security order signed *
    backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order positive)

theorem normalizedFamily_mul_positive (security order : ℕ) (positive : FiniteDist (Fin 4 → Palette security))
    (signed : (Fin 4 → Palette security) → ℝ) :
    normalizedFamily security order positive signed * positiveFamily security order positive =
      completeFamily security order signed := by
  unfold normalizedFamily
  rw [mul_assoc, backgroundInverse_mul (primaryLaw security) (bodyReference security) order
    (positiveFamily security order positive) (positiveFamily_zeroArity security order positive), mul_one]

theorem normalizedFamily_physical_identity (security order : ℕ) (positive : FiniteDist (Fin 4 → Palette security))
    (signed : (Fin 4 → Palette security) → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (normalizedFamily security order positive signed) *
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight positive.weight) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight signed) := by
  rw [← completeFamily_image security order positive.weight bodyForms hbody,
    ← completeFamily_image security order signed bodyForms hbody]
  change evaluation security order bodyForms hbody (normalizedFamily security order positive signed) *
      evaluation security order bodyForms hbody (positiveFamily security order positive) = _
  rw [← map_mul, normalizedFamily_mul_positive]

def independentPositiveLaw (security : ℕ) : FiniteDist (Fin 4 → Palette security) :=
  (PhysicalSynthesis.groupLaw security).mix (IndependentPairedReference.independentControlLaw security)

/-- The actual independent-root local normalized response. Both its
positive denominator and signed numerator come from the same complete
four-coordinate reference experiment. -/
def independentNormalized (security order : ℕ) (score : Palette security → ℝ) : Family security order :=
  normalizedFamily security order (independentPositiveLaw security)
    (IndependentPairedReference.independentSignedMass security score)

theorem independentNormalized_physical_identity (security order : ℕ) (score : Palette security → ℝ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    evaluation security order bodyForms hbody (independentNormalized security order score) *
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
          (independentPositiveLaw security).weight) =
      TruncatedOutput.quotientMap order
        (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
          (IndependentPairedReference.independentSignedMass security score)) :=
  normalizedFamily_physical_identity security order _ _ bodyForms hbody

end

end CurrentAFT.NormalizedLocalPolynomial

import CurrentAFT.CompleteRaising
import CurrentAFT.PointPolynomial
import CurrentAFT.BodyChannelEvaluation

/-! # Physical image of the complete independent-root normalized response

The leading term is reconstructed from the original joint kernel. The
remaining terms are exactly the two-role raising operator. No injectivity
of physical polynomial evaluation is assumed.
-/
namespace CurrentAFT.CompleteRaisingEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising CompleteRaising LeadingEvaluation PointPolynomial
  LocalCoefficientEvaluation BackgroundEvaluation PrimaryMassFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

theorem densityPolynomial_one_atom {Color Variable : Type*} [Fintype Color]
    (law : FiniteDist Color) (forms : Color → MvPolynomial Variable ℝ) (source : Color) :
    densityPolynomial law forms 1 (oneWordProfile (Hoeffding.centeredAtom law source)) =
      atomForm law forms source := by
  unfold densityPolynomial atomForm
  simp only [oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word : Fin 1 → Color =>
      MvPolynomial.C (law.weight (word 0) * Hoeffding.centeredAtom law source (word 0)) * forms (word 0))).symm

theorem primaryPoint_image (security order : ℕ) (horder : 1 ≤ order)
    (source : ActualControls.Palette security) :
    BackgroundEvaluation.evaluation security order (primaryPoint security order horder source) =
      TruncatedOutput.quotientMap order (atomForm (primaryLaw security) (primaryForm security) source) := by
  change LeadingEvaluation.familyHom _ _ _ _ (primaryForm_homogeneous security) (bodyForm_homogeneous security) _ (primaryFamily _ _ _ _ _ _) = _
  rw [BackgroundFirstEvaluation.primaryFamily_generic_image]
  change TruncatedOutput.quotientMap order
    (densityPolynomial _ _ 1 (oneWordProfile (Hoeffding.centeredAtom _ source))) = _
  rw [densityPolynomial_one_atom]

theorem bodyPoint_image (security order : ℕ) (horder : 1 ≤ order)
    (source : SafePalette security) :
    BackgroundEvaluation.evaluation security order (bodyPoint security order horder source) =
      TruncatedOutput.quotientMap order (atomForm (bodyReference security) (bodyForm security) source) := by
  change LeadingEvaluation.familyHom _ _ _ _ (primaryForm_homogeneous security) (bodyForm_homogeneous security) _ (bodyFamily _ _ _ _ _ _) = _
  rw [BodyChannelEvaluation.bodyFamily_generic_image, densityPolynomial_one_atom]

theorem emptyPointProduct_image (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    BackgroundEvaluation.evaluation security order
      (CompleteRaising.selectedPointProduct security order horder ∅ colors centers) =
      TruncatedOutput.quotientMap order
        ((∏ index, atomForm (primaryLaw security) (primaryForm security) (colors index)) *
          ∏ index, atomForm (bodyReference security) (bodyForm security) (centers index)) := by
  simp [CompleteRaising.selectedPointProduct,
    slotLeading, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, map_mul, map_prod,
    primaryPoint_image, bodyPoint_image]

theorem emptyCorrection_image (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    BackgroundEvaluation.evaluation security order
      (CompleteRaising.selectedCorrection security order horder ∅ kernel) =
      TruncatedOutput.quotientMap order (kernelPolynomial (primaryLaw security) (bodyReference security)
        (primaryForm security) (bodyForm security) kernel.val) := by
  rw [joint_polynomial_reconstruction _ _ (primaryReference_positive security) (bodyReference_positive security)]
  simp only [CompleteRaising.selectedCorrection, map_sum, map_smul, emptyPointProduct_image]

def normalizedSlot (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => NormalizedLocalPolynomial.independentNormalized security order
    (primaryAtom security (colors index)).val)
    (fun index => OrdinaryRaising.normalizedFamily security order horder
      (bodyAtom security (centers index)).val (bodyAtom security (centers index)).property)

theorem normalizedSlot_eq (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security)
    (slot : Fin r ⊕ Fin s) :
    normalizedSlot security order horder colors centers slot =
      slotLeading security order horder colors centers slot + slotRaised security order horder colors centers slot := by
  cases slot with
  | inl index =>
    change NormalizedLocalPolynomial.independentNormalized security order _ =
      primaryPoint security order horder _ + raisedPoint security order horder _
    change _ = primaryEmbeddingLinear security order horder _ +
      (NormalizedLocalPolynomial.independentNormalized security order _ - primaryEmbeddingLinear security order horder _)
    abel
  | inr index =>
    exact OrdinaryRaising.normalizedFamily_eq_leading_add security order horder _ _

theorem prod_normalizedSlot (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    (∏ slot, normalizedSlot security order horder colors centers slot) =
      ∑ selected, CompleteRaising.selectedPointProduct security order horder selected colors centers := by
  simp_rw [normalizedSlot_eq, add_comm (slotLeading security order horder colors centers _)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro selected _
  simp [CompleteRaising.selectedPointProduct, Finset.prod_ite, ← Finset.mem_compl]

def normalizedJoint (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ colors, ∑ centers,
    ((∏ index, (primaryLaw security).weight (colors index)) *
      (∏ index, (bodyReference security).weight (centers index)) * kernel.val colors centers) •
        ∏ slot, normalizedSlot security order horder colors centers slot

theorem normalizedJoint_expansion (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    normalizedJoint security order horder kernel =
      ∑ selected, CompleteRaising.selectedCorrection security order horder selected kernel := by
  unfold normalizedJoint CompleteRaising.selectedCorrection
  simp_rw [prod_normalizedSlot, Finset.smul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext colors
    rw [Finset.sum_comm]

theorem normalizedJoint_eq (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    normalizedJoint security order horder kernel =
      CompleteRaising.selectedCorrection security order horder ∅ kernel +
        CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel := by
  rw [normalizedJoint_expansion]
  simp only [CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  change _ = CompleteRaising.selectedCorrection security order horder ∅ kernel +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r ⊕ Fin s))).erase ∅,
      CompleteRaising.selectedCorrection security order horder selected kernel
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ ∅)).symm

def normalizedResponse (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    Family security order :=
  ∑ arity : TruncatedArity order, normalizedJoint security order horder (family arity)

/-- Literal physical image of all normalized local factors, retaining the
original joint input coefficient and both actual reference laws. -/
theorem normalizedResponse_image (security order : ℕ) (horder : 1 ≤ order)
    (family : Family security order) :
    BackgroundEvaluation.evaluation security order (normalizedResponse security order horder family) =
      BackgroundEvaluation.evaluation security order
        (family + CompleteRaising.raisingLinear security order horder family) := by
  unfold normalizedResponse
  simp_rw [map_sum, normalizedJoint_eq, map_add, emptyCorrection_image]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · exact (LeadingEvaluation.familyLinear_apply _ _ _ _ _ family).symm
  · change _ = BackgroundEvaluation.evaluation security order
      (∑ arity : TruncatedArity order,
        CompleteRaising.homogeneousCorrectionLinear security order horder
          arity.val.1.val arity.val.2.val (family arity))
    rw [map_sum]

end
end CurrentAFT.CompleteRaisingEvaluation

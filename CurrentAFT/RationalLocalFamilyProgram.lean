import CurrentAFT.RationalPrimaryColumnProgram
import CurrentAFT.RationalFamilyProductProgram

/-! # Explicit point tables of the centered primary numerator family

Each of the fifteen nonempty physical slot subsets is inserted in its
actual arity. The constant and all body fibers are set to zero, as proved
for the centered primary experiment.
-/
namespace CurrentAFT.RationalLocalFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def insertSelected {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (selected : Finset (Fin 4)) (value : (Fin selected.card → Primary) → Scalar) :
    RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors _ => if hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val then
    value (colors ∘ finCongr hmatch.1) else 0

def numerator (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    insertSelected order selected
      (RationalPrimaryColumnProgram.current security bits compensatorRoot attachmentRoot primaryColor selected)
        arity colors centers

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem insertSelected_actual (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    insertSelected order selected
      (fun word => (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (LocalCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold insertSelected LocalCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = LocalCoefficientFamily.selectedArity order selected hdegree := by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          exact hmatch.1.symm
        · apply Fin.ext
          exact hmatch.2.symm
      subst arity
      rw [dif_pos hmatch, Pi.single_eq_same]
      have hcenters : centers = (Fin.elim0 : Fin 0 → SafePalette security) :=
        @Subsingleton.elim (Fin 0 → SafePalette security) inferInstance centers Fin.elim0
      rw [hcenters]
      rfl
    · have harity : arity ≠ LocalCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : TruncatedArity order =>
          canonicalKernels (primaryLaw security) (bodyReference security) point.val.1.val point.val.2.val) harity
        (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl

theorem completeFamily_zero_mass (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    (LocalRaisingLinear.completeFamilyLinear security order mass arity).val colors centers =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        insertSelected order selected
          (fun word => (LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
          arity colors centers := by
  change (NormalizedLocalPolynomial.completeFamily security order mass arity).val colors centers = _
  unfold NormalizedLocalPolynomial.completeFamily
  rw [hmass, zero_smul, zero_add]
  simp only [Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (insertSelected_actual security order mass selected arity colors centers).symm

theorem primaryMassAt_zero (security : ℕ) (roots : RootTaggedSelected.RootPair security) (primaryColor : Palette security) :
    (∑ word, RootMassColumns.primaryMassAt security roots
      (centerLinear (primaryLaw security) (Pi.single primaryColor 1)) word) = 0 := by
  simp only [RationalRootMassProgram.primaryMassAt_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scalar _
  rw [← Finset.mul_sum, FixedPairedFirst.fixedMass_sum, center_mean, mul_zero, mul_zero]

theorem primaryError_nonneg (security degree : ℕ) :
    0 ≤ RationalPrimaryColumnProgram.errorConstant security degree := by
  unfold RationalPrimaryColumnProgram.errorConstant RationalPrimaryColumnProgram.massErrorConstant
    RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError RationalCoefficientExtraction.atomErrorConstant
    RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
    RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    RationalTensorInverseProgram.tensorErrorConstant
  positivity [RationalTensorInverseProgram.actualBound_nonneg security,
    RationalTensorInverseProgram.errorConstant_nonneg security, RationalTensorInverseProgram.factorBound_one_le security]

theorem insertSelected_error (order : ℕ) (selected : Finset (Fin 4)) (security : ℕ)
    (computed : (Fin selected.card → ℕ) → ℚ) (actual : (Fin selected.card → Palette security) → ℝ)
    (error : ℝ) (he : 0 ≤ error)
    (hvalue : ∀ word, |(computed (fun index => (word index).val) : ℝ) - actual word| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(insertSelected order selected computed arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℝ) -
      insertSelected order selected actual arity colors centers| ≤ error := by
  unfold insertSelected
  split_ifs with hmatch
  · exact hvalue (colors ∘ finCongr hmatch.1)
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using he

def numeratorErrorConstant (security : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    RationalPrimaryColumnProgram.errorConstant security selected.card

/-- A simultaneous point-table approximation of the actual complete
centered primary numerator family, including all retained degrees. -/
theorem numerator_error (security bits order : ℕ) (roots : RootTaggedSelected.RootPair security)
    (primaryColor : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(numerator security bits order roots.1.val roots.2.val primaryColor.val arity
        (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (LocalRaisingLinear.completeFamilyLinear security order
        (RootMassColumns.primaryMassAt security roots (centerLinear (primaryLaw security) (Pi.single primaryColor 1)))
          arity).val colors centers| ≤
      numeratorErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsum : (numerator security bits order roots.1.val roots.2.val primaryColor.val arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      (insertSelected order selected
        (RationalPrimaryColumnProgram.current security bits roots.1.val roots.2.val primaryColor.val selected)
        arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold numerator
    simp only [Rat.cast_sum]
    apply Finset.sum_congr (by ext; simp)
    intro selected _
    rfl
  rw [hsum, completeFamily_zero_mass security order _ (primaryMassAt_zero security roots primaryColor)]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        RationalPrimaryColumnProgram.errorConstant security selected.card * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact insertSelected_error order selected security _ _ _ (by positivity [primaryError_nonneg security selected.card])
        (fun word => RationalPrimaryColumnProgram.current_error security bits roots primaryColor selected hfirst hprecision hbudget
          word Fin.elim0) arity colors centers
    _ = _ := by rw [← Finset.sum_mul]; rfl

end
end CurrentAFT.RationalLocalFamilyProgram

import CurrentAFT.RationalLegCoefficientExtraction
import CurrentAFT.RootLegCoefficientLinear
import CurrentAFT.RationalFamilyPowerProgram
import CurrentAFT.RootLegNormalized

/-! Literal selected-slot tables for the complete actual three-output leg. -/
namespace CurrentAFT.RationalLegFamilyTable
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def insertSelected {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (selected : Finset (Fin 3)) (value : (Fin selected.card → Primary) → Scalar) :
    RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors _ => if hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val then
    value (colors ∘ finCongr hmatch.1) else 0

def higher (security bits order : ℕ) (mass : (Fin 3 → ℕ) → ℚ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order := fun arity colors centers =>
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits mass selected) arity colors centers

def positive (security bits order : ℕ) (mass : (Fin 3 → ℕ) → ℚ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order := fun arity colors centers =>
  RationalFamilyProductProgram.unit order arity colors centers +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits mass selected) arity colors centers

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem insertSelected_actual (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    insertSelected order selected
      (fun word => (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val word Fin.elim0)
        arity colors centers =
      (RootLegCoefficientFamily.selectedFamily security order mass selected arity).val colors centers := by
  unfold insertSelected RootLegCoefficientFamily.selectedFamily
  by_cases hdegree : selected.card ≤ order
  · rw [dif_pos hdegree]
    by_cases hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val
    · have harity : arity = RootLegCoefficientFamily.selectedArity order selected hdegree := by
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
    · have harity : arity ≠ RootLegCoefficientFamily.selectedArity order selected hdegree := by
        intro hequal
        apply hmatch
        subst arity
        exact ⟨rfl, rfl⟩
      rw [dif_neg hmatch]
      have hzero := Pi.single_eq_of_ne
        (M := fun point : TruncatedArity order =>
          canonicalKernels (primaryLaw security) (bodyReference security) point.val.1.val point.val.2.val) harity
        (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
      rw [hzero]
      rfl
  · rw [dif_neg hdegree]
    have hmatch : ¬(selected.card = arity.val.1.val ∧ 0 = arity.val.2.val) := by
      intro h
      have hbound := arity.property
      omega
    rw [dif_neg hmatch]
    rfl

theorem insertSelected_error (order : ℕ) (selected : Finset (Fin 3)) (security : ℕ)
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

def higherError (security : ℕ) (massBound massError : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    RationalLegCoefficientExtraction.normalizedError security selected.card massBound massError

theorem normalizedError_nonneg (security degree : ℕ) (massBound massError : ℝ)
    (hbound : 0 ≤ massBound) (herror : 0 ≤ massError) :
    0 ≤ RationalLegCoefficientExtraction.normalizedError security degree massBound massError := by
  unfold RationalLegCoefficientExtraction.normalizedError RationalLegCoefficientExtraction.extractionBound
    RationalLegCoefficientExtraction.extractionError RationalLegCoefficientExtraction.atomErrorConstant
    RationalTensorInverseProgram.tensorErrorConstant RationalRootMassProgram.primaryErrorConstant
  positivity [RationalTensorInverseProgram.actualBound_nonneg security,
    RationalTensorInverseProgram.errorConstant_nonneg security, RationalTensorInverseProgram.factorBound_one_le security]

theorem higher_error (security bits order : ℕ) (computed : (Fin 3 → ℕ) → ℚ)
    (mass : (Fin 3 → Palette security) → ℝ) (massBound massError : ℝ)
    (hbound : 0 ≤ massBound) (herror : 0 ≤ massError)
    (hmass : ∀ word, |mass word| ≤ massBound)
    (hdiff : ∀ word : Fin 3 → Palette security,
      |(computed (fun index => (word index).val) : ℝ) - mass word| ≤ massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(higher security bits order computed arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegCoefficientLinear.higherFamilyLinear security order mass arity).val colors centers| ≤
      higherError security massBound massError * (1 / (2 : ℝ)^bits) := by
  have hsum : (higher security bits order computed arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
        (insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits computed selected)
          arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    unfold higher
    simp only [Rat.cast_sum]
  rw [hsum, RootLegCoefficientLinear.higherFamilyLinear_apply]
  simp only [RootLegCoefficientFamily.higherFamily, Finset.sum_apply, Submodule.coe_sum]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
        RationalLegCoefficientExtraction.normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      rw [← insertSelected_actual security order mass selected arity colors centers]
      exact insertSelected_error order selected security _ _ _
        (by positivity [normalizedError_nonneg security selected.card massBound massError hbound herror])
        (fun word => RationalLegCoefficientExtraction.selectedKernel_error security bits computed mass selected massBound massError
          hbound herror hmass hdiff hfirst hprecision hbudget word Fin.elim0) arity colors centers
    _ = _ := by unfold higherError; rw [Finset.sum_mul]

theorem positive_data (security order : ℕ) (law : FiniteDist (Fin 3 → Palette security))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    (RootLegNormalized.positiveFamily security order law arity).val colors centers =
      RationalFamilyProductProgram.unit order arity colors centers +
        ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
          insertSelected order selected
            (fun word => (RootLegCoefficientFamily.selectedKernel security selected.card law.weight selected (by simp)).val word Fin.elim0)
            arity colors centers := by
  unfold RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
  rw [FiniteDist.sum_one, one_smul]
  simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_apply, Submodule.coe_sum]
  have hunit := congrFun (congrFun (congrFun
    (RationalFamilyProductProgram.unit_actual (primaryLaw security) (bodyReference security) order) arity) colors) centers
  rw [← hunit]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro selected _
  exact (insertSelected_actual security order law.weight selected arity colors centers).symm

def positiveError (security : ℕ) (massError : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
    RationalLegCoefficientExtraction.normalizedError security selected.card 1 massError

theorem positive_error (security bits order : ℕ) (computed : (Fin 3 → ℕ) → ℚ)
    (law : FiniteDist (Fin 3 → Palette security)) (massError : ℝ) (herror : 0 ≤ massError)
    (hdiff : ∀ word : Fin 3 → Palette security,
      |(computed (fun index => (word index).val) : ℝ) - law.weight word| ≤ massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(positive security bits order computed arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) -
      (RootLegNormalized.positiveFamily security order law arity).val colors centers| ≤
      positiveError security massError * (1 / (2 : ℝ)^bits) := by
  rw [positive_data]
  have hcast : (positive security bits order computed arity
      (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) =
      RationalFamilyProductProgram.unit order arity colors centers +
        ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
          (insertSelected order selected (RationalLegCoefficientExtraction.selectedKernel security bits computed selected)
            arity (fun index => (colors index).val) (fun index => (centers index).val.val) : ℝ) := by
    simp only [positive, Rat.cast_add, Rat.cast_sum]
    congr 1
    unfold RationalFamilyProductProgram.unit
    split_ifs <;> norm_num
  rw [hcast, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
        RationalLegCoefficientExtraction.normalizedError security selected.card 1 massError * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro selected _
      exact insertSelected_error order selected security _ _ _
        (by positivity [normalizedError_nonneg security selected.card 1 massError (by norm_num) herror])
        (fun word => RationalLegCoefficientExtraction.selectedKernel_error security bits computed law.weight selected 1 massError
          (by norm_num) herror (fun word => by rw [abs_of_nonneg (law.nonneg word)]; exact law.atom_le_one word)
          hdiff hfirst hprecision hbudget word Fin.elim0) arity colors centers
    _ = _ := by unfold positiveError; rw [Finset.sum_mul]


end
end CurrentAFT.RationalLegFamilyTable

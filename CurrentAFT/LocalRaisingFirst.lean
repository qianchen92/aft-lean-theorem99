import CurrentAFT.NormalizedLocalPolynomial
import CurrentAFT.BackgroundFamilies
import AFT.ReferenceSingletonComponent

/-! # The genuine first coefficient and degree raising of the actual local response -/

namespace CurrentAFT.LocalRaisingFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial BackgroundFamilies
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected :=
  Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem selectedDensity_singleton (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (slot : Fin 4) (hdegree : Fintype.card ({slot} : Finset (Fin 4)) = 1) (color : Palette security) :
    selectedDensity security 1 mass {slot} hdegree (fun _ => color) =
      ((∑ word, if word slot = color then mass word else 0) -
        (LocalReferenceEnergy.uniformReference security).weight color * ∑ word, mass word) /
          (primaryLaw security).weight color := by
  unfold selectedDensity
  rw [LocalTensors.referenceRestrictedComponent_singleton]
  rfl

theorem tensorInverse_one (security : ℕ) (density : (Fin 1 → Palette security) → ℝ)
    (color : Palette security) :
    PrimaryTensorInverse.tensorInverse security 1 density (fun _ => color) =
      PrimaryTensorInverse.densityInverse security (fun input => density (fun _ => input)) color := by
  change PrimaryTensorInverse.densityInverse security (fun input => density (Fin.cons input Fin.elim0)) color = _
  have hfun : (fun input => density (Fin.cons input Fin.elim0)) =
      (fun input => density (fun _ => input)) := by
    funext input
    congr 1
    funext index
    have hi : index = 0 := Fin.eq_zero index
    subst index
    rfl
  exact congrArg (fun f => PrimaryTensorInverse.densityInverse security f color) hfun

theorem selectedKernel_one (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = 1)
    (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security) :
    (selectedKernel security 1 mass selected hdegree).val colors centers =
      normalizedSelectedDensity security 1 mass selected hdegree colors := by
  change symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
    normalizedSelectedDensity security 1 mass selected hdegree colors) colors centers = _
  rw [symmetrize_of_symmetric]
  intro primaryOrder bodyOrder input _
  congr 1
  funext index
  have hi : primaryOrder index = index := Subsingleton.elim _ _
  simp only [Function.comp_apply, hi]

theorem selectedFamily_singleton_primary (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (slot : Fin 4) (color : Palette security) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass {slot}) color =
      PrimaryTensorInverse.densityInverse security (fun input =>
        ((∑ word, if word slot = input then mass word else 0) -
          (LocalReferenceEnergy.uniformReference security).weight input * ∑ word, mass word) /
            (primaryLaw security).weight input) color := by
  have hsingle : selectedFamily security order mass {slot} =
      Pi.single (primaryArity order horder) (selectedKernel security 1 mass {slot} (by simp)) := by
    unfold selectedFamily
    rw [dif_pos (by simpa using horder)]
    unfold selectedArity primaryArity
    rfl
  rw [hsingle]
  unfold primaryCoefficient
  rw [Pi.single_eq_same]
  rw [selectedKernel_one]
  unfold normalizedSelectedDensity
  change PrimaryTensorInverse.densityInverse security
    (fun input => selectedDensity security 1 mass {slot} _ (Fin.cons input Fin.elim0)) color = _
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  have hword : Fin.cons input Fin.elim0 = (fun _ : Fin 1 => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword]
  exact selectedDensity_singleton security mass slot _ input

def primaryProjection {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order) :
    KernelFamily primary body order →ₗ[ℝ] (Primary → ℝ) where
  toFun := primaryCoefficient primary body order horder
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primaryProjection_one {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order) :
    primaryProjection primary body order horder 1 = 0 := by
  funext color
  change ((familyUnit primary body order) (primaryArity order horder)).val (fun _ => color) Fin.elim0 = 0
  unfold familyUnit
  rw [Pi.single_eq_of_ne]
  · rfl
  · intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
    change 1 = 0 at h
    omega

theorem selectedFamily_primary_nonone (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4)) (hcard : selected.card ≠ 1) :
    primaryProjection (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass selected) = 0 := by
  funext color
  unfold primaryProjection primaryCoefficient selectedFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    · rfl
    · intro hequal
      have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
      exact hcard h.symm
  · rfl

private theorem sum_nonempty_singletons {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (term : Finset Slot → ℝ) (hzero : ∀ selected, selected.card ≠ 1 → term selected = 0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected) =
      ∑ slot, term {slot} := by
  let singles := (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card = 1)
  have hsubset : singles ⊆ (Finset.univ : Finset (Finset Slot)).erase ∅ := by
    intro selected hselected
    apply Finset.mem_erase.mpr
    constructor
    · intro hequal
      have hcard := (Finset.mem_filter.mp hselected).2
      rw [hequal, Finset.card_empty] at hcard
      omega
    · exact Finset.mem_univ _
  have hreduce : (∑ selected ∈ singles, term selected) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected := by
    apply Finset.sum_subset hsubset
    intro selected _ hnot
    apply hzero
    intro hcard
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
  rw [← hreduce]
  symm
  apply Finset.sum_bij (fun slot _ => ({slot} : Finset Slot))
  · intro slot _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton _⟩
  · intro first _ second _ hequal
    exact Finset.singleton_injective hequal
  · intro selected hselected
    obtain ⟨slot, hequal⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hselected).2
    exact ⟨slot, Finset.mem_univ _, hequal.symm⟩
  · intro slot _
    rfl

theorem completeFamily_primary_centered (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (completeFamily security order mass) =
        PrimaryTensorInverse.densityInverse security
          (fun color => LocalTensors.signedColorCount mass color / (primaryLaw security).weight color) := by
  change primaryProjection (primaryLaw security) (bodyReference security) order horder
    (completeFamily security order mass) = _
  unfold completeFamily
  rw [map_add, map_smul, primaryProjection_one, smul_zero, zero_add, map_sum]
  funext color
  simp only [Finset.sum_apply]
  rw [sum_nonempty_singletons _ (fun selected hcard =>
    congrFun (selectedFamily_primary_nonone security order horder mass selected hcard) color)]
  simp only [primaryProjection, LinearMap.coe_mk, AddHom.coe_mk, selectedFamily_singleton_primary,
    hmass, mul_zero, sub_zero]
  have hsum : (∑ slot : Fin 4, PrimaryTensorInverse.densityInverse security
      (fun input => (∑ word, if word slot = input then mass word else 0) /
        (primaryLaw security).weight input) color) =
      PrimaryTensorInverse.densityInverse security
        (∑ slot : Fin 4, fun input => (∑ word, if word slot = input then mass word else 0) /
          (primaryLaw security).weight input) color := by
    rw [map_sum]
    simp only [Finset.sum_apply]
  rw [hsum]
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  simp only [Finset.sum_apply, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  unfold LocalTensors.signedColorCount
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  split_ifs <;> simp

theorem densityInverse_response (security : ℕ) (score : Palette security → ℝ) :
    PrimaryTensorInverse.densityInverse security (PrimaryTensorInverse.densityResponse security score) = score := by
  have hprofile : (fun color => (primaryLaw security).weight color *
      PrimaryTensorInverse.densityResponse security score color) =
      activation security • FirstResponse.response security (fun color => (primaryLaw security).weight color * score color) := by
    funext color
    rw [PrimaryTensorInverse.densityResponse_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(primaryReference_positive security color).ne']
  funext color
  rw [PrimaryTensorInverse.densityInverse_apply, hprofile, map_smul]
  have hinverse : (FirstResponse.responseEquiv security).symm
      (FirstResponse.response security (fun input => (primaryLaw security).weight input * score input)) =
        fun input => (primaryLaw security).weight input * score input := by
    rw [← FirstResponse.responseEquiv_forward]
    exact (FirstResponse.responseEquiv security).symm_apply_apply _
  rw [hinverse]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(primaryReference_positive security color).ne', (activation_pos security).ne']

theorem independentComplete_primary (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (completeFamily security order (IndependentPairedReference.independentSignedMass security score)) = score := by
  rw [completeFamily_primary_centered security order horder _
    (IndependentPairedReference.independentSigned_mass_zero security score hcentered)]
  have hprofile : (fun color => LocalTensors.signedColorCount
      (IndependentPairedReference.independentSignedMass security score) color / (primaryLaw security).weight color) =
      PrimaryTensorInverse.densityResponse security score := by
    funext color
    rw [IndependentPairedReference.independentSigned_first_profile security score hcentered,
      PrimaryTensorInverse.densityResponse_apply]
    rfl
  rw [hprofile, densityInverse_response]

section Filtration

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem vanishesBelow_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (first second : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order degree first)
    (hsecond : VanishesBelow primary body order degree second) :
    VanishesBelow primary body order degree (first + second) := by
  intro arity hdegree
  change first arity + second arity = 0
  rw [hfirst arity hdegree, hsecond arity hdegree, add_zero]

theorem vanishesBelow_sum {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (selected : Finset Index) (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, VanishesBelow primary body order degree (family index)) :
    VanishesBelow primary body order degree (∑ index ∈ selected, family index) := by
  intro arity hdegree
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun index hindex => hfamily index hindex arity hdegree)

theorem backgroundInverse_sub_one_vanishes (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (background : KernelFamily primary body order)
    (hzero : background (zeroArity order) = (1 : KernelFamily primary body order) (zeroArity order)) :
    VanishesBelow primary body order 1 (backgroundInverse primary body order background - 1) := by
  have hbase : (1 - background : KernelFamily primary body order) (zeroArity order) = 0 := by
    change (1 : KernelFamily primary body order) (zeroArity order) - background (zeroArity order) = 0
    rw [hzero, sub_self]
  have hfirst := vanishesBelow_one_of_zero primary body order (1 - background) hbase
  have hsplit : backgroundInverse primary body order background - 1 =
      ∑ power ∈ (Finset.range (order + 1)).erase 0, (1 - background) ^ power := by
    unfold backgroundInverse
    have hsum := Finset.sum_erase_add (Finset.range (order + 1))
      (fun power => (1 - background) ^ power) (by simp : 0 ∈ Finset.range (order + 1))
    simp only [pow_zero] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  rw [hsplit]
  apply vanishesBelow_sum
  intro power hpower arity hdegree
  have hpositive : 0 < power := Nat.pos_of_ne_zero (Finset.mem_erase.mp hpower).1
  exact vanishesBelow_pow primary body order (1 - background) hfirst power arity (by omega)

end Filtration

theorem completeFamily_vanishes_one (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (completeFamily security order mass) := by
  apply vanishesBelow_one_of_zero
  rw [completeFamily_zeroArity, hmass, zero_smul]

/-- Division by the genuine positive local law changes no first coefficient
of a centered signed mass: its actual correction has degree at least two. -/
theorem normalizedFamily_sub_complete_raises (security order : ℕ)
    (positive : FiniteDist (Fin 4 → Palette security)) (mass : (Fin 4 → Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (normalizedFamily security order positive mass - completeFamily security order mass) := by
  have hequal : normalizedFamily security order positive mass - completeFamily security order mass =
      completeFamily security order mass *
        (backgroundInverse (primaryLaw security) (bodyReference security) order
          (positiveFamily security order positive) - 1) := by
    unfold normalizedFamily
    rw [mul_sub, mul_one]
  rw [hequal]
  exact vanishesBelow_mul (primaryLaw security) (bodyReference security) order 1 1 _ _
    (completeFamily_vanishes_one security order mass hmass)
    (backgroundInverse_sub_one_vanishes _ _ order _ (positiveFamily_zeroArity security order positive))

theorem independentNormalized_sub_complete_raises (security order : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (independentNormalized security order score -
        completeFamily security order (IndependentPairedReference.independentSignedMass security score)) :=
  normalizedFamily_sub_complete_raises security order _ _
    (IndependentPairedReference.independentSigned_mass_zero security score hcentered)

theorem completeFamily_no_body (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (arity : TruncatedArity order) (hbody : 0 < arity.val.2.val) :
    completeFamily security order mass arity = 0 := by
  have hunit : (1 : Family security order) arity = 0 := by
    change familyUnit (primaryLaw security) (bodyReference security) order arity = 0
    unfold familyUnit
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  have hselected (selected : Finset (Fin 4)) : selectedFamily security order mass selected arity = 0 := by
    unfold selectedFamily
    split_ifs with hdegree
    · rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
      change arity.val.2.val = 0 at h
      omega
    · rfl
  unfold completeFamily
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, hunit, smul_zero, hselected,
    Finset.sum_const_zero, add_zero]

theorem independentNormalized_primary (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (independentNormalized security order score) = score := by
  have hraise := independentNormalized_sub_complete_raises security order score hcentered
    (primaryArity order horder) (by change 1 + 0 < 2; decide)
  have hequal : independentNormalized security order score (primaryArity order horder) =
      completeFamily security order (IndependentPairedReference.independentSignedMass security score)
        (primaryArity order horder) := sub_eq_zero.mp hraise
  change (fun color => (independentNormalized security order score (primaryArity order horder)).val
    (fun _ => color) Fin.elim0) = _
  rw [hequal]
  exact independentComplete_primary security order horder score hcentered

theorem independentComplete_sub_primary_raises (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (completeFamily security order (IndependentPairedReference.independentSignedMass security score) -
        primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered) := by
  intro arity hsmall
  change completeFamily security order (IndependentPairedReference.independentSignedMass security score) arity -
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [completeFamily_no_body security order _ arity hb]
    unfold primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [completeFamily_zeroArity, IndependentPairedReference.independentSigned_mass_zero security score hcentered,
        zero_smul]
      unfold primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      exact congrFun (independentComplete_primary security order horder score hcentered) (colors 0)

/-- The actual degree-raising local response, built from the physical
four-coordinate laws and the proved finite inverse of their positive
reference polynomial. -/
def localRaising (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) : Family security order :=
  independentNormalized security order score -
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered

theorem localRaising_vanishesBelow (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (localRaising security order horder score hcentered) := by
  have hsplit : localRaising security order horder score hcentered =
      (independentNormalized security order score -
        completeFamily security order (IndependentPairedReference.independentSignedMass security score)) +
      (completeFamily security order (IndependentPairedReference.independentSignedMass security score) -
        primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered) := by
    unfold localRaising
    abel
  rw [hsplit]
  exact vanishesBelow_add _ _ order 2 _ _
    (independentNormalized_sub_complete_raises security order score hcentered)
    (independentComplete_sub_primary_raises security order horder score hcentered)

end
end CurrentAFT.LocalRaisingFirst

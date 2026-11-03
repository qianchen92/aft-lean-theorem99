import CurrentAFT.RationalRootMassProgram
import CurrentAFT.RationalTensorInverseProgram
import CurrentAFT.RootLegCoefficientFamily

/-! # Computed ordering and rational local coefficient extraction

Selected output slots are sorted in their actual `Fin 3` order. The
canonical coefficient is independent of the arbitrary finite equivalence
used by the abstract construction, after its genuine symmetrization.
-/
namespace CurrentAFT.RationalLegCoefficientExtraction
open AFT DiffuseProfiles ProposalPrimary ActualControls
  ControlCoordinates ControlProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def slotNumber (selected : Finset (Fin 3)) : selected → Fin selected.card :=
  (Finset.orderIsoOfFin selected rfl).symm

def atom (security bits source output : ℕ) : ℚ :=
  ((if source = output then 1 else 0) - 1 / (PublicParameterProgram.modulus security).count) /
    RationalProposalProgram.primary security bits output

def density (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  ∑ source : Fin 3 → Fin (PublicParameterProgram.modulus security).count,
    mass (fun index => (source index).val) *
      ∏ slot : selected, atom security bits (source slot.val).val (output (slotNumber selected slot))

def normalized (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected) output

def selectedKernel (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → ℕ) : ℚ :=
  (1 / selected.card.factorial : ℚ) *
    ∑ permutation : Equiv.Perm (Fin selected.card), normalized security bits mass selected (output ∘ permutation)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def orderedDensity (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (output : Fin selected.card → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 3 => primaryLaw security)
    (fun _ : Fin 3 => LocalReferenceEnergy.uniformReference security) mass selected
      (fun slot => output (slotNumber selected slot))

theorem tensorInverse_permutation (security degree : ℕ)
    (kernel : (Fin degree → Palette security) → ℝ) (permutation : Equiv.Perm (Fin degree))
    (output : Fin degree → Palette security) :
    PrimaryTensorInverse.tensorInverse security degree kernel (output ∘ permutation) =
      PrimaryTensorInverse.tensorInverse security degree (fun word => kernel (word ∘ permutation)) output := by
  change TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) kernel (output ∘ permutation) =
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) (fun word => kernel (word ∘ permutation)) output
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance]
  rw [← (PrimaryTensorInverse.wordPermutation (Input := Palette security) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  exact Equiv.prod_comp permutation (fun index =>
    PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))

def orderPermutation (selected : Finset (Fin 3)) : Equiv.Perm (Fin selected.card) :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card selected = selected.card)).symm.trans
    (Finset.orderIsoOfFin selected rfl).symm.toEquiv

theorem orderedDensity_reindex (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    orderedDensity security mass selected = fun output =>
      RootLegCoefficientFamily.selectedDensity security selected.card mass selected (by simp)
        (output ∘ orderPermutation selected) := by
  funext output
  unfold orderedDensity RootLegCoefficientFamily.selectedDensity
  congr 1
  funext slot
  simp only [Function.comp_apply, orderPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- The program's sorted ordering yields the original canonical kernel
as coefficient data. No injectivity of physical evaluation is used. -/
theorem selectedKernel_ordered (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) :
    (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val =
      symmetrize (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) selected.card 0 :=
    fun colors _ => RootLegCoefficientFamily.normalizedSelectedDensity security selected.card mass selected (by simp) colors
  have hraw : (fun (colors : Fin selected.card → Palette security) (_ : Fin 0 → SafePalette security) =>
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected) colors) =
      reindexKernel (orderPermutation selected) (Equiv.refl (Fin 0)) raw := by
    funext colors centers
    rw [orderedDensity_reindex, ← tensorInverse_permutation]
    rfl
  rw [hraw, symmetrize_reindex_permutations]
  rfl

theorem numerator_bound (security : ℕ) (source output : Palette security) :
    |(if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)| ≤ 1 := by
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.two_le.trans' (by omega)
  have hl : 0 ≤ 1 / (Parameters.modulus security : ℝ) := by positivity
  have hu : 1 / (Parameters.modulus security : ℝ) ≤ 1 :=
    (div_le_iff₀ (FirstResponse.modulus_pos security)).mpr (by simpa using hq)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem atom_cast (security bits : ℕ) (source output : Palette security) :
    (atom security bits source.val output.val : ℝ) =
      ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ)) /
        (RationalProposalProgram.approximatePrimaryLaw security bits).weight output := by
  unfold atom
  rw [PublicParameterProgram.modulus_value]
  by_cases hequal : source = output
  · subst output
    simp only [if_true, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
    rfl
  · have hne : source.val ≠ output.val := fun h => hequal (Fin.ext h)
    simp only [if_neg hne, if_neg hequal, Rat.cast_div, Rat.cast_sub, Rat.cast_zero, Rat.cast_one, Rat.cast_natCast]
    rfl

theorem atom_bound (security bits : ℕ) (source output : Palette security) :
    |(atom security bits source.val output.val : ℝ)| ≤ 4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp := RationalProposalProgram.primary_lower security bits output
  have hpos : 0 < (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
    (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus security : ℝ))).trans_le hp
  rw [atom_cast, abs_div, abs_of_pos hpos]
  calc
    _ ≤ 1 / (RationalProposalProgram.approximatePrimaryLaw security bits).weight output :=
      div_le_div_of_nonneg_right (numerator_bound security source output) hpos.le
    _ ≤ 1 / (1 / (4 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = _ := by simp only [one_div, inv_inv]

def atomErrorConstant (security : ℕ) : ℝ :=
  16 * (Parameters.modulus security : ℝ)^2 * RationalRootMassProgram.primaryErrorConstant security

theorem atom_error (security bits : ℕ) (source output : Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(atom security bits source.val output.val : ℝ) -
      MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
        atomErrorConstant security * (1 / (2 : ℝ)^bits) := by
  have hq0 := FirstResponse.modulus_pos security
  have hlo : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    have h : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security output
    have hscale : 1 / (4 * (Parameters.modulus security : ℝ)) ≤ 1 / (2 * (Parameters.modulus security : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact hscale.trans h
  have hp : |(RationalProposalProgram.approximatePrimaryLaw security bits).weight output - (primaryLaw security).weight output| ≤
      RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits) := by
    simpa only [RationalProposalProgram.approximatePrimaryLaw, primaryLaw, RationalRootMassProgram.primaryErrorConstant] using
      RationalProposalProgram.primary_error security bits output hprecision hbudget
  rw [atom_cast, MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight]
  have h := RationalDensityInverseProgram.quotient_error
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((if source = output then (1 : ℝ) else 0) - 1 / (Parameters.modulus security : ℝ))
    ((RationalProposalProgram.approximatePrimaryLaw security bits).weight output)
    ((primaryLaw security).weight output)
    (1 / (4 * (Parameters.modulus security : ℝ))) 0
    (RationalRootMassProgram.primaryErrorConstant security * (1 / (2 : ℝ)^bits)) 1
    (by positivity) (RationalProposalProgram.primary_lower security bits output) hlo (by norm_num)
    (by unfold RationalRootMassProgram.primaryErrorConstant; positivity) (by norm_num)
    (by simp) hp (numerator_bound security source output)
  apply h.trans_eq
  unfold atomErrorConstant
  ring_nf
  simp only [inv_inv]

theorem actual_atom_bound (security : ℕ) (source output : Palette security) :
    |MixedKernel.referenceAtom (primaryLaw security) (LocalReferenceEnergy.uniformReference security) source output| ≤
      4 * (Parameters.modulus security : ℝ) := by
  have hq0 := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  rw [MixedKernel.referenceAtom_eq, LocalReferenceEnergy.uniformReference_weight, abs_div,
    abs_of_pos (primaryReference_positive security output)]
  calc
    _ ≤ 1 / (primaryLaw security).weight output :=
      div_le_div_of_nonneg_right (numerator_bound security source output) (primaryReference_positive security output).le
    _ ≤ 1 / (1 / (2 * (Parameters.modulus security : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hp
    _ ≤ _ := by simp only [one_div, inv_inv]; linarith

theorem density_cast (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ) (selected : Finset (Fin 3))
    (output : Fin selected.card → Palette security) :
    (density security bits mass selected (fun index => (output index).val) : ℝ) =
      ∑ source : Fin 3 → Palette security, (mass (fun index => (source index).val) : ℝ) *
        ∏ slot : selected, (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ) := by
  unfold density
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  congr 1

theorem epsilon_le_one (bits : ℕ) : 1 / (2 : ℝ)^bits ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr
  simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^bits)

def extractionError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 *
    (massError + massBound * degree * atomErrorConstant security) *
      (4 * (Parameters.modulus security : ℝ))^degree

def extractionBound (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 * (massBound + massError) *
    (4 * (Parameters.modulus security : ℝ))^degree

theorem density_bound (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits)) (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ)| ≤
      extractionBound security selected.card massBound massError := by
  rw [density_cast]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 3 → Palette security,
        (massBound + massError) * (4 * (Parameters.modulus security : ℝ))^selected.card := by
      apply Finset.sum_le_sum
      intro source _
      have happrox : |(mass (fun index => (source index).val) : ℝ)| ≤ massBound + massError := by
        have h := abs_add_le ((mass (fun index => (source index).val) : ℝ) - actualMass source) (actualMass source)
        rw [sub_add_cancel] at h
        have hs := mul_le_mul_of_nonneg_left (epsilon_le_one bits) hE
        linarith [hdiff source, hmass source]
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul happrox _ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
      calc
        _ ≤ ∏ _slot : selected, 4 * (Parameters.modulus security : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => atom_bound security bits _ _)
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionBound
      push_cast
      ring

theorem density_error (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(density security bits mass selected (fun index => (output index).val) : ℝ) -
      orderedDensity security actualMass selected output| ≤
        extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let K : ℝ := 4 * Parameters.modulus security
  have hK : 1 ≤ K := by
    have hq : (2 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.two_le
    dsimp only [K]
    linarith
  have hA : 0 ≤ atomErrorConstant security := by
    unfold atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  rw [density_cast]
  unfold orderedDensity LocalTensors.referenceRestrictedComponent
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin 3 → Palette security,
        (massError + massBound * selected.card * atomErrorConstant security) * K^selected.card * epsilon := by
      apply Finset.sum_le_sum
      intro source _
      let approxAtom := fun slot : selected =>
        (atom security bits (source slot.val).val (output (slotNumber selected slot)).val : ℝ)
      let trueAtom := fun slot : selected => MixedKernel.referenceAtom (primaryLaw security)
        (LocalReferenceEnergy.uniformReference security) (source slot.val) (output (slotNumber selected slot))
      have haprod : |∏ slot : selected, approxAtom slot| ≤ K^selected.card := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _slot : selected, K := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun slot _ => atom_bound security bits _ _)
          _ = _ := by simp
      have hprod := RationalTensorInverseProgram.product_difference_bound Finset.univ approxAtom trueAtom K
        (atomErrorConstant security * epsilon) hK (by positivity)
        (fun slot _ => atom_bound security bits _ _)
        (fun slot _ => actual_atom_bound security _ _)
        (fun slot _ => atom_error security bits _ _ hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_coe] at hprod
      change |(mass (fun index => (source index).val) : ℝ) * (∏ slot, approxAtom slot) -
        actualMass source * (∏ slot, trueAtom slot)| ≤ _
      calc
        _ = |((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot) +
          actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot)| := by congr 1; ring
        _ ≤ |(mass (fun index => (source index).val) : ℝ) - actualMass source| * |∏ slot, approxAtom slot| +
          |actualMass source| * |(∏ slot, approxAtom slot) - ∏ slot, trueAtom slot| := by
            simpa only [abs_mul] using abs_add_le
              (((mass (fun index => (source index).val) : ℝ) - actualMass source) * (∏ slot, approxAtom slot))
              (actualMass source * ((∏ slot, approxAtom slot) - ∏ slot, trueAtom slot))
        _ ≤ (massError * epsilon) * K^selected.card +
          massBound * ((selected.card : ℝ) * (atomErrorConstant security * epsilon) * K^selected.card) :=
            add_le_add (mul_le_mul (hdiff source) haprod (abs_nonneg _) (by positivity))
              (mul_le_mul (hmass source) hprod (abs_nonneg _) hM)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold extractionError
      dsimp only [K, epsilon]
      push_cast
      ring

def normalizedError (security degree : ℕ) (massBound massError : ℝ) : ℝ :=
  RationalTensorInverseProgram.tensorErrorConstant security degree * extractionBound security degree massBound massError +
    (Parameters.modulus security : ℝ)^degree * (RationalTensorInverseProgram.actualBound security)^degree *
      extractionError security degree massBound massError

theorem normalized_error (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) :
    |(normalized security bits mass selected (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  let approximate := fun source : Fin selected.card → Palette security =>
    (density security bits mass selected (fun index => (source index).val) : ℝ)
  have hbound : 0 ≤ extractionBound security selected.card massBound massError := by
    unfold extractionBound
    positivity
  have he : 0 ≤ extractionError security selected.card massBound massError := by
    unfold extractionError atomErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have hprogram := RationalTensorInverseProgram.current_error security bits selected.card
    (density security bits mass selected) (extractionBound security selected.card massBound massError) hbound
    (fun source => density_bound security bits mass actualMass selected massBound massError hM hE hmass hdiff source)
    hfirst hprecision hbudget output
  have hreal := RationalTensorInverseProgram.actual_tensor_difference security selected.card
    approximate (orderedDensity security actualMass selected)
    (extractionError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) (by positivity)
    (fun source => density_error security bits mass actualMass selected massBound massError hM hE hmass hdiff
      hprecision hbudget source) output
  unfold normalized
  calc
    _ ≤ |(RationalTensorInverseProgram.current security bits selected.card (density security bits mass selected)
          (fun index => (output index).val) : ℝ) -
        PrimaryTensorInverse.tensorInverse security selected.card approximate output| +
      |PrimaryTensorInverse.tensorInverse security selected.card approximate output -
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security actualMass selected) output| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hprogram hreal
    _ = _ := by unfold normalizedError; ring

theorem selectedKernel_cast (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (selected : Finset (Fin 3)) (output : Fin selected.card → Palette security) :
    (selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        (normalized security bits mass selected (fun index => (output (permutation index)).val) : ℝ)) := by
  simp only [selectedKernel, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sum]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin, one_div]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro permutation _
  rfl

theorem actual_selectedKernel_average (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (output : Fin selected.card → Palette security)
    (body : Fin 0 → SafePalette security) :
    (RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val output body =
      (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).expectation (fun permutation =>
        PrimaryTensorInverse.tensorInverse security selected.card (orderedDensity security mass selected)
          (output ∘ permutation)) := by
  rw [selectedKernel_ordered, ControlProduct.symmetrize_apply]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
  unfold FiniteDist.expectation
  simp only [FiniteDist.uniform_weight, ← Finset.mul_sum, Fintype.card_perm, Fintype.card_fin]

theorem selectedKernel_error (security bits : ℕ) (mass : (Fin 3 → ℕ) → ℚ)
    (actualMass : (Fin 3 → Palette security) → ℝ) (selected : Finset (Fin 3))
    (massBound massError : ℝ) (hM : 0 ≤ massBound) (hE : 0 ≤ massError)
    (hmass : ∀ source, |actualMass source| ≤ massBound)
    (hdiff : ∀ source, |(mass (fun index => (source index).val) : ℝ) - actualMass source| ≤
      massError * (1 / (2 : ℝ)^bits))
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(selectedKernel security bits mass selected (fun index => (output index).val) : ℝ) -
      (RootLegCoefficientFamily.selectedKernel security selected.card actualMass selected (by simp)).val output body| ≤
        normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits) := by
  rw [selectedKernel_cast, actual_selectedKernel_average]
  unfold FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ permutation : Equiv.Perm (Fin selected.card),
        (FiniteDist.uniform (Equiv.Perm (Fin selected.card))).weight permutation *
          (normalizedError security selected.card massBound massError * (1 / (2 : ℝ)^bits)) := by
      apply Finset.sum_le_sum
      intro permutation _
      rw [← mul_sub, abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)]
      exact mul_le_mul_of_nonneg_left
        (normalized_error security bits mass actualMass selected massBound massError hM hE hmass hdiff
          hfirst hprecision hbudget (output ∘ permutation)) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end
end CurrentAFT.RationalLegCoefficientExtraction

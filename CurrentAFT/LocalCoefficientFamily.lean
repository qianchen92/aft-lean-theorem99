import CurrentAFT.PairedReferenceEnergy
import CurrentAFT.PrimaryTensorInverse
import CurrentAFT.GradedInverse
import AFT.MixedReferenceCanonicalFibers
import AFT.ReferenceCoefficientPolynomial

/-!
# Actual local coefficients in the current canonical graded algebra

Each selected coefficient is extracted from the physical signed mass by
the atoms `(delta - uniform) / primary`. It is transported to ordered Fin
slots, acted on by the constructed primary tensor inverse, and genuinely
symmetrized. The higher family below retains precisely the subsets with
at least two outputs. No higher response or raising operator is a premise.
-/

namespace CurrentAFT.LocalCoefficientFamily

open AFT DiffuseProfiles ProposalPrimary ActualControls
open ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
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
abbrev Family (security order : ℕ) := KernelFamily (primaryLaw security) (bodyReference security) order

def selectedDensity (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree)
    (word : Fin degree → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
    (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security) mass selected
      (word ∘ Fintype.equivFinOfCardEq hdegree)

private theorem selectedDensity_generic_canonical {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
    (primary reference : FiniteDist Color) (hpositive : ∀ color, 0 < primary.weight color)
    (degree : ℕ) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primary) Finset.univ
      (fun word => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
        (fun _ : Slot => reference) mass selected (word ∘ Fintype.equivFinOfCardEq hdegree)) := by
  have hraw := LocalTensors.referenceRestrictedComponent_canonical
    (fun _ : Slot => primary) (fun _ : Slot => reference) (fun _ => hpositive) mass selected
  let raw : Kernel (Primary := Color) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected colors
  have hcentered : raw ∈ centeredKernelSpace primary (FiniteDist.uniform Unit) := by
    constructor
    · intro index colors _
      exact hraw.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have htransport := reindexKernel_centered primary (FiniteDist.uniform Unit)
    (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw hcentered
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ index))
    rw [heq]
  · intro index _ word
    exact htransport.1 index word Fin.elim0

theorem selectedDensity_canonical (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (selectedDensity security degree mass selected hdegree) :=
  selectedDensity_generic_canonical (primaryLaw security) (LocalReferenceEnergy.uniformReference security)
    (primaryReference_positive security) degree mass selected hdegree

def normalizedSelectedDensity (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (Fin degree → Palette security) → ℝ :=
  PrimaryTensorInverse.tensorInverse security degree (selectedDensity security degree mass selected hdegree)

theorem normalizedSelectedDensity_leading (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    PrimaryTensorInverse.tensorResponse security degree
      (normalizedSelectedDensity security degree mass selected hdegree) =
        selectedDensity security degree mass selected hdegree :=
  PrimaryTensorInverse.tensorResponse_inverse security degree _

theorem normalizedSelectedDensity_canonical (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (normalizedSelectedDensity security degree mass selected hdegree) :=
  PrimaryTensorInverse.tensorInverse_canonical security degree _
    (selectedDensity_canonical security degree mass selected hdegree)

def selectedKernel (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    canonicalKernels (primaryLaw security) (bodyReference security) degree 0 := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) degree 0 :=
    fun colors _ => normalizedSelectedDensity security degree mass selected hdegree colors
  have hcanonical := normalizedSelectedDensity_canonical security degree mass selected hdegree
  have hcentered : raw ∈ centeredKernelSpace (primaryLaw security) (bodyReference security) := by
    constructor
    · intro index colors _
      exact hcanonical.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have hs := symmetrize_centered (primaryLaw security) (bodyReference security) raw hcentered
  refine ⟨symmetrize raw, hs.1, hs.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

def selectedArity (order : ℕ) (selected : Finset (Fin 4)) (hdegree : selected.card ≤ order) : TruncatedArity order :=
  ⟨(⟨selected.card, by omega⟩, 0), by simpa using hdegree⟩

def selectedFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) : Family security order :=
  if hdegree : selected.card ≤ order then
    Pi.single (selectedArity order selected hdegree)
      (selectedKernel security selected.card mass selected (by simp))
  else 0

def higherFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
    selectedFamily security order mass selected

theorem higherFamily_vanishesBelow (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (higherFamily security order mass) := by
  intro arity hsmall
  unfold higherFamily
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro selected hselected
  have hcard := (Finset.mem_filter.mp hselected).2
  unfold selectedFamily
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    intro hequal
    have hsmall' := hsmall
    rw [hequal] at hsmall'
    change selected.card + 0 < 2 at hsmall'
    omega
  · rfl

/-- The explicit higher family extracted from the actual fixed-root
four-output paired signed channel. -/
def pairedHigherFamily (security order : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ) : Family security order :=
  higherFamily security order (PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score)

theorem pairedHigherFamily_vanishesBelow (security order : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (pairedHigherFamily security order compensatorRoot attachmentRoot scalar score) :=
  higherFamily_vanishesBelow security order _

def massPolynomial (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ) :
    MvPolynomial (Palette security) ℝ :=
  ∑ word, MvPolynomial.C (profile word) * ∏ index, MvPolynomial.X (word index)

def primaryLeadingPolynomial (security degree : ℕ) (density : (Fin degree → Palette security) → ℝ) :
    MvPolynomial (Palette security) ℝ :=
  massPolynomial security degree (PrimaryTensorInverse.massLeading security degree density)

private def orderedWordEquiv {Source Target Color : Type*} (equiv : Source ≃ Target) :
    (Target → Color) ≃ (Source → Color) where
  toFun word := word ∘ equiv
  invFun word := word ∘ equiv.symm
  left_inv word := by funext index; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv word := by funext index; simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- The actual inverse's output polynomial is exactly the selected
uniform-centered physical PGF coefficient. This identity keeps the full
joint selected kernel and merely renames its finite coordinates. -/
theorem normalizedSelectedDensity_polynomial (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    primaryLeadingPolynomial security degree (normalizedSelectedDensity security degree mass selected hdegree) =
      RepresentedPolynomial.referenceCoefficientForm (primaryLaw security)
        (LocalReferenceEnergy.uniformReference security) mass selected := by
  unfold primaryLeadingPolynomial massPolynomial PrimaryTensorInverse.massLeading
  rw [normalizedSelectedDensity_leading]
  let equiv := Fintype.equivFinOfCardEq hdegree
  have hreindex := (orderedWordEquiv (Color := Palette security) equiv).sum_comp
    (fun word : selected → Palette security =>
      MvPolynomial.C (LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
        (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security) mass selected word *
          ∏ index, (primaryLaw security).weight (word index)) *
        ∏ index, MvPolynomial.X (R := ℝ) (word index))
  change _ = ∑ word : selected → Palette security, _
  apply Eq.trans ?_ hreindex
  apply Finset.sum_congr rfl
  intro word _
  have hweight := equiv.prod_comp (fun index : Fin degree => (primaryLaw security).weight (word index))
  have hmonomial := equiv.prod_comp (fun index : Fin degree => MvPolynomial.X (R := ℝ) (word index))
  simp only [orderedWordEquiv, Equiv.coe_fn_mk, Function.comp_apply, hweight, hmonomial,
    selectedDensity, PrimaryTensorInverse.referenceWeight]
  congr 1
  congr 1
  ring

theorem normalizedSelectedDensity_physical_coefficient (security degree : ℕ)
    (mass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :
    primaryLeadingPolynomial security degree (normalizedSelectedDensity security degree mass selected hdegree) =
      ∑ source, MvPolynomial.C (mass source) * ∏ index : selected,
        (MvPolynomial.X (source index) - RepresentedPolynomial.profileForm
          (LocalReferenceEnergy.uniformReference security).weight) := by
  rw [normalizedSelectedDensity_polynomial]
  exact RepresentedPolynomial.referenceCoefficientForm_formula _ _ (primaryReference_positive security) mass selected

end

end CurrentAFT.LocalCoefficientFamily

import CurrentAFT.OrdinaryRaising

/-!
# Both-role independent-root raising operator

Each nonempty pattern may replace primary or ordinary selected controls.
Ordinary numerators retain their original safe body slot, while their
positive reciprocal emits only primary slots. Every joint input is kept
inside its actual two-reference finite sum.
-/
namespace CurrentAFT.CompleteRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def bodyAtom (security : ℕ) (source : SafePalette security) : OrdinaryRaising.centeredBodyScores security :=
  ⟨Hoeffding.centeredAtom (bodyReference security) source,
    Hoeffding.centeredAtom_mean _ (bodyReference_positive security) source⟩

def ordinaryRaisedPoint (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) : Family security order :=
  OrdinaryRaising.raisingLinear security order horder (bodyAtom security source)

def slotLeading (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => primaryPoint security order horder (sourcePrimary index))
    (fun index => bodyPoint security order horder (sourceBody index))

def slotRaised (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => raisedPoint security order horder (sourcePrimary index))
    (fun index => ordinaryRaisedPoint security order horder (sourceBody index))

def selectedPointProduct (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Family security order :=
  ∏ slot : Fin r ⊕ Fin s, if slot ∈ selected then slotRaised security order horder sourcePrimary sourceBody slot
    else slotLeading security order horder sourcePrimary sourceBody slot

theorem selectedPointProduct_vanishes (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order (r + s + selected.card)
      (selectedPointProduct security order horder selected sourcePrimary sourceBody) := by
  have h := GlobalRaising.vanishesBelow_prod (primaryLaw security) (bodyReference security) order
    (Finset.univ : Finset (Fin r ⊕ Fin s)) (fun slot => if slot ∈ selected then 2 else 1)
    (fun slot => if slot ∈ selected then slotRaised security order horder sourcePrimary sourceBody slot
      else slotLeading security order horder sourcePrimary sourceBody slot) (fun slot _ => by
        dsimp only
        split_ifs
        · cases slot with
          | inl index => exact raisedPoint_vanishes security order horder _
          | inr index => exact OrdinaryRaising.raisingFamily_vanishesBelow security order horder _ _
        · cases slot with
          | inl index => exact primaryPoint_vanishes security order horder _
          | inr index => exact bodyPoint_vanishes security order horder _)
  have hcount : (∑ slot : Fin r ⊕ Fin s, if slot ∈ selected then 2 else 1) = r + s + selected.card := by
    have hpoint (slot : Fin r ⊕ Fin s) : (if slot ∈ selected then 2 else 1) =
        1 + (if slot ∈ selected then 1 else 0) := by split_ifs <;> omega
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib]
  simpa only [hcount, selectedPointProduct] using h

def selectedCorrection (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    Family security order :=
  ∑ sourcePrimary, ∑ sourceBody,
    ((∏ index, (primaryLaw security).weight (sourcePrimary index)) *
      (∏ index, (bodyReference security).weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
        selectedPointProduct security order horder selected sourcePrimary sourceBody

def selectedCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order where
  toFun := selectedCorrection security order horder selected
  map_add' first second := by
    simp only [selectedCorrection, Submodule.coe_add, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [selectedCorrection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro sourcePrimary _
    apply Finset.sum_congr rfl
    intro sourceBody _
    rw [smul_smul]
    congr 1
    ring

def homogeneousCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r ⊕ Fin s))).erase ∅,
    selectedCorrectionLinear security order horder selected

theorem homogeneousCorrection_vanishes (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    VanishesBelow (primaryLaw security) (bodyReference security) order (r + s + 1)
      (homogeneousCorrectionLinear security order horder r s kernel) := by
  simp only [homogeneousCorrectionLinear, LinearMap.sum_apply]
  apply vanishesBelow_sum
  intro selected hselected
  change VanishesBelow _ _ order (r + s + 1) (selectedCorrection security order horder selected kernel)
  unfold selectedCorrection
  apply vanishesBelow_sum
  intro sourcePrimary _
  apply vanishesBelow_sum
  intro sourceBody _
  apply GlobalRaising.vanishesBelow_smul
  intro arity hdegree
  have hpositive : 0 < selected.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
  exact selectedPointProduct_vanishes security order horder selected sourcePrimary sourceBody arity (by omega)

def raisingLinear (security order : ℕ) (horder : 1 ≤ order) : Family security order →ₗ[ℝ] Family security order where
  toFun family := ∑ arity : TruncatedArity order,
    homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity)
  map_add' first second := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar family := by simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum, RingHom.id_apply]

theorem raisingLinear_raises (security order : ℕ) (horder : 1 ≤ order) (degree : ℕ)
    (family : Family security order)
    (hfamily : VanishesBelow (primaryLaw security) (bodyReference security) order degree family) :
    VanishesBelow (primaryLaw security) (bodyReference security) order (degree + 1)
      (raisingLinear security order horder family) := by
  change VanishesBelow _ _ order (degree + 1) (∑ arity : TruncatedArity order,
    homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity))
  apply vanishesBelow_sum
  intro arity _
  by_cases hsmall : arity.val.1.val + arity.val.2.val < degree
  · rw [hfamily arity hsmall, map_zero]
    intro output _
    rfl
  · intro output hdegree
    exact homogeneousCorrection_vanishes security order horder _ _ (family arity) output (by omega)

end
end CurrentAFT.CompleteRaising

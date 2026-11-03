import CurrentAFT.LocalRaisingBounds
import CurrentAFT.CanonicalReconstruction

/-!
# The primary part of the actual finite-sum degree-raising response

The leading coefficient is the original canonical joint kernel. Every
nonleading pattern replaces a nonempty set of its primary slots by the
constructed local raising response. All source coordinates are summed
against the original joint kernel and the two actual product references;
no factorization of that kernel is assumed. Ordinary reciprocal corrections
are added separately in `CompleteRaising`.
-/
namespace CurrentAFT.GlobalRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryAtom (security : ℕ) (source : Palette security) : centeredScores security :=
  ⟨Hoeffding.centeredAtom (primaryLaw security) source,
    Hoeffding.centeredAtom_mean _ (primaryReference_positive security) source⟩

def primaryPoint (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) : Family security order :=
  primaryEmbeddingLinear security order horder (primaryAtom security source)

def raisedPoint (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) : Family security order :=
  localRaisingLinear security order horder (primaryAtom security source)

def bodyPoint (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder
    (Hoeffding.centeredAtom (bodyReference security) source)
      (Hoeffding.centeredAtom_mean _ (bodyReference_positive security) source)

theorem primaryPoint_vanishes (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (primaryPoint security order horder source) := by
  apply vanishesBelow_one_of_zero
  unfold primaryPoint primaryEmbeddingLinear primaryFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega

theorem bodyPoint_vanishes (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (bodyPoint security order horder source) := by
  apply vanishesBelow_one_of_zero
  unfold bodyPoint bodyFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : TruncatedArity order => arity.val.2.val) hequal
  change 0 = 1 at h
  omega

theorem raisedPoint_vanishes (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (raisedPoint security order horder source) :=
  localRaisingLinear_vanishesBelow security order horder _

section Filtration
variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body]

theorem vanishesBelow_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (scalar : ℝ) (family : KernelFamily primary body order)
    (hfamily : VanishesBelow primary body order degree family) :
    VanishesBelow primary body order degree (scalar • family) := by
  intro arity hdegree
  change scalar • family arity = 0
  rw [hfamily arity hdegree, smul_zero]

theorem vanishesBelow_prod (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (selected : Finset Index) (degree : Index → ℕ)
    (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, VanishesBelow primary body order (degree index) (family index)) :
    VanishesBelow primary body order (∑ index ∈ selected, degree index) (∏ index ∈ selected, family index) := by
  induction selected using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact vanishesBelow_zero primary body order _
  | @insert index selected hnot ih =>
    rw [Finset.sum_insert hnot, Finset.prod_insert hnot]
    exact vanishesBelow_mul primary body order _ _ _ _
      (hfamily index (Finset.mem_insert_self _ _))
      (ih (fun other hother => hfamily other (Finset.mem_insert_of_mem hother)))

end Filtration

def selectedPointProduct (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Family security order :=
  (∏ index : Fin r, if index ∈ selected then raisedPoint security order horder (sourcePrimary index)
    else primaryPoint security order horder (sourcePrimary index)) *
      ∏ index : Fin s, bodyPoint security order horder (sourceBody index)

theorem selectedPointProduct_vanishes (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    VanishesBelow (primaryLaw security) (bodyReference security) order (r + s + selected.card)
      (selectedPointProduct security order horder selected sourcePrimary sourceBody) := by
  have hp := vanishesBelow_prod (primaryLaw security) (bodyReference security) order
    (Finset.univ : Finset (Fin r)) (fun index => if index ∈ selected then 2 else 1)
    (fun index => if index ∈ selected then raisedPoint security order horder (sourcePrimary index)
      else primaryPoint security order horder (sourcePrimary index)) (fun index _ => by
        dsimp only
        split_ifs
        · exact raisedPoint_vanishes security order horder _
        · exact primaryPoint_vanishes security order horder _)
  have hb := vanishesBelow_prod (primaryLaw security) (bodyReference security) order
    (Finset.univ : Finset (Fin s)) (fun _ => 1)
    (fun index => bodyPoint security order horder (sourceBody index))
    (fun _ _ => bodyPoint_vanishes security order horder _)
  have hcount : (∑ index : Fin r, if index ∈ selected then 2 else 1) = r + selected.card := by
    have hpoint (index : Fin r) : (if index ∈ selected then 2 else 1) =
        1 + (if index ∈ selected then 1 else 0) := by split_ifs <;> omega
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib]
  simp only [hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_one, smul_eq_mul] at hp hb
  have h := vanishesBelow_mul (primaryLaw security) (bodyReference security) order _ _ _ _ hp hb
  have hdegree : r + selected.card + s = r + s + selected.card := by omega
  rw [hdegree] at h
  simpa only [selectedPointProduct] using h

def selectedCorrection (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r)) (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    Family security order :=
  ∑ sourcePrimary, ∑ sourceBody,
    ((∏ index, (primaryLaw security).weight (sourcePrimary index)) *
      (∏ index, (bodyReference security).weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
        selectedPointProduct security order horder selected sourcePrimary sourceBody

def selectedCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r)) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order where
  toFun := selectedCorrection security order horder selected
  map_add' first second := by
    simp only [selectedCorrection, Submodule.coe_add, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [selectedCorrection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro sourcePrimary _
    apply Finset.sum_congr rfl
    intro sourceBody _
    rw [smul_smul]
    congr 1
    ring

def homogeneousCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r))).erase ∅,
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
  apply vanishesBelow_smul
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

theorem raising_pow_vanishes (security order : ℕ) (horder : 1 ≤ order) (power : ℕ)
    (family : Family security order) :
    VanishesBelow (primaryLaw security) (bodyReference security) order power
      (((raisingLinear security order horder : Module.End ℝ (Family security order)) ^ power) family) := by
  induction power with
  | zero => exact vanishesBelow_zero _ _ order _
  | succ power ih =>
    rw [pow_succ']
    change VanishesBelow _ _ order (power + 1)
      (raisingLinear security order horder (((raisingLinear security order horder : Module.End ℝ (Family security order)) ^ power) family))
    exact raisingLinear_raises security order horder power _ ih

theorem raising_nilpotent (security order : ℕ) (horder : 1 ≤ order) :
    (raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
  apply LinearMap.ext
  intro family
  funext arity
  exact raising_pow_vanishes security order horder (order + 1) family arity (by have := arity.property; omega)

def responseLinear (security order : ℕ) (horder : 1 ≤ order) : Module.End ℝ (Family security order) :=
  1 + raisingLinear security order horder

/-- The actual strictly raising operator has a finite exact inverse. This
algebraic conclusion is separate from its quantitative norm estimate. -/
def responseInverse (security order : ℕ) (horder : 1 ≤ order) : Module.End ℝ (Family security order) :=
  ∑ power ∈ Finset.range (order + 1), (-raisingLinear security order horder) ^ power

theorem responseInverse_mul (security order : ℕ) (horder : 1 ≤ order) :
    responseInverse security order horder * responseLinear security order horder = 1 := by
  have hnil : (-raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
    simpa only [raising_nilpotent security order horder, mul_zero] using
      (neg_pow (raisingLinear security order horder : Module.End ℝ (Family security order)) (order + 1))
  have h := geom_sum_mul_neg (-raisingLinear security order horder) (order + 1)
  simpa only [responseInverse, responseLinear, sub_neg_eq_add, hnil, sub_zero] using h

theorem mul_responseInverse (security order : ℕ) (horder : 1 ≤ order) :
    responseLinear security order horder * responseInverse security order horder = 1 := by
  have hnil : (-raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
    simpa only [raising_nilpotent security order horder, mul_zero] using
      (neg_pow (raisingLinear security order horder : Module.End ℝ (Family security order)) (order + 1))
  have h := mul_neg_geom_sum (-raisingLinear security order horder) (order + 1)
  simpa only [responseInverse, responseLinear, sub_neg_eq_add, hnil, sub_zero] using h

theorem responseInverse_response (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    responseInverse security order horder (responseLinear security order horder family) = family := by
  have h := congrArg (fun channel : Module.End ℝ (Family security order) => channel family)
    (responseInverse_mul security order horder)
  exact h

theorem response_responseInverse (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    responseLinear security order horder (responseInverse security order horder family) = family := by
  have h := congrArg (fun channel : Module.End ℝ (Family security order) => channel family)
    (mul_responseInverse security order horder)
  exact h

end
end CurrentAFT.GlobalRaising

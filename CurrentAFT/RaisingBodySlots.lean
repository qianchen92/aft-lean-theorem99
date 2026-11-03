import CurrentAFT.CompleteRaising

/-! # The two-role raising operator creates no body slots -/
namespace CurrentAFT.RaisingBodySlots

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  NormalizedLocalPolynomial BackgroundFamilies GlobalRaising
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

section Generic
variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body]

def AtMost (primary : FiniteDist Primary) (body : FiniteDist Body) (order bound : ℕ)
    (family : KernelFamily primary body order) : Prop :=
  ∀ arity, bound < arity.val.2.val → family arity = 0

theorem atMost_add (primary : FiniteDist Primary) (body : FiniteDist Body) (order bound : ℕ)
    (first second : KernelFamily primary body order) (hfirst : AtMost primary body order bound first)
    (hsecond : AtMost primary body order bound second) : AtMost primary body order bound (first + second) := by
  intro arity hbody
  change first arity + second arity = 0
  rw [hfirst arity hbody, hsecond arity hbody, add_zero]

theorem atMost_sub (primary : FiniteDist Primary) (body : FiniteDist Body) (order bound : ℕ)
    (first second : KernelFamily primary body order) (hfirst : AtMost primary body order bound first)
    (hsecond : AtMost primary body order bound second) : AtMost primary body order bound (first - second) := by
  intro arity hbody
  change first arity - second arity = 0
  rw [hfirst arity hbody, hsecond arity hbody, sub_self]

theorem atMost_smul (primary : FiniteDist Primary) (body : FiniteDist Body) (order bound : ℕ)
    (scalar : ℝ) (family : KernelFamily primary body order) (hfamily : AtMost primary body order bound family) :
    AtMost primary body order bound (scalar • family) := by
  intro arity hbody
  change scalar • family arity = 0
  rw [hfamily arity hbody, smul_zero]

theorem atMost_sum (primary : FiniteDist Primary) (body : FiniteDist Body) (order bound : ℕ)
    (selected : Finset Index) (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, AtMost primary body order bound (family index)) :
    AtMost primary body order bound (∑ index ∈ selected, family index) := by
  intro arity hbody
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun index hindex => hfamily index hindex arity hbody)

theorem atMost_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order firstBound secondBound : ℕ)
    (first second : KernelFamily primary body order) (hfirst : AtMost primary body order firstBound first)
    (hsecond : AtMost primary body order secondBound second) :
    AtMost primary body order (firstBound + secondBound) (first * second) := by
  intro output hbody
  change familyProduct primary body order first second output = 0
  unfold familyProduct
  apply Finset.sum_eq_zero
  intro left _
  apply Finset.sum_eq_zero
  intro right _
  split_ifs with hmatch
  · by_cases hleft : firstBound < left.val.2.val
    · rw [hfirst left hleft, homogeneousProduct_zero_left, transportKernel_zero]
    · have hright : secondBound < right.val.2.val := by omega
      rw [hsecond right hright, homogeneousProduct_zero_right, transportKernel_zero]
  · rfl

theorem atMost_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (arity : TruncatedArity order) (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    AtMost primary body order arity.val.2.val (Pi.single arity kernel) := by
  intro output hbody
  rw [Pi.single_eq_of_ne]
  intro hequal
  rw [hequal] at hbody
  omega

theorem atMost_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    AtMost primary body order 0 (1 : KernelFamily primary body order) :=
  atMost_single primary body order (zeroArity order) (scalarUnit primary body)

theorem atMost_zero_pow (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hfamily : AtMost primary body order 0 family) (power : ℕ) :
    AtMost primary body order 0 (family ^ power) := by
  induction power with
  | zero => rw [pow_zero]; exact atMost_one primary body order
  | succ power ih =>
    rw [pow_succ]
    exact atMost_mul primary body order 0 0 _ _ ih hfamily

theorem atMost_inverse (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hfamily : AtMost primary body order 0 family) :
    AtMost primary body order 0 (backgroundInverse primary body order family) := by
  unfold backgroundInverse
  apply atMost_sum
  intro power _
  exact atMost_zero_pow primary body order (1 - family)
    (atMost_sub primary body order 0 1 family (atMost_one primary body order) hfamily) power

theorem atMost_prod (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (selected : Finset Index) (bound : Index → ℕ) (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, AtMost primary body order (bound index) (family index)) :
    AtMost primary body order (∑ index ∈ selected, bound index) (∏ index ∈ selected, family index) := by
  induction selected using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using atMost_one primary body order
  | @insert index selected hnot ih =>
    rw [Finset.sum_insert hnot, Finset.prod_insert hnot]
    exact atMost_mul primary body order _ _ _ _ (hfamily index (Finset.mem_insert_self _ _))
      (ih (fun other hother => hfamily other (Finset.mem_insert_of_mem hother)))
end Generic

theorem primaryFamily_atMost (security order : ℕ) (horder : 1 ≤ order)
    (score : ActualControls.Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    AtMost (primaryLaw security) (bodyReference security) order 0
      (primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered) :=
  atMost_single _ _ order (primaryArity order horder) _

theorem bodyFamily_atMost (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    AtMost (primaryLaw security) (bodyReference security) order 1
      (bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered) :=
  atMost_single _ _ order (bodyArity order horder) _

theorem completeFamily_atMost (security order : ℕ) (mass : (Fin 4 → ActualControls.Palette security) → ℝ) :
    AtMost (primaryLaw security) (bodyReference security) order 0 (completeFamily security order mass) :=
  completeFamily_no_body security order mass

theorem primaryRaising_atMost (security order : ℕ) (horder : 1 ≤ order)
    (score : ActualControls.Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    AtMost (primaryLaw security) (bodyReference security) order 0
      (localRaising security order horder score hcentered) := by
  unfold localRaising independentNormalized normalizedFamily
  apply atMost_sub
  · exact atMost_mul _ _ order 0 0 _ _ (completeFamily_atMost security order _)
      (atMost_inverse _ _ order _ (completeFamily_atMost security order _))
  · exact primaryFamily_atMost security order horder score hcentered

theorem ordinaryRaising_atMost (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    AtMost (primaryLaw security) (bodyReference security) order 1
      (OrdinaryRaising.raisingFamily security order horder score hcentered) := by
  have hatom : AtMost (primaryLaw security) (bodyReference security) order 0
      (OrdinaryRaising.positiveAtom security order horder) :=
    atMost_single _ _ order (PrimaryMassFamilies.primaryArity order 1 horder) _
  have hpositive := atMost_add _ _ order 0 _ _ (atMost_one _ _ order) hatom
  have hinverse := atMost_inverse _ _ order (OrdinaryRaising.positiveFamily security order horder) hpositive
  exact atMost_mul _ _ order 1 0 _ _ (bodyFamily_atMost security order horder score hcentered)
    (atMost_sub _ _ order 0 _ _ hinverse (atMost_one _ _ order))

theorem selectedPointProduct_atMost (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (sourcePrimary : Fin r → ActualControls.Palette security)
    (sourceBody : Fin s → SafePalette security) :
    AtMost (primaryLaw security) (bodyReference security) order s
      (CompleteRaising.selectedPointProduct security order horder selected sourcePrimary sourceBody) := by
  have h := atMost_prod (primaryLaw security) (bodyReference security) order Finset.univ
    (Sum.elim (fun _ : Fin r => 0) (fun _ : Fin s => 1))
    (fun slot => if slot ∈ selected then CompleteRaising.slotRaised security order horder sourcePrimary sourceBody slot
      else CompleteRaising.slotLeading security order horder sourcePrimary sourceBody slot) (fun slot _ => by
        dsimp only
        by_cases hselected : slot ∈ selected
        · rw [if_pos hselected]
          cases slot with
          | inl index => exact primaryRaising_atMost security order horder _ _
          | inr index => exact ordinaryRaising_atMost security order horder _ _
        · rw [if_neg hselected]
          cases slot with
          | inl index => exact primaryFamily_atMost security order horder _ _
          | inr index => exact bodyFamily_atMost security order horder _ _)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, zero_add,
    CompleteRaising.selectedPointProduct] using h

theorem selectedCorrection_atMost (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    AtMost (primaryLaw security) (bodyReference security) order s
      (CompleteRaising.selectedCorrection security order horder selected kernel) := by
  unfold CompleteRaising.selectedCorrection
  apply atMost_sum
  intro sourcePrimary _
  apply atMost_sum
  intro sourceBody _
  exact atMost_smul _ _ order s _ _ (selectedPointProduct_atMost security order horder selected sourcePrimary sourceBody)

theorem homogeneousCorrection_atMost (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    AtMost (primaryLaw security) (bodyReference security) order s
      (CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel) := by
  simp only [CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  apply atMost_sum
  intro selected _
  exact selectedCorrection_atMost security order horder selected kernel

/-- Every input body-order bound is preserved by the complete actual
independent-root upper response, including ordinary reciprocal outputs. -/
theorem raising_preserves_body (security order : ℕ) (horder : 1 ≤ order) (bound : ℕ)
    (family : Family security order) (hfamily : AtMost (primaryLaw security) (bodyReference security) order bound family) :
    AtMost (primaryLaw security) (bodyReference security) order bound
      (CompleteRaising.raisingLinear security order horder family) := by
  change AtMost _ _ order bound (∑ arity : TruncatedArity order,
    CompleteRaising.homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity))
  apply atMost_sum
  intro arity _
  by_cases hlarge : bound < arity.val.2.val
  · rw [hfamily arity hlarge, map_zero]
    intro output _
    rfl
  · intro output houtput
    exact homogeneousCorrection_atMost security order horder arity.val.1.val arity.val.2.val (family arity)
      output (by omega)

end
end CurrentAFT.RaisingBodySlots

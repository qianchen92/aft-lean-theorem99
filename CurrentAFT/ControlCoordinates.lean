import AFT.CompatibleFibers
import CurrentAFT.Parameters

/-!
# Canonical density kernels for the current two public-control alphabets

This file realizes `def:df-control-coordinates` as actual finite density
kernels. Primary controls use all residue colors; body controls use the safe
palette. Positive arities are centered in every slot and separately symmetric,
and degree zero is a separate real scalar. These are public controls under
the uncharged proposal at a fixed placement, not independent hidden endpoints.

The explicit single-slot centering projections and distinct-index two-pool
averages below prove their claimed mean identities by finite sums. The paired
lift uses the manuscript's density-to-profile anchor kernel and compensator
density ratio. No actual response stability, protected-cycle independence,
coordinate basis, disjoint-slot multiplication theorem, or sampler complexity
is assumed or asserted here. Reference laws remain parameters until the
current positive-proposal construction supplies them.
-/

namespace CurrentAFT.ControlCoordinates

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) :=
  Classical.decEq _

/-- The primary-control alphabet in the current manuscript. -/
abbrev PrimaryAlphabet (modulus : ℕ) := ZMod modulus

/-- Canonical residues in the inclusive safe interval
`margin, ..., modulus - 1 - margin`. -/
abbrev BodyAlphabet (modulus margin : ℕ) :=
  {color : ZMod modulus // margin ≤ color.val ∧ color.val + margin < modulus}

/-- The actual public family fixes both alphabets before the calibration order. -/
abbrev CurrentPrimaryAlphabet (security : ℕ) := PrimaryAlphabet (Parameters.modulus security)

abbrev CurrentBodyAlphabet (security : ℕ) :=
  BodyAlphabet (Parameters.modulus security) (Parameters.safeMargin security)

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

/-- Density relative to the product reference; the two input alphabets differ. -/
abbrev DensityKernel (primaryDegree bodyDegree : ℕ) :=
  (Fin primaryDegree → Primary) → (Fin bodyDegree → Body) → ℝ

def PrimaryCenteredAt (primary : FiniteDist Primary) {r s : ℕ}
    (index : Fin r) (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ colors centers, ∑ color, primary.weight color *
    kernel (Function.update colors index color) centers = 0

def BodyCenteredAt (body : FiniteDist Body) {r s : ℕ}
    (index : Fin s) (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ colors centers, ∑ center, body.weight center *
    kernel colors (Function.update centers index center) = 0

def SeparatelySymmetric {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : Prop :=
  ∀ (primaryOrder : Equiv.Perm (Fin r)) (bodyOrder : Equiv.Perm (Fin s)) colors centers,
    kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers

/-- The actual finite coefficient fiber at arity `(r,s)`. No tensor
factorization or independence of the kernel's arguments is required. -/
def canonicalKernels (primary : FiniteDist Primary) (body : FiniteDist Body) (r s : ℕ) :
    Submodule ℝ (DensityKernel (Primary := Primary) (Body := Body) r s) where
  carrier := {kernel | (∀ index, PrimaryCenteredAt primary index kernel) ∧
    (∀ index, BodyCenteredAt body index kernel) ∧ SeparatelySymmetric kernel}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      simp
    · intro index colors centers
      simp
    · intro primaryOrder bodyOrder colors centers
      rfl
  add_mem' := by
    intro first second hfirst hsecond
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.1 index colors centers, hsecond.1 index colors centers, add_zero]
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.2.1 index colors centers, hsecond.2.1 index colors centers, add_zero]
    · intro primaryOrder bodyOrder colors centers
      simp only [Pi.add_apply, hfirst.2.2 primaryOrder bodyOrder colors centers,
        hsecond.2.2 primaryOrder bodyOrder colors centers]
  smul_mem' := by
    intro scalar kernel hkernel
    refine ⟨?_, ?_, ?_⟩
    · intro index colors centers
      change (∑ color, primary.weight color *
        (scalar * kernel (Function.update colors index color) centers)) = 0
      calc
        _ = scalar * ∑ color, primary.weight color *
            kernel (Function.update colors index color) centers := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hkernel.1 index colors centers, mul_zero]
    · intro index colors centers
      change (∑ center, body.weight center *
        (scalar * kernel colors (Function.update centers index center))) = 0
      calc
        _ = scalar * ∑ center, body.weight center *
            kernel colors (Function.update centers index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hkernel.2.1 index colors centers, mul_zero]
    · intro primaryOrder bodyOrder colors centers
      simp only [Pi.smul_apply, hkernel.2.2 primaryOrder bodyOrder colors centers]

/-- All positive arities up to the fixed calibration order. -/
abbrev PositiveArity (order : ℕ) :=
  {arity : Fin (order + 1) × Fin (order + 1) //
    1 ≤ arity.1.val + arity.2.val ∧ arity.1.val + arity.2.val ≤ order}

/-- The scalar is the complete degree-zero coefficient; positive degrees are
actual canonical kernel fibers rather than unconstrained coordinate arrays. -/
abbrev CoefficientSpace (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :=
  ℝ × ((arity : PositiveArity order) →
    canonicalKernels primary body arity.val.1.val arity.val.2.val)

instance coefficientSpace_finiteDimensional (primary : FiniteDist Primary)
    (body : FiniteDist Body) (order : ℕ) :
    FiniteDimensional ℝ (CoefficientSpace primary body order) := by infer_instance

/-- Subtract the actual conditional mean in a specified primary slot. -/
def centerPrimarySlot (primary : FiniteDist Primary) {r s : ℕ} (index : Fin r)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers => kernel colors centers -
    ∑ color, primary.weight color * kernel (Function.update colors index color) centers

omit [Fintype Body] in
theorem centerPrimarySlot_centered (primary : FiniteDist Primary) {r s : ℕ} (index : Fin r)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    PrimaryCenteredAt primary index (centerPrimarySlot primary index kernel) := by
  intro colors centers
  simp only [centerPrimarySlot, Function.update_idem, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, primary.sum_one, one_mul]
  ring

omit [Fintype Body] in
theorem centerPrimarySlot_of_centered (primary : FiniteDist Primary) {r s : ℕ} (index : Fin r)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (hkernel : PrimaryCenteredAt primary index kernel) : centerPrimarySlot primary index kernel = kernel := by
  funext colors centers
  simp only [centerPrimarySlot, hkernel colors centers, sub_zero]

omit [Fintype Body] in
theorem centerPrimarySlot_idempotent (primary : FiniteDist Primary) {r s : ℕ} (index : Fin r)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    centerPrimarySlot primary index (centerPrimarySlot primary index kernel) =
      centerPrimarySlot primary index kernel :=
  centerPrimarySlot_of_centered primary index _ (centerPrimarySlot_centered primary index kernel)

/-- Subtract the actual conditional mean in a specified body slot. -/
def centerBodySlot (body : FiniteDist Body) {r s : ℕ} (index : Fin s)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers => kernel colors centers -
    ∑ center, body.weight center * kernel colors (Function.update centers index center)

omit [Fintype Primary] in
theorem centerBodySlot_centered (body : FiniteDist Body) {r s : ℕ} (index : Fin s)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    BodyCenteredAt body index (centerBodySlot body index kernel) := by
  intro colors centers
  simp only [centerBodySlot, Function.update_idem, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, body.sum_one, one_mul]
  ring

omit [Fintype Primary] in
theorem centerBodySlot_of_centered (body : FiniteDist Body) {r s : ℕ} (index : Fin s)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (hkernel : BodyCenteredAt body index kernel) : centerBodySlot body index kernel = kernel := by
  funext colors centers
  simp only [centerBodySlot, hkernel colors centers, sub_zero]

omit [Fintype Primary] in
theorem centerBodySlot_idempotent (body : FiniteDist Body) {r s : ℕ} (index : Fin s)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    centerBodySlot body index (centerBodySlot body index kernel) = centerBodySlot body index kernel :=
  centerBodySlot_of_centered body index _ (centerBodySlot_centered body index kernel)

/-- The two different control alphabets have their specified independent
product-reference laws. This says nothing about endpoint independence. -/
def kernelMean (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) : ℝ :=
  ((FiniteDist.independent (fun _ : Fin r => primary)).prod
    (FiniteDist.independent (fun _ : Fin s => body))).expectation
      (fun inputs => kernel inputs.1 inputs.2)

theorem kernelMean_iterated (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    kernelMean primary body kernel =
      (FiniteDist.independent (fun _ : Fin r => primary)).expectation (fun colors =>
        (FiniteDist.independent (fun _ : Fin s => body)).expectation (kernel colors)) := by
  simp only [kernelMean, FiniteDist.expectation, FiniteDist.prod_weight,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem kernelMean_iterated_reverse (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    kernelMean primary body kernel =
      (FiniteDist.independent (fun _ : Fin s => body)).expectation (fun centers =>
        (FiniteDist.independent (fun _ : Fin r => primary)).expectation (fun colors => kernel colors centers)) := by
  rw [kernelMean_iterated]
  simp only [FiniteDist.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro centers _
  apply Finset.sum_congr rfl
  intro colors _
  ring

theorem kernelMean_const (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : ℕ) (constant : ℝ) :
    kernelMean primary body (fun (_ : Fin r → Primary) (_ : Fin s → Body) => constant) = constant := by
  simp only [kernelMean, FiniteDist.expectation, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]

theorem canonicalKernel_mean_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) (hdegree : 0 < r + s) :
    kernelMean primary body kernel.val = 0 := by
  by_cases hr : 0 < r
  · rw [kernelMean_iterated_reverse]
    have hmean (centers : Fin s → Body) :
        (FiniteDist.independent (fun _ : Fin r => primary)).expectation
          (fun colors => kernel.val colors centers) = 0 := by
      have hcenter : Hoeffding.CenteredAt (fun _ : Fin r => primary) ⟨0, hr⟩
          (fun colors => kernel.val colors centers) := fun colors => kernel.property.1 ⟨0, hr⟩ colors centers
      have h := Hoeffding.orthogonal_of_centered (fun _ : Fin r => primary) ∅ ⟨0, hr⟩ (by simp)
        (fun colors => kernel.val colors centers) (fun _ => 1) hcenter
        (by unfold Hoeffding.DependsOn; intros; rfl)
      simpa only [mul_one] using h
    simp_rw [hmean]
    simp only [FiniteDist.expectation, mul_zero, Finset.sum_const_zero]
  · have hs : 0 < s := by omega
    rw [kernelMean_iterated]
    have hmean (colors : Fin r → Primary) :
        (FiniteDist.independent (fun _ : Fin s => body)).expectation (kernel.val colors) = 0 := by
      have hcenter : Hoeffding.CenteredAt (fun _ : Fin s => body) ⟨0, hs⟩ (kernel.val colors) :=
        fun centers => kernel.property.2.1 ⟨0, hs⟩ colors centers
      have h := Hoeffding.orthogonal_of_centered (fun _ : Fin s => body) ∅ ⟨0, hs⟩ (by simp)
        (kernel.val colors) (fun _ => 1) hcenter
        (by unfold Hoeffding.DependsOn; intros; rfl)
      simpa only [mul_one] using h
    simp_rw [hmean]
    simp only [FiniteDist.expectation, mul_zero, Finset.sum_const_zero]

/-- The density-to-profile anchor action in the paired lift. The anchor is a
public Markov kernel into the safe body alphabet, not an observed hidden root. -/
def anchorProfile (primary : FiniteDist Primary) (anchor : Primary → FiniteDist Body)
    (score : Primary → ℝ) (center : Body) : ℝ :=
  ∑ color, primary.weight color * score color * (anchor color).weight center

theorem anchorProfile_mass (primary : FiniteDist Primary) (anchor : Primary → FiniteDist Body)
    (score : Primary → ℝ) :
    (∑ center, anchorProfile primary anchor score center) = primary.expectation score := by
  unfold anchorProfile
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one, FiniteDist.expectation]

/-- The manuscript's first-order paired density lift, including the true body
reference denominator. -/
def pairedLift (primary : FiniteDist Primary) (body : FiniteDist Body)
    (anchor : Primary → FiniteDist Body) (activation : ℝ) (score : Primary → ℝ)
    (inputs : Primary × Body) : ℝ :=
  score inputs.1 - activation * anchorProfile primary anchor score inputs.2 / body.weight inputs.2

theorem pairedLift_mean (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hbody : ∀ center, 0 < body.weight center) (anchor : Primary → FiniteDist Body)
    (activation : ℝ) (score : Primary → ℝ) :
    (primary.prod body).expectation (pairedLift primary body anchor activation score) =
      (1 - activation) * primary.expectation score := by
  have hcancel (color : Primary) (center : Body) :
      (primary.weight color * body.weight center) *
        (score color - activation * anchorProfile primary anchor score center / body.weight center) =
      primary.weight color * body.weight center * score color -
        primary.weight color * activation * anchorProfile primary anchor score center := by
    field_simp [ne_of_gt (hbody center)]
  simp only [FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type,
    pairedLift, hcancel, Finset.sum_sub_distrib]
  simp only [mul_right_comm (primary.weight _) (body.weight _) (score _),
    ← Finset.mul_sum, body.sum_one, mul_one, anchorProfile_mass,
    ← Finset.sum_mul, primary.sum_one, one_mul]
  unfold FiniteDist.expectation
  ring

theorem pairedLift_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hbody : ∀ center, 0 < body.weight center) (anchor : Primary → FiniteDist Body)
    (activation : ℝ) (score : Primary → ℝ) (hscore : primary.expectation score = 0) :
    (primary.prod body).expectation (pairedLift primary body anchor activation score) = 0 := by
  rw [pairedLift_mean primary body hbody anchor activation score, hscore, mul_zero]

/-- The actual ordered distinct-index average. Its two falling-factorial
normalizers retain the distinct primary-group and ordinary-body populations. -/
def twoPoolUStatistic {r s : ℕ} (primaryPool bodyPool : ℕ)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) :
    DensityKernel (Primary := Primary) (Body := Body) primaryPool bodyPool :=
  fun colors centers =>
    (∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
      kernel (colors ∘ selection.1) (centers ∘ selection.2)) /
        ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ))

theorem placedKernel_mean (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s primaryPool bodyPool : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (primarySelection : Fin r ↪ Fin primaryPool) (bodySelection : Fin s ↪ Fin bodyPool) :
    kernelMean primary body (fun colors centers =>
      kernel (colors ∘ primarySelection) (centers ∘ bodySelection)) = kernelMean primary body kernel := by
  rw [kernelMean_iterated, kernelMean_iterated]
  have hbody (colors : Fin primaryPool → Primary) :
      (FiniteDist.independent (fun _ : Fin bodyPool => body)).expectation
          (fun centers => kernel (colors ∘ primarySelection) (centers ∘ bodySelection)) =
        (FiniteDist.independent (fun _ : Fin s => body)).expectation (kernel (colors ∘ primarySelection)) :=
    CanonicalMoments.independent_embedding_expectation_general
      (fun _ : Fin bodyPool => body) bodySelection (kernel (colors ∘ primarySelection))
  simp_rw [hbody]
  exact CanonicalMoments.independent_embedding_expectation_general
    (fun _ : Fin primaryPool => primary) primarySelection
      (fun colors => (FiniteDist.independent (fun _ : Fin s => body)).expectation (kernel colors))

private theorem expectation_div_formula {State : Type*} [Fintype State]
    (law : FiniteDist State) (function : State → ℝ) (denominator : ℝ) :
    law.expectation (fun state => function state / denominator) = law.expectation function / denominator := by
  simp only [FiniteDist.expectation, mul_div_assoc, Finset.sum_div]

private theorem expectation_sum_formula {State Index : Type*} [Fintype State] [Fintype Index]
    (law : FiniteDist State) (function : Index → State → ℝ) :
    law.expectation (fun state => ∑ index, function index state) =
      ∑ index, law.expectation (function index) := by
  simp only [FiniteDist.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem twoPoolUStatistic_mean_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) (hdegree : 0 < r + s)
    (primaryPool bodyPool : ℕ) :
    kernelMean primary body (twoPoolUStatistic primaryPool bodyPool kernel.val) = 0 := by
  unfold kernelMean
  simp only [twoPoolUStatistic]
  rw [expectation_div_formula, expectation_sum_formula]
  have hterm (selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool)) :
      (((FiniteDist.independent (fun _ : Fin primaryPool => primary)).prod
        (FiniteDist.independent (fun _ : Fin bodyPool => body))).expectation
          (fun inputs => kernel.val (inputs.1 ∘ selection.1) (inputs.2 ∘ selection.2))) = 0 := by
    exact (placedKernel_mean primary body kernel.val selection.1 selection.2).trans
      (canonicalKernel_mean_zero primary body kernel hdegree)
  simp only [hterm, Finset.sum_const_zero, zero_div]

/-- Synthesis by the unpaired canonical statistics. The physical synthesis
additionally applies the paired lift in every primary slot; this definition
keeps that separate obligation visible. -/
def coefficientStatistic (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order primaryPool bodyPool : ℕ) (coefficient : CoefficientSpace primary body order) :
    DensityKernel (Primary := Primary) (Body := Body) primaryPool bodyPool :=
  fun colors centers => coefficient.1 + ∑ arity : PositiveArity order,
    twoPoolUStatistic primaryPool bodyPool (coefficient.2 arity).val colors centers

/-- The scalar coordinate is exactly the expectation of the complete finite
sum of canonical U-statistics. All positive arities have already been proved
to integrate to zero under this same reference. -/
theorem coefficientStatistic_mean (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order primaryPool bodyPool : ℕ) (coefficient : CoefficientSpace primary body order) :
    kernelMean primary body (coefficientStatistic primary body order primaryPool bodyPool coefficient) =
      coefficient.1 := by
  have hpositive : kernelMean primary body
      (fun colors centers => ∑ arity : PositiveArity order,
        twoPoolUStatistic primaryPool bodyPool (coefficient.2 arity).val colors centers) = 0 := by
    unfold kernelMean
    rw [expectation_sum_formula]
    apply Finset.sum_eq_zero
    intro arity _
    exact twoPoolUStatistic_mean_zero primary body (coefficient.2 arity)
      (by have := arity.property.1; omega) primaryPool bodyPool
  have hadd : kernelMean primary body
      (coefficientStatistic primary body order primaryPool bodyPool coefficient) =
      kernelMean primary body
          (fun (_ : Fin primaryPool → Primary) (_ : Fin bodyPool → Body) => coefficient.1) +
        kernelMean primary body (fun colors centers => ∑ arity : PositiveArity order,
          twoPoolUStatistic primaryPool bodyPool (coefficient.2 arity).val colors centers) := by
    simp only [coefficientStatistic, kernelMean, FiniteDist.expectation, mul_add,
      Finset.sum_add_distrib]
  rw [hadd, kernelMean_const, hpositive, add_zero]

theorem coefficientStatistic_mass_one (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order primaryPool bodyPool : ℕ) (coefficient : CoefficientSpace primary body order)
    (hscalar : coefficient.1 = 1) :
    kernelMean primary body (coefficientStatistic primary body order primaryPool bodyPool coefficient) = 1 := by
  rw [coefficientStatistic_mean, hscalar]

end

end CurrentAFT.ControlCoordinates

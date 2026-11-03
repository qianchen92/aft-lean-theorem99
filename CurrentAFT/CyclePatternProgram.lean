import CurrentAFT.WindowGaussianSampler
import CurrentAFT.ProtectedCycle
import CurrentAFT.CycleSelections
import AFT.CompatibleFibers
import AFT.FiniteIndependentSampling
import AFT.MixedAveraging
import CurrentAFT.TensorPublicProjection

/-! # Fixed-order sparse cycle programs

Only latent edges touched by the supplied root positions are enumerated.
Adjacent selected roots read the same stored edge and the predecessor of
the first body position is still the closing edge. The program is a
finite rational sum, with its exact whole-body semantics proved below.
This is not yet the complete local physical-response evaluator.
-/
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def touched {body order : ℕ} (sites : Fin order → Fin body) : Finset (Fin body) :=
  Finset.univ.image sites ∪ Finset.univ.image (fun slot => (finRotate body).symm (sites slot))

def currentEdge {body order : ℕ} (sites : Fin order → Fin body) (slot : Fin order) : touched sites :=
  ⟨sites slot, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩)⟩

def previousEdge {body order : ℕ} (sites : Fin order → Fin body) (slot : Fin order) : touched sites :=
  ⟨(finRotate body).symm (sites slot), Finset.mem_union_right _ (Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩)⟩

def roots {Scalar Group : Type*} [AddGroup Group] {body order : ℕ}
    (sites : Fin order → Fin body) (value : Scalar → Group) (latent : touched sites → Scalar) : Fin order → Group :=
  fun slot => value (latent (currentEdge sites slot)) - value (latent (previousEdge sites slot))

/-- This program uses actual rational multiplication and finite sums on
the active edge alphabet. It never iterates over all body-edge words. -/
def evaluate {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group] {body order : ℕ}
    (sites : Fin order → Fin body) (weight : Scalar → ℚ) (value : Scalar → Group)
    (test : (Fin order → Group) → ℚ) : ℚ :=
  ∑ latent : touched sites → Scalar, (∏ edge, weight (latent edge)) * test (roots sites value latent)

theorem touched_card {body order : ℕ} (sites : Fin order → Fin body) : (touched sites).card ≤ 2 * order := by
  apply (Finset.card_union_le _ _).trans
  have hcurrent := Finset.card_image_le (s := (Finset.univ : Finset (Fin order))) (f := sites)
  have hprevious := Finset.card_image_le (s := (Finset.univ : Finset (Fin order)))
    (f := fun slot => (finRotate body).symm (sites slot))
  simp only [Finset.card_univ, Fintype.card_fin] at hcurrent hprevious
  omega

theorem state_count {Scalar : Type*} [Fintype Scalar] [Nonempty Scalar] {body order : ℕ}
    (sites : Fin order → Fin body) : Fintype.card (touched sites → Scalar) ≤ (Fintype.card Scalar)^(2*order) := by
  rw [Fintype.card_fun, Fintype.card_coe]
  exact Nat.pow_le_pow_right (Fintype.card_pos (α := Scalar)) (touched_card sites)

theorem window_state_count {body order cutoff : ℕ} (sites : Fin order → Fin body) :
    Fintype.card (touched sites → Window cutoff) ≤ (2*cutoff+1)^(2*order) := by
  letI : Nonempty (Window cutoff) := ⟨windowZero cutoff⟩
  have h := state_count (Scalar := Window cutoff) sites
  have hcard : Fintype.card (Window cutoff) = 2*cutoff+1 := by
    rw [← Fintype.card_congr (FiniteConvolutionProgram.windowIndexEquiv cutoff), Fintype.card_fin]
  simpa only [hcard] using h

def gaussianEvaluate {body order : ℕ} (security cutoff bits : ℕ) (sites : Fin order → Fin body)
    (test : (Fin order → ℤ) → ℚ) : ℚ :=
  evaluate sites (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits)
    (fun point : Window cutoff => point.val) test

/-- Genuine distinct selections are enumerated at fixed order. The
normalizer is computed from their finite count, rather than supplied. -/
def selectionEquiv (body order : ℕ) :
    (Fin order ↪ Fin body) ≃ {sites : Fin order → Fin body // Function.Injective sites} where
  toFun sites := ⟨sites, sites.injective⟩
  invFun sites := ⟨sites.val, sites.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def selectionFintype (body order : ℕ) : Fintype (Fin order ↪ Fin body) := by
  letI : DecidablePred (Function.Injective (α := Fin order) (β := Fin body)) :=
    fun sites => by unfold Function.Injective; infer_instance
  exact Fintype.ofEquiv {sites : Fin order → Fin body // Function.Injective sites} (selectionEquiv body order).symm

def averagedEvaluate (security cutoff bits body order : ℕ)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) : ℚ :=
  letI := selectionFintype body order
  (Fintype.card (Fin order ↪ Fin body) : ℚ)⁻¹ *
    ∑ sites : Fin order ↪ Fin body, gaussianEvaluate security cutoff bits sites (test sites)

theorem pattern_state_count (body order cutoff : ℕ) :
    (∑ sites : Fin order ↪ Fin body, Fintype.card (touched sites → Window cutoff)) ≤
      body^order * (2*cutoff+1)^(2*order) := by
  calc
    _ ≤ ∑ _sites : Fin order ↪ Fin body, (2*cutoff+1)^(2*order) :=
      Finset.sum_le_sum (fun sites _ => window_state_count sites)
    _ = body.descFactorial order * (2*cutoff+1)^(2*order) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow body order)

noncomputable section
open scoped Classical

theorem restricted_expectation {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℝ) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
      test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot))))) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation (fun latent => test (roots sites value latent)) := by
  let embedding : touched sites ↪ Fin body := ⟨Subtype.val, Subtype.val_injective⟩
  have h := CanonicalMoments.independent_embedding_expectation_general
    (fun _ : Fin body => source) embedding (fun latent => test (roots sites value latent))
  apply Eq.trans (TensorPublicProjection.independent_decision_expectation
    (inferInstance : DecidableEq (Fin body)) (Classical.decEq _) (fun _ => source) _)
  apply Eq.trans h
  exact TensorPublicProjection.independent_decision_expectation (Classical.decEq _)
    (inferInstance : DecidableEq (touched sites)) (fun _ => source) _

/-- The sparse rational program is exactly the complete independent latent
experiment for the supplied rational reference, for arbitrary joint tests. -/
theorem evaluate_local {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : touched sites => source)).expectation
        (fun latent => (test (roots sites value latent) : ℝ)) := by
  simp only [evaluate, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, hweight,
    FiniteDist.expectation, FiniteDist.independent]

theorem evaluate_semantics {Scalar Group : Type*} [Fintype Scalar] [AddGroup Group]
    {body order : ℕ} (sites : Fin order → Fin body) (source : FiniteDist Scalar)
    (weight : Scalar → ℚ) (hweight : ∀ scalar, (weight scalar : ℝ) = source.weight scalar)
    (value : Scalar → Group) (test : (Fin order → Group) → ℚ) :
    (evaluate sites weight value test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
        (test (fun slot => value (latent (sites slot)) - value (latent ((finRotate body).symm (sites slot)))) : ℝ)) := by
  exact (evaluate_local sites source weight hweight value test).trans
    (restricted_expectation sites source value (fun input => (test input : ℝ))).symm

theorem gaussianEvaluate_semantics {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) :
    (gaussianEvaluate security cutoff bits sites test : ℝ) =
      (FiniteDist.independent (fun _ : Fin body => windowApproxLaw
        (WindowGaussianSampler.squaredWidth security) cutoff bits)).expectation (fun latent =>
          (test (fun slot => (latent (sites slot)).val - (latent ((finRotate body).symm (sites slot))).val) : ℝ)) :=
  evaluate_semantics sites _ _ (fun _ => rfl) _ test

theorem expectation_difference_le_l1 {State : Type*} [Fintype State] (first second : FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (htest : ∀ state, |test state| ≤ bound) :
    |first.expectation test - second.expectation test| ≤
      bound * ∑ state, |first.weight state - second.weight state| := by
  unfold FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ state, (first.weight state - second.weight state) * test state| := by
      congr 1
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ ≤ ∑ state, |(first.weight state - second.weight state) * test state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, bound * |first.weight state - second.weight state| := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (htest state) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Gaussian approximation is charged only on the at most `2*order`
active edges. There is no factor equal to the whole body population. -/
theorem gaussianEvaluate_error {body order : ℕ} (security cutoff bits : ℕ)
    (sites : Fin order → Fin body) (test : (Fin order → ℤ) → ℚ) (bound : ℝ)
    (hbound : 0 ≤ bound) (htest : ∀ roots, |(test roots : ℝ)| ≤ bound) :
    |(gaussianEvaluate security cutoff bits sites test : ℝ) -
      (FiniteDist.independent (fun _ : Fin body => windowGaussian (Parameters.sourceWidth security) cutoff)).expectation
        (fun latent => (test (fun slot => (latent (sites slot)).val -
          (latent ((finRotate body).symm (sites slot))).val) : ℝ))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits := by
  let first := windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits
  let second := windowGaussian (Parameters.sourceWidth security) cutoff
  have hscalar : (∑ point, |first.weight point - second.weight point|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hproduct := FiniteDist.l1_independent_le (fun _ : touched sites => first) (fun _ => second)
  have hlocal : (∑ latent,
      |(FiniteDist.independent (fun _ : touched sites => first)).weight latent -
        (FiniteDist.independent (fun _ : touched sites => second)).weight latent|) ≤
      (2 * order : ℕ) / (2 : ℝ)^bits := by
    apply hproduct.trans
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    calc
      _ ≤ ((touched sites).card : ℝ) * (1 / (2 : ℝ)^bits) :=
        mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)
      _ ≤ (2 * order : ℕ) * (1 / (2 : ℝ)^bits) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (touched_card sites)) (by positivity)
      _ = _ := by ring
  have hprogram := evaluate_local sites first
    (windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits) (fun _ => rfl)
    (fun point : Window cutoff => point.val) test
  have htrue := restricted_expectation sites second (fun point : Window cutoff => point.val)
    (fun input => (test input : ℝ))
  calc
    _ = |(FiniteDist.independent (fun _ : touched sites => first)).expectation
        (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ)) -
      (FiniteDist.independent (fun _ : touched sites => second)).expectation
        (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ))| :=
      congrArg abs (congrArg₂ (· - ·) hprogram htrue)
    _ ≤ _ := (expectation_difference_le_l1 _ _
      (fun latent => (test (roots sites (fun point : Window cutoff => point.val) latent) : ℝ))
      bound (fun _ => htest _)).trans ((mul_le_mul_of_nonneg_left hlocal hbound).trans_eq (by ring))

theorem edge_pattern_error {body order : ℕ} (security bits : ℕ) (sites : Fin order → Fin body)
    (test : (Fin order → ℤ) → ℚ) (bound : ℝ) (hbound : 0 ≤ bound)
    (htest : ∀ roots, |(test roots : ℝ)| ≤ bound) :
    |(gaussianEvaluate security (edgeCutoff security) bits sites test : ℝ) -
      (FiniteDist.independent (fun _ : Fin body => edgeLaw security)).expectation (fun latent =>
        (test (fun slot => (latent (sites slot)).val - (latent ((finRotate body).symm (sites slot))).val) : ℝ))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits :=
  gaussianEvaluate_error security _ bits sites test bound hbound htest

theorem averagedEvaluate_cast (security cutoff bits body order : ℕ) (hroom : order ≤ body)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) :
    (averagedEvaluate security cutoff bits body order test : ℝ) =
      (CycleSelections.selectionLaw body order hroom).expectation
        (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ)) := by
  have henumeration (first second : Fintype (Fin order ↪ Fin body)) (value : (Fin order ↪ Fin body) → ℝ) :
      ((@Fintype.card (Fin order ↪ Fin body) first : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) first, value state) =
        ((@Fintype.card (Fin order ↪ Fin body) second : ℝ)⁻¹ * ∑ state ∈ @Finset.univ (Fin order ↪ Fin body) second, value state) := by
    cases Subsingleton.elim first second
    rfl
  unfold averagedEvaluate
  simp only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum,
    CycleSelections.selectionLaw, FiniteDist.expectation, FiniteDist.uniform_weight, ← Finset.mul_sum]
  exact henumeration (selectionFintype body order) (inferInstance : Fintype (Fin order ↪ Fin body))
    (fun sites => (gaussianEvaluate security cutoff bits sites (test sites) : ℝ))

theorem averaged_edge_error (security bits body order : ℕ) (hroom : order ≤ body)
    (test : (Fin order ↪ Fin body) → (Fin order → ℤ) → ℚ) (bound : ℝ)
    (hbound : 0 ≤ bound) (htest : ∀ sites roots, |(test sites roots : ℝ)| ≤ bound) :
    |(averagedEvaluate security (edgeCutoff security) bits body order test : ℝ) -
      (CycleSelections.selectionLaw body order hroom).expectation (fun sites =>
        (FiniteDist.independent (fun _ : Fin body => edgeLaw security)).expectation (fun latent =>
          (test sites (fun slot => (latent (sites slot)).val -
            (latent ((finRotate body).symm (sites slot))).val) : ℝ)))| ≤
      (2 * order : ℕ) * bound / (2 : ℝ)^bits := by
  rw [averagedEvaluate_cast security (edgeCutoff security) bits body order hroom]
  rw [← FiniteDist.expectation_sub]
  exact FiniteDist.abs_average_le_bound _ _ _ (fun sites =>
    edge_pattern_error security bits sites (test sites) bound hbound (htest sites))

end
end CurrentAFT.CyclePatternProgram

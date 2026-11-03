import CurrentAFT.CurrentFlagProgram
import AFT.BinaryChartIteration

/-!
# Finite rational iteration for the actual chart response

The matrix is minus the literal deletion operator, so the stored iteration
`rhs - matrix * previous` is the Neumann recurrence.  Its limit is the
canonical rational ideal used by `currentLaw`, rather than a separately
chosen positive table.  Matrix-entry construction and bit costs are kept
separate from the convergence proof.
-/

namespace CurrentAFT.CurrentFlagIteration

open AFT AFT.BoundaryCalibration AFT.RationalNumerics
open AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1200000

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I] [DecidableEq Ω]

def iterationMatrix (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    Matrix Ω Ω ℚ :=
  LinearMap.toMatrix' (responseQ features allowed safe - LinearMap.id)

def iterate (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop)
    (target : Ω → ℚ) (steps : ℕ) : Ω → ℚ :=
  linearIteration (iterationMatrix features allowed safe) target steps

theorem matrixApply_eq (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    matrixApply (iterationMatrix features allowed safe) profile =
      responseQ features allowed safe profile - profile := by
  change (LinearMap.toMatrix' (responseQ features allowed safe - LinearMap.id)).mulVec profile = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem iterate_succ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    realVector (iterate features allowed safe target (steps + 1)) =
      realVector target + deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe
        (realVector (iterate features allowed safe target steps)) := by
  have he : iterate features allowed safe target (steps + 1) =
      target - (responseQ features allowed safe (iterate features allowed safe target steps) -
        iterate features allowed safe target steps) := by
    exact congrArg (fun value => target - value) (matrixApply_eq features allowed safe _)
  rw [he]
  have hr := responseQ_cast features allowed safe (iterate features allowed safe target steps)
  funext x
  have hx := congrFun hr x
  simp only [realVector, Pi.sub_apply, Rat.cast_sub, Pi.add_apply] at hx ⊢
  linarith

theorem iterate_error [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hop : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ bound)
    (target : Ω → ℚ) (steps : ℕ) :
    ‖realVector (iterate features allowed safe target steps) - realVector (solve features allowed safe target)‖ ≤
      bound ^ steps * ‖realVector (solve features allowed safe target)‖ := by
  let D := deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe
  let exactValue := realVector (solve features allowed safe target)
  have hfixed : realVector target + D exactValue = exactValue := by
    have h := congrArg realVector (solve_equation features allowed safe hD target)
    rw [responseQ_cast] at h
    change exactValue - D exactValue = realVector target at h
    linear_combination -h
  induction steps with
  | zero =>
    have hz : realVector (0 : Ω → ℚ) = 0 := by ext x; simp [realVector]
    simp only [iterate, linearIteration, hz, zero_sub, norm_neg, pow_zero, one_mul, le_refl]
  | succ steps ih =>
    have hid : realVector (iterate features allowed safe target (steps + 1)) - exactValue =
        D (realVector (iterate features allowed safe target steps) - exactValue) := by
      rw [iterate_succ_cast, map_sub]
      change realVector target + D _ - exactValue = D _ - D exactValue
      linear_combination hfixed
    change ‖realVector (iterate features allowed safe target (steps + 1)) - exactValue‖ ≤ _
    rw [hid]
    calc
      ‖D (realVector (iterate features allowed safe target steps) - exactValue)‖ ≤
          bound * ‖realVector (iterate features allowed safe target steps) - exactValue‖ :=
        (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      _ ≤ bound * (bound ^ steps * ‖exactValue‖) := mul_le_mul_of_nonneg_left ih hbound
      _ = bound ^ (steps + 1) * ‖exactValue‖ := by rw [pow_succ]; ring

theorem iterate_error_quarter [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4)
    (target : Ω → ℚ) (steps : ℕ) :
    ‖realVector (iterate features allowed safe target steps) - realVector (solve features allowed safe target)‖ ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) * ‖realVector target‖) := by
  have hD := hquarter.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)
  apply (iterate_error features allowed safe hD (1 / 4) (by norm_num) hquarter target steps).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [solve_cast features allowed safe hD]
  exact neumannSolve_norm _ hD hquarter _

def regularIterate (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) : Ω → ℚ :=
  fun x => if safe x then iterate features allowed safe
    (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) steps x else 0

theorem regularIterate_error [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4)
    (steps : ℕ) (point : Ω) :
    |(regularIterate features allowed line safe atom spike steps point : ℝ) -
        (regularDensityQ features allowed line safe atom spike point : ℝ)| ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) *
        ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike)‖) := by
  by_cases hs : safe point
  · simp only [regularIterate, regularDensityQ, if_pos hs]
    exact (norm_le_pi_norm
      (realVector (iterate features allowed safe _ steps) - realVector (solve features allowed safe _)) point).trans
        (iterate_error_quarter features allowed safe hquarter _ steps)
  · simp only [regularIterate, regularDensityQ, if_neg hs, Rat.cast_zero, sub_self, abs_zero]
    positivity

section ActualParameters

variable {F J : Type*} [Field F] [Fintype F] [Fintype J]

theorem affine_quarter (inputs : J → F × F) (hinj : Function.Injective inputs)
    (allowed : J → Finset F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card J + 1) * δ ≤ 1 / 4) :
    ‖deletion (chartProjection (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed)
      (affineSafe inputs allowed)‖ ≤ 1 / 4 := by
  let p := FiniteDist.uniform (Chart F)
  have hfeature (i : J) : p.map (affineFeatures inputs i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : J) (hij : i ≠ j) :
      p.map (fun x => (affineFeatures inputs i x, affineFeatures inputs j x)) =
        (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : J) : p.map (fun x => (affineFeatures inputs i x, x.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase 0)) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) = affineDeletionBudget allowed := by
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator (affineSafe inputs allowed)) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p (fun chart => chart.2.1) (Finset.univ.erase 0)
      (affineFeatures inputs) allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (affineFeatures inputs i) (badIndicator (affineSafe inputs allowed)) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p _ _ (affineFeatures inputs) allowed hfeature hpair hauxpair i c hc
  exact (chartDeletion_norm p (affineFeatures inputs) allowed (affineSafe inputs allowed)
    δ hδ hglobal hconditional).trans hsmall

local instance iterationPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

theorem current_quarter (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) :
    ‖deletion (chartProjection (FiniteDist.uniform (Chart (ZMod (Parameters.modulus security))))
      (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))
      (affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))‖ ≤ 1 / 4 := by
  have hb := leg_budget_conditions security
  exact affine_quarter _ (protectedInputs_injective _ _ (leg_input_separation security)) _
    (legDeletionUpper security) hb.1 (protectedPalette_current_budget security baseline hbaseline) hb.2.2.1

end ActualParameters

end
end CurrentAFT.CurrentFlagIteration

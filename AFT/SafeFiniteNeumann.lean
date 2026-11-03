import AFT.SourceSmoothing

/-! # Finite compactly smoothed root inverse with its exact residual -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G σ : Type*} [Fintype G] [AddCommGroup G] [Fintype σ]

omit [AddCommGroup G] in
theorem countingL2_sum {ι : Type*} (indices : Finset ι) (profiles : ι → G → ℝ) :
    countingL2 (∑ index ∈ indices, profiles index) ≤ ∑ index ∈ indices, countingL2 (profiles index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [countingL2]
  | @insert index indices hi ih =>
    simp only [Finset.sum_insert hi]
    exact (countingL2_add _ _).trans (add_le_add le_rfl ih)

omit [AddCommGroup G] in
theorem operator_power_L2_le (operator : Module.End ℝ (G → ℝ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (hoperator : ∀ profile, countingL2 (operator profile) ≤ bound * countingL2 profile)
    (order : ℕ) (profile : G → ℝ) :
    countingL2 ((operator ^ order) profile) ≤ bound ^ order * countingL2 profile := by
  induction order with
  | zero => simp
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hoperator _).trans ((mul_le_mul_of_nonneg_left ih hbound).trans_eq (by ring))

theorem probability_defect_L2_le (source : FiniteDist G) (profile : G → ℝ) :
    countingL2 ((1 - convolution source.weight) profile) ≤ 2 * countingL2 profile := by
  change countingL2 (profile + -(convolution source.weight profile)) ≤ _
  exact (countingL2_add _ _).trans (by
    rw [countingL2_neg]
    linarith [probability_convolution_L2_le source profile])

theorem probability_power_L2_le (source : FiniteDist G) (order : ℕ) (profile : G → ℝ) :
    countingL2 ((convolution source.weight ^ order) profile) ≤ countingL2 profile := by
  simpa only [one_pow, one_mul] using operator_power_L2_le (convolution source.weight) 1 (by norm_num)
    (fun profile => by simpa only [one_mul] using probability_convolution_L2_le source profile) order profile

/-- The certificate is a finite sum of true root-defect translates of the
smoothed target. No infinite inverse or limiting sampling law is used. -/
noncomputable def compactRootInput (root smooth : FiniteDist G) (depth : ℕ) (seed : G → ℝ) : G → ℝ :=
  finiteCorrection (convolution root.weight - 1) depth ((convolution smooth.weight ^ (depth + 1)) seed)

/-- The exact residual retains every finite root-source term. -/
theorem compactRootInput_residual (root smooth : FiniteDist G) (depth : ℕ) (seed : G → ℝ) :
    convolution root.weight (compactRootInput root smooth depth seed) =
      (convolution smooth.weight ^ (depth + 1)) seed -
        (((1 - convolution root.weight) * convolution smooth.weight) ^ (depth + 1)) seed := by
  have hcomm : Commute (1 - convolution root.weight) (convolution smooth.weight) :=
    (Commute.one_left _).sub_left (convolution_commute _ _)
  have hh := finiteCorrection_apply (convolution root.weight - 1) depth
    ((convolution smooth.weight ^ (depth + 1)) seed)
  have ha : (1 + (convolution root.weight - 1) : Module.End ℝ (G → ℝ)) = convolution root.weight := by abel
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  rw [ha, hb] at hh
  rw [hcomm.mul_pow, Module.End.mul_apply]
  exact hh

/-- Fixed truncation costs only a fixed scalar, independently of the
palette size and of the exact finite source law. -/
theorem compactRootInput_L2_le (root smooth : FiniteDist G) (depth : ℕ) (seed : G → ℝ) :
    countingL2 (compactRootInput root smooth depth seed) ≤
      (∑ index ∈ Finset.range (depth + 1), (2 : ℝ) ^ index) * countingL2 seed := by
  let target := (convolution smooth.weight ^ (depth + 1)) seed
  have htarget := probability_power_L2_le smooth (depth + 1) seed
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  have heq : compactRootInput root smooth depth seed =
      ∑ index ∈ Finset.range (depth + 1), ((1 - convolution root.weight) ^ index) target := by
    simp only [compactRootInput, finiteCorrection, LinearMap.sum_apply, hb, target]
  rw [heq]
  calc
    _ ≤ ∑ index ∈ Finset.range (depth + 1), countingL2 (((1 - convolution root.weight) ^ index) target) :=
      countingL2_sum _ _
    _ ≤ ∑ index ∈ Finset.range (depth + 1), (2 : ℝ) ^ index * countingL2 seed := by
      apply Finset.sum_le_sum
      intro index _
      exact (operator_power_L2_le _ 2 (by norm_num) (probability_defect_L2_le root) index target).trans
        (mul_le_mul_of_nonneg_left htarget (by positivity))
    _ = _ := by rw [Finset.sum_mul]

variable [DecidableEq G]

/-- For the real compact box and actual bounded root shifts, every retained
source term is explicit and the last residual gains one smoothing factor
per Neumann step. -/
theorem box_compactRootInput_residual_L2_le (embedding : ℤ →+ G) (start : ℤ) (width : ℕ) (hw : width ≠ 0)
    (source : FiniteDist σ) (firstShift secondShift : σ → ℤ) (shiftBound : ℝ)
    (hbound : 0 ≤ shiftBound)
    (hshift : ∀ sample, (firstShift sample).natAbs + (secondShift sample).natAbs ≤ shiftBound)
    (depth : ℕ) (seed : G × G → ℝ) :
    let root := source.map (fun sample => (embedding (firstShift sample), embedding (secondShift sample)))
    let smooth := boxDistribution embedding start width hw
    countingL2 (convolution root.weight (compactRootInput root smooth depth seed) -
      (convolution smooth.weight ^ (depth + 1)) seed) ≤
      (2 * shiftBound / width) ^ (depth + 1) * countingL2 seed := by
  dsimp only
  rw [compactRootInput_residual]
  have heq (first second : G × G → ℝ) : first - second - first = -second := by abel
  rw [heq, countingL2_neg]
  exact operator_power_L2_le _ (2 * shiftBound / width) (by positivity)
    (box_source_defect_L2_le embedding start width hw source firstShift secondShift shiftBound hshift)
    (depth + 1) seed

end AFT.SafeConvolution

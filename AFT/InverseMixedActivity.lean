import AFT.PrimaryParameterBounds

/-!
# The actual local inverse on arbitrary finite Hilbert fibers

Scalar profile bounds extend to arbitrary remaining-coordinate weights.
Applying the inverse separately in each remaining fiber and using its exact
operator equation yields the inverse mixed-activity bound without a
palette-dependent norm-equivalence constant.
-/

namespace AFT

open scoped BigOperators

section FiberTriangle

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem weightedDensity_sqrt_add_le (weight first second : ι → ℝ)
    (hw : ∀ color, 0 ≤ weight color) :
    Real.sqrt (∑ color, weight color * (first color + second color) ^ 2) ≤
      Real.sqrt (∑ color, weight color * first color ^ 2) +
        Real.sqrt (∑ color, weight color * second color ^ 2) := by
  have hf : 0 ≤ ∑ color, weight color * first color ^ 2 :=
    Finset.sum_nonneg fun color _ => mul_nonneg (hw color) (sq_nonneg _)
  have hg : 0 ≤ ∑ color, weight color * second color ^ 2 :=
    Finset.sum_nonneg fun color _ => mul_nonneg (hw color) (sq_nonneg _)
  have hc : (∑ color, weight color * first color * second color) ^ 2 ≤
      (∑ color, weight color * first color ^ 2) *
        ∑ color, weight color * second color ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _; exact mul_nonneg (hw color) (sq_nonneg _)
    · intro color _; exact mul_nonneg (hw color) (sq_nonneg _)
    · intro color _; ring
  have hcross := Real.le_sqrt_of_sq_le hc
  rw [Real.sqrt_mul hf] at hcross
  have heq : (∑ color, weight color * (first color + second color) ^ 2) =
      (∑ color, weight color * first color ^ 2) +
        (∑ color, weight color * second color ^ 2) +
          2 * ∑ color, weight color * first color * second color := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro color _; ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [heq]
    nlinarith [Real.sq_sqrt hf, Real.sq_sqrt hg]

theorem integratedFiberNorm_add_le (primary : ι → ℝ) (remaining : κ → ℝ)
    (first second : ι → κ → ℝ) (hp : ∀ color, 0 ≤ primary color)
    (hq : ∀ rest, 0 ≤ remaining rest) :
    integratedFiberNorm primary remaining (first + second) ≤
      integratedFiberNorm primary remaining first + integratedFiberNorm primary remaining second := by
  have h := weightedDensity_sqrt_add_le (fun pair : κ × ι => remaining pair.1 * primary pair.2)
    (fun pair => first pair.2 pair.1) (fun pair => second pair.2 pair.1)
    (fun pair => mul_nonneg (hq pair.1) (hp pair.2))
  simpa only [integratedFiberNorm, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc,
    Pi.add_apply] using h

theorem fixedFiberNorm_add_le (remaining : κ → ℝ) (first second : ι → κ → ℝ)
    (hq : ∀ rest, 0 ≤ remaining rest) :
    fixedFiberNorm remaining (first + second) ≤
      fixedFiberNorm remaining first + fixedFiberNorm remaining second := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro color
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := weightedDensity_sqrt_add_le remaining (first color) (second color) hq
  have hf := norm_le_pi_norm (fun color => Real.sqrt (∑ rest, remaining rest * first color rest ^ 2)) color
  have hg := norm_le_pi_norm (fun color => Real.sqrt (∑ rest, remaining rest * second color rest ^ 2)) color
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hf hg
  exact h.trans (add_le_add hf hg)

theorem coordinateActivity_add_le (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (first second : ι → κ → ℝ) (hrate : 0 ≤ rate)
    (hp : ∀ color, 0 ≤ primary color) (hq : ∀ rest, 0 ≤ remaining rest) :
    coordinateActivity rate primary remaining (first + second) ≤
      coordinateActivity rate primary remaining first + coordinateActivity rate primary remaining second := by
  have hi := mul_le_mul_of_nonneg_left (integratedFiberNorm_add_le primary remaining first second hp hq) hrate
  have hf := mul_le_mul_of_nonneg_left (fixedFiberNorm_add_le remaining first second hq) (sq_nonneg rate)
  unfold coordinateActivity
  linarith

@[simp] theorem coordinateActivity_neg (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) :
    coordinateActivity rate primary remaining (-kernel) = coordinateActivity rate primary remaining kernel := by
  simp [coordinateActivity, integratedFiberNorm, fixedFiberNorm]

end FiberTriangle

section ProfileAmplification

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Apply an actual profile operator to the distinguished density coordinate. -/
noncomputable def partialProfileOperator (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (kernel : ι → κ → ℝ) : ι → κ → ℝ :=
  fun output rest => operator (fun input => primary input * kernel input rest) output / primary output

omit [Fintype κ] in
theorem profileSquareNorm_densityProfile (primary density : ι → ℝ)
    (hp : ∀ color, 0 < primary color) :
    profileSquareNorm primary (fun color => primary color * density color) =
      ∑ color, primary color * density color ^ 2 := by
  apply Finset.sum_congr rfl
  intro color _
  have hn := ne_of_gt (hp color)
  field_simp

theorem partialProfileOperator_integrated_le (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ) (bound : ℝ)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest) (hb : 0 ≤ bound)
    (hscalar : ∀ profile, Real.sqrt (profileSquareNorm primary (operator profile)) ≤
      bound * Real.sqrt (profileSquareNorm primary profile)) :
    integratedFiberNorm primary remaining (partialProfileOperator operator primary kernel) ≤
      bound * integratedFiberNorm primary remaining kernel := by
  have hs (rest : κ) :
      (∑ color, primary color * partialProfileOperator operator primary kernel color rest ^ 2) ≤
        bound ^ 2 * ∑ color, primary color * kernel color rest ^ 2 := by
    have h := hscalar (fun color => primary color * kernel color rest)
    have hn := profileSquareNorm_nonneg primary (operator (fun color => primary color * kernel color rest))
      (fun color => (hp color).le)
    have hm := profileSquareNorm_nonneg primary (fun color => primary color * kernel color rest)
      (fun color => (hp color).le)
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hb (Real.sqrt_nonneg _))).mpr h
    rw [mul_pow, Real.sq_sqrt hn, Real.sq_sqrt hm,
      profileSquareNorm_densityProfile primary _ hp] at hh
    simpa only [partialProfileOperator, ← densityScore_square, densitySquareNorm] using hh
  have hh := Finset.sum_le_sum fun rest (_ : rest ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hs rest) (hq rest)
  have hsum : (∑ rest, remaining rest * ∑ color,
      primary color * partialProfileOperator operator primary kernel color rest ^ 2) ≤
        bound ^ 2 * ∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2 := by
    simpa only [Finset.mul_sum, mul_left_comm] using hh
  unfold integratedFiberNorm
  exact (Real.sqrt_le_sqrt hsum).trans_eq (by rw [Real.sqrt_mul (sq_nonneg bound), Real.sqrt_sq hb])

theorem partialProfileOperator_fixed_le (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ) (bound : ℝ)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest) (hb : 0 ≤ bound)
    (hscalar : ∀ profile, ‖fun color => operator profile color / primary color‖ ≤
      bound * Real.sqrt (profileSquareNorm primary profile)) :
    fixedFiberNorm remaining (partialProfileOperator operator primary kernel) ≤
      bound * integratedFiberNorm primary remaining kernel := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))).mpr
  intro output
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs (rest : κ) : partialProfileOperator operator primary kernel output rest ^ 2 ≤
      bound ^ 2 * ∑ color, primary color * kernel color rest ^ 2 := by
    have h := (norm_le_pi_norm (fun color => operator (fun color => primary color * kernel color rest) color /
      primary color) output).trans (hscalar (fun color => primary color * kernel color rest))
    rw [Real.norm_eq_abs] at h
    have hm := profileSquareNorm_nonneg primary (fun color => primary color * kernel color rest)
      (fun color => (hp color).le)
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hb (Real.sqrt_nonneg _))).mpr h
    rw [sq_abs, mul_pow, Real.sq_sqrt hm, profileSquareNorm_densityProfile primary _ hp] at hh
    exact hh
  have hh := Finset.sum_le_sum fun rest (_ : rest ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hs rest) (hq rest)
  have hsum : (∑ rest, remaining rest * partialProfileOperator operator primary kernel output rest ^ 2) ≤
      bound ^ 2 * ∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2 := by
    simpa only [Finset.mul_sum, mul_left_comm] using hh
  exact (Real.sqrt_le_sqrt hsum).trans_eq (by rw [Real.sqrt_mul (sq_nonneg bound), Real.sqrt_sq hb])

/-- Actual scalar profile and row bounds amplify to all Hilbert fibers. -/
theorem partialProfileOperator_activity_le (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (rate bound₂ boundSup : ℝ) (hrate : 0 ≤ rate)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (hb₂ : 0 ≤ bound₂) (hbSup : 0 ≤ boundSup)
    (hscalar₂ : ∀ profile, Real.sqrt (profileSquareNorm primary (operator profile)) ≤
      bound₂ * Real.sqrt (profileSquareNorm primary profile))
    (hscalarSup : ∀ profile, ‖fun color => operator profile color / primary color‖ ≤
      boundSup * Real.sqrt (profileSquareNorm primary profile)) :
    coordinateActivity rate primary remaining (partialProfileOperator operator primary kernel) ≤
      (bound₂ + rate * boundSup) * coordinateActivity rate primary remaining kernel := by
  have hi := mul_le_mul_of_nonneg_left
    (partialProfileOperator_integrated_le operator primary remaining kernel bound₂ hp hq hb₂ hscalar₂) hrate
  have hf := mul_le_mul_of_nonneg_left
    (partialProfileOperator_fixed_le operator primary remaining kernel boundSup hp hq hbSup hscalarSup) (sq_nonneg rate)
  have hn : 0 ≤ fixedFiberNorm remaining kernel := norm_nonneg _
  have hc : 0 ≤ bound₂ + rate * boundSup := by positivity
  unfold coordinateActivity
  nlinarith [mul_nonneg hc (mul_nonneg (sq_nonneg rate) hn)]

/-- The inverse bound uses the exact equation on every remaining fiber.
No finite-dimensional norm comparison is used in this amplification. -/
theorem partialProfileInverse_activity_le (operator : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (error : Module.End ℝ (ι → ℝ)) (hoperator : operator.toLinearMap = LinearMap.id + error)
    (primary : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (rate constant : ℝ) (hrate : 0 ≤ rate)
    (hp : ∀ color, 0 < primary color) (hq : ∀ rest, 0 ≤ remaining rest)
    (hsmall : constant < 1)
    (herror : ∀ input : ι → κ → ℝ,
      coordinateActivity rate primary remaining (partialProfileOperator error primary input) ≤
        constant * coordinateActivity rate primary remaining input) :
    coordinateActivity rate primary remaining (partialProfileOperator operator.symm.toLinearMap primary kernel) ≤
      coordinateActivity rate primary remaining kernel / (1 - constant) := by
  let inverseKernel := partialProfileOperator operator.symm.toLinearMap primary kernel
  have heq : inverseKernel = kernel + -(partialProfileOperator error primary inverseKernel) := by
    funext color rest
    have hin : (fun input => primary input * inverseKernel input rest) =
        operator.symm (fun input => primary input * kernel input rest) := by
      funext input
      simp only [inverseKernel, partialProfileOperator, LinearEquiv.coe_coe]
      exact mul_div_cancel₀ _ (ne_of_gt (hp input))
    have h := congrArg (fun map : Module.End ℝ (ι → ℝ) =>
      map (operator.symm (fun input => primary input * kernel input rest)) color) hoperator
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.add_apply,
      LinearMap.id_apply, Pi.add_apply] at h
    change operator.symm (fun input => primary input * kernel input rest) color / primary color =
      kernel color rest + -(error (fun input => primary input * inverseKernel input rest) color / primary color)
    rw [hin]
    apply (div_eq_iff (ne_of_gt (hp color))).mpr
    have hc := ne_of_gt (hp color)
    field_simp
    nlinarith
  have ht := coordinateActivity_add_le rate primary remaining kernel
    (-(partialProfileOperator error primary inverseKernel)) hrate (fun color => (hp color).le) hq
  rw [← heq, coordinateActivity_neg] at ht
  have he := herror inverseKernel
  apply (le_div_iff₀ (by linarith : 0 < 1 - constant)).mpr
  dsimp [inverseKernel] at ht he
  nlinarith

omit [Fintype ι] [Fintype κ] in
@[simp] theorem partialProfileOperator_id (primary : ι → ℝ) (kernel : ι → κ → ℝ)
    (hp : ∀ color, 0 < primary color) :
    partialProfileOperator LinearMap.id primary kernel = kernel := by
  funext color rest
  exact mul_div_cancel_left₀ _ (ne_of_gt (hp color))

omit [Fintype ι] [Fintype κ] in
theorem partialProfileOperator_add (first second : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (kernel : ι → κ → ℝ) :
    partialProfileOperator (first + second) primary kernel =
      partialProfileOperator first primary kernel + partialProfileOperator second primary kernel := by
  funext color rest
  simp [partialProfileOperator, add_div]

omit [Fintype ι] [Fintype κ] in
theorem partialProfileOperator_comp (first second : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (kernel : ι → κ → ℝ) (hp : ∀ color, 0 < primary color) :
    partialProfileOperator (first.comp second) primary kernel =
      partialProfileOperator first primary (partialProfileOperator second primary kernel) := by
  have hprofile (rest : κ) :
      (fun input => primary input * partialProfileOperator second primary kernel input rest) =
        second (fun input => primary input * kernel input rest) := by
    funext input
    exact mul_div_cancel₀ _ (ne_of_gt (hp input))
  funext color rest
  simp only [partialProfileOperator, LinearMap.comp_apply]
  exact congrArg (fun profile => first profile color / primary color) (hprofile rest).symm

omit [Fintype κ] in
/-- Scalar interval bounds retain the actual finite support and row formula. -/
theorem intervalTranslationOperator_scalarBounds (colors starts : ι → ℤ)
    (hinj : Function.Injective colors) (shift : ℤ) (width : ℕ)
    (shiftBound lower : ℝ) (primary : ι → ℝ)
    (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : (shift.natAbs : ℝ) ≤ shiftBound) (profile : ι → ℝ) :
    Real.sqrt (profileSquareNorm primary (intervalTranslationOperator colors starts shift width profile)) ≤
      Real.sqrt (2 * shiftBound / ((width : ℝ) ^ 2 * lower)) * Real.sqrt (profileSquareNorm primary profile) ∧
    ‖fun color => intervalTranslationOperator colors starts shift width profile color / primary color‖ ≤
      (1 / ((width : ℝ) * lower)) * Real.sqrt (profileSquareNorm primary profile) := by
  have hsb : 0 ≤ shiftBound := (Nat.cast_nonneg shift.natAbs).trans hshift
  constructor
  · have hraw := finitePalette_anchorProfile_bound colors starts hinj shift width primary profile lower
      hp hmass hlower hout
    have hcoef : 2 * (shift.natAbs : ℝ) / ((width : ℝ) ^ 2 * lower) ≤
        2 * shiftBound / ((width : ℝ) ^ 2 * lower) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hn := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
    exact (Real.sqrt_le_sqrt (hraw.trans (mul_le_mul_of_nonneg_right hcoef hn))).trans_eq
      (Real.sqrt_mul (by positivity) _)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro output
    rw [Real.norm_eq_abs]
    exact intervalAnchorDifference_density_row_bound starts shift (colors output) width primary profile
      (primary output) lower hp hmass hlower (hout output)

omit [Fintype κ] in
/-- Convex averaging preserves both scalar bounds, by weighted Cauchy--Schwarz. -/
theorem averagedProfileOperator_scalarBounds {τ : Type*} [Fintype τ]
    (operators : τ → Module.End ℝ (ι → ℝ)) (weights : τ → ℝ)
    (primary : ι → ℝ) (bound₂ boundSup : ℝ)
    (hp : ∀ color, 0 < primary color) (hw : ∀ source, 0 ≤ weights source)
    (hmass : ∑ source, weights source = 1) (hb₂ : 0 ≤ bound₂) (hbSup : 0 ≤ boundSup)
    (hbounds : ∀ source profile,
      Real.sqrt (profileSquareNorm primary (operators source profile)) ≤
        bound₂ * Real.sqrt (profileSquareNorm primary profile) ∧
      ‖fun color => operators source profile color / primary color‖ ≤
        boundSup * Real.sqrt (profileSquareNorm primary profile)) (profile : ι → ℝ) :
    Real.sqrt (profileSquareNorm primary ((∑ source, weights source • operators source) profile)) ≤
      bound₂ * Real.sqrt (profileSquareNorm primary profile) ∧
    ‖fun color => (∑ source, weights source • operators source) profile color / primary color‖ ≤
      boundSup * Real.sqrt (profileSquareNorm primary profile) := by
  have hinput := profileSquareNorm_nonneg primary profile (fun color => (hp color).le)
  have hlocal (source : τ) : profileSquareNorm primary (operators source profile) ≤
      bound₂ ^ 2 * profileSquareNorm primary profile := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hb₂ (Real.sqrt_nonneg _))).mpr
      (hbounds source profile).1
    rwa [mul_pow, Real.sq_sqrt hinput,
      Real.sq_sqrt (profileSquareNorm_nonneg primary _ (fun color => (hp color).le))] at hh
  have hjensen (color : ι) : (∑ source, weights source * operators source profile color) ^ 2 ≤
      ∑ source, weights source * (operators source profile color) ^ 2 := by
    have hh : (∑ source, weights source * operators source profile color) ^ 2 ≤
        (∑ source, weights source) * ∑ source, weights source * (operators source profile color) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro source _; exact hw source
      · intro source _; exact mul_nonneg (hw source) (sq_nonneg _)
      · intro source _; ring
    simpa only [hmass, one_mul] using hh
  constructor
  · have hnorm : profileSquareNorm primary ((∑ source, weights source • operators source) profile) ≤
        bound₂ ^ 2 * profileSquareNorm primary profile := by
      calc
        _ ≤ ∑ color, (∑ source, weights source * (operators source profile color) ^ 2) / primary color := by
          apply Finset.sum_le_sum
          intro color _
          simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul] using div_le_div_of_nonneg_right (hjensen color) (hp color).le
        _ = ∑ source, weights source * profileSquareNorm primary (operators source profile) := by
          simp only [Finset.sum_div, profileSquareNorm, Finset.mul_sum, mul_div_assoc]
          exact Finset.sum_comm
        _ ≤ ∑ source, weights source * (bound₂ ^ 2 * profileSquareNorm primary profile) :=
          Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hlocal source) (hw source)
        _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]
    exact (Real.sqrt_le_sqrt hnorm).trans_eq (by rw [Real.sqrt_mul (sq_nonneg bound₂), Real.sqrt_sq hb₂])
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro color
    rw [Real.norm_eq_abs]
    have heq : (∑ source, weights source • operators source) profile color / primary color =
        ∑ source, weights source * (operators source profile color / primary color) := by
      simp [Finset.sum_div, mul_div_assoc]
    rw [heq]
    calc
      _ ≤ ∑ source, |weights source * (operators source profile color / primary color)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ source, weights source * (boundSup * Real.sqrt (profileSquareNorm primary profile)) := by
        apply Finset.sum_le_sum
        intro source _
        rw [abs_mul, abs_of_nonneg (hw source)]
        have hh := norm_le_pi_norm (fun color => operators source profile color / primary color) color
        rw [Real.norm_eq_abs] at hh
        exact mul_le_mul_of_nonneg_left (hh.trans (hbounds source profile).2) (hw source)
      _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem averagedIntervalTranslationOperator_fiber_le {τ : Type*} [Fintype τ]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (rate shiftBound lower : ℝ) (primary : ι → ℝ)
    (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (hweights : ∀ source, 0 ≤ weights source) (hweightmass : ∑ source, weights source = 1)
    (hrate : 0 ≤ rate) (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hq : ∀ rest, 0 ≤ remaining rest) (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : ∀ source, ((shifts source).natAbs : ℝ) ≤ shiftBound) :
    coordinateActivity rate primary remaining
      (partialProfileOperator (averagedIntervalTranslationOperator colors starts shifts width weights) primary kernel) ≤
      intervalTranslationActivityConstant rate shiftBound width lower *
        coordinateActivity rate primary remaining kernel := by
  have hbounds := averagedProfileOperator_scalarBounds
    (fun source => intervalTranslationOperator colors (starts source) (shifts source) width)
    weights primary (Real.sqrt (2 * shiftBound / ((width : ℝ) ^ 2 * lower)))
    (1 / ((width : ℝ) * lower)) hp hweights hweightmass (Real.sqrt_nonneg _) (by positivity)
    (fun source profile => intervalTranslationOperator_scalarBounds colors (starts source) hinj
      (shifts source) width shiftBound lower primary hp hmass hlower hout (hshift source) profile)
  exact partialProfileOperator_activity_le _ primary remaining kernel rate _ _ hrate hp hq
    (Real.sqrt_nonneg _) (by positivity) (fun profile => (hbounds profile).1) (fun profile => (hbounds profile).2)

theorem finitePrimaryRankEquiv_fiber_le (rate activation majorant : ℝ)
    (primary signProfile sign : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (hrate : 0 ≤ rate) (hp : ∀ color, 0 < primary color) (hmass : ∑ color, primary color = 1)
    (hq : ∀ rest, 0 ≤ remaining rest) (hmajorant : 0 ≤ majorant) (hsign : ∀ color, |sign color| ≤ 1)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color)
    (hsmall : (∑ color, |signProfile color|) < activation) :
    coordinateActivity rate primary remaining
      (partialProfileOperator (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm.toLinearMap
        primary kernel) ≤
      rankInverseActivityConstant rate activation majorant signProfile sign *
        coordinateActivity rate primary remaining kernel := by
  let denominator := activation + signFunctional sign signProfile
  let correction : Module.End ℝ (ι → ℝ) := denominator⁻¹ • profileRankOne signProfile (profileSignMap sign)
  have hc (profile : ι → ℝ) : correction profile =
      (signFunctional sign profile / denominator) • signProfile := by
    simp [correction, profileRankOne, profileSignMap, div_eq_mul_inv, smul_smul, mul_comm]
  have hC : 0 ≤ majorant * (∑ color, |signProfile color|) / denominator ^ 2 := by
    exact div_nonneg (mul_nonneg hmajorant (Finset.sum_nonneg fun color _ => abs_nonneg _)) (sq_nonneg _)
  have hbound := partialProfileOperator_activity_le correction primary remaining kernel rate
    (Real.sqrt (majorant * (∑ color, |signProfile color|) / denominator ^ 2))
    (majorant / |denominator|) hrate hp hq (Real.sqrt_nonneg _) (by positivity)
    (fun profile => by
      rw [hc]
      exact (Real.sqrt_le_sqrt (rankCorrection_profileSquareNorm_le primary signProfile sign profile
        denominator majorant hp hmass hsign hmajorant hprofile)).trans_eq (Real.sqrt_mul hC _))
    (fun profile => by
      rw [hc]
      exact rankCorrection_densityNorm_le primary signProfile sign profile denominator majorant
        hp hmass hsign hmajorant hprofile)
  have heq : partialProfileOperator
      (finitePrimaryRankEquiv activation signProfile sign hsign hsmall).symm.toLinearMap primary kernel =
        kernel + -(partialProfileOperator correction primary kernel) := by
    funext color rest
    simp only [partialProfileOperator, LinearEquiv.coe_coe, finitePrimaryRankEquiv_inverse_apply,
      Pi.sub_apply, sub_div, Pi.add_apply, Pi.neg_apply]
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hn := ne_of_gt (hp color)
    dsimp [denominator]
    field_simp
    ring
  rw [heq]
  have ht := coordinateActivity_add_le rate primary remaining kernel
    (-(partialProfileOperator correction primary kernel)) hrate (fun color => (hp color).le) hq
  rw [coordinateActivity_neg] at ht
  unfold rankInverseActivityConstant
  dsimp [denominator] at hbound
  nlinarith only [ht, hbound]

/-- The constructed local primary inverse has the same explicit bound on
every mixed Hilbert fiber, including arbitrary remaining-coordinate laws. -/
theorem finiteIntervalPrimary_inverse_fiber_bound {τ : Type*} [Fintype τ]
    (colors : ι → ℤ) (starts : τ → ι → ℤ) (shifts : τ → ℤ)
    (width : ℕ) (weights : τ → ℝ) (hinj : Function.Injective colors)
    (rate shiftBound lower activation majorant : ℝ)
    (primary signProfile sign : ι → ℝ) (remaining : κ → ℝ) (kernel : ι → κ → ℝ)
    (hweights : ∀ source, 0 ≤ weights source) (hweightmass : ∑ source, weights source = 1)
    (hrate : 0 ≤ rate) (hp : ∀ input, 0 < primary input) (hmass : ∑ input, primary input = 1)
    (hq : ∀ rest, 0 ≤ remaining rest) (hlower : 0 < lower) (hout : ∀ output, lower ≤ primary output)
    (hshift : ∀ source, ((shifts source).natAbs : ℝ) ≤ shiftBound)
    (hmajorant : 0 ≤ majorant) (hsign : ∀ color, |sign color| ≤ 1)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color)
    (hsignsmall : (∑ color, |signProfile color|) < activation)
    (hsmall : rankInverseActivityConstant rate activation majorant signProfile sign *
      intervalTranslationActivityConstant rate shiftBound width lower < 1)
    (operator : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hoperator : operator.toLinearMap = primaryRankOperator activation signProfile (profileSignMap sign) +
      averagedIntervalTranslationOperator colors starts shifts width weights) :
    coordinateActivity rate primary remaining (partialProfileOperator operator.symm.toLinearMap primary kernel) ≤
      (rankInverseActivityConstant rate activation majorant signProfile sign /
        (1 - rankInverseActivityConstant rate activation majorant signProfile sign *
          intervalTranslationActivityConstant rate shiftBound width lower)) *
        coordinateActivity rate primary remaining kernel := by
  let rank := finitePrimaryRankEquiv activation signProfile sign hsign hsignsmall
  let error := averagedIntervalTranslationOperator colors starts shifts width weights
  let correction := rank.symm.toLinearMap.comp error
  let neumann := operator.trans rank.symm
  let rankBound := rankInverseActivityConstant rate activation majorant signProfile sign
  let errorBound := intervalTranslationActivityConstant rate shiftBound width lower
  have hrank (input : ι → κ → ℝ) : coordinateActivity rate primary remaining
      (partialProfileOperator rank.symm.toLinearMap primary input) ≤
        rankBound * coordinateActivity rate primary remaining input :=
    finitePrimaryRankEquiv_fiber_le rate activation majorant primary signProfile sign remaining input
      hrate hp hmass hq hmajorant hsign hprofile hsignsmall
  have herr (input : ι → κ → ℝ) : coordinateActivity rate primary remaining
      (partialProfileOperator error primary input) ≤
        errorBound * coordinateActivity rate primary remaining input :=
    averagedIntervalTranslationOperator_fiber_le colors starts shifts width weights hinj rate shiftBound
      lower primary remaining input hweights hweightmass hrate hp hmass hq hlower hout hshift
  have hrankNonneg : 0 ≤ rankBound := by
    dsimp [rankBound, rankInverseActivityConstant]
    positivity
  have hcontract (input : ι → κ → ℝ) : coordinateActivity rate primary remaining
      (partialProfileOperator correction primary input) ≤
        (rankBound * errorBound) * coordinateActivity rate primary remaining input := by
    rw [show correction = rank.symm.toLinearMap.comp error from rfl,
      partialProfileOperator_comp _ _ primary input hp]
    exact (hrank _).trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (herr input) hrankNonneg)
  have hneumann : neumann.toLinearMap = LinearMap.id + correction := by
    apply LinearMap.ext
    intro profile
    have heval := congrArg (fun map : Module.End ℝ (ι → ℝ) => map profile) hoperator
    change operator profile = rank profile + error profile at heval
    change rank.symm (operator profile) = profile + rank.symm (error profile)
    rw [heval, map_add, LinearEquiv.symm_apply_apply]
  have hbound := partialProfileInverse_activity_le neumann correction hneumann primary remaining
    (partialProfileOperator rank.symm.toLinearMap primary kernel) rate (rankBound * errorBound)
    hrate hp hq hsmall hcontract
  have hcomp : neumann.symm.toLinearMap.comp rank.symm.toLinearMap = operator.symm.toLinearMap := by
    ext profile
    simp [neumann]
  rw [← partialProfileOperator_comp _ _ primary kernel hp, hcomp] at hbound
  have hden : 0 < 1 - rankBound * errorBound := by dsimp [rankBound, errorBound]; linarith
  exact hbound.trans (by
    have hh := div_le_div_of_nonneg_right (hrank kernel) hden.le
    simpa only [div_mul_eq_mul_div] using hh)

end ProfileAmplification

end AFT

import AFT.ActiveEndpointDifference
import AFT.CanonicalPairDensity
import AFT.ReferencePrimaryDensity
import AFT.ActualCovarianceInput

/-! # All actual active-branch canonical covariance coefficients -/

namespace AFT.V7Calibration
open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

def activeCanonicalPairDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  SafePair.canonicalPair (actualReferenceMean cutoffScale parameter beta)
    (activeEndpointDifference cutoffScale parameter beta) first second /
      (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second)

def activePairActivityBound (parameter : ℕ) (rate : ℝ) : ℝ :=
  let F := Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)
  let X := 36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter
  rate*rate*(F+rate*X+rate*X+rate*rate*X)+2*rate*rate*(3+8*rate)*(F+rate*X)

def activeCanonicalPairInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  RepresentedPolynomial.primaryPairInput (activeCanonicalPairDensity cutoffScale parameter beta)

theorem activeCanonicalPairDensity_centered (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (primary : FiniteDist (Fin (Parameters.modulus parameter)))
    (hprimary : primary.weight = actualPrimary cutoffScale parameter beta)
    (hp : ∀ color, 0 < actualPrimary cutoffScale parameter beta color)
    (hmass : (∑ first, ∑ second, activeEndpointDifference cutoffScale parameter beta first second) = 0) :
    activeCanonicalPairDensity cutoffScale parameter beta =
      MixedKernel.centeredPairDensity primary
        (fun color => actualReferenceMean cutoffScale parameter beta color / actualPrimary cutoffScale parameter beta color)
        (activeEndpointDensity cutoffScale parameter beta) := by
  funext first second
  unfold activeCanonicalPairDensity SafePair.canonicalPair MixedKernel.centeredPairDensity
  rw [hmass]
  have hrow : MixedKernel.rowAverage primary (activeEndpointDensity cutoffScale parameter beta) first =
      (∑ y, activeEndpointDifference cutoffScale parameter beta first y) / actualPrimary cutoffScale parameter beta first := by
    simp only [MixedKernel.rowAverage, hprimary, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    unfold activeEndpointDensity
    field_simp [ne_of_gt (hp first), ne_of_gt (hp y)]
  have hcol : MixedKernel.columnAverage primary (activeEndpointDensity cutoffScale parameter beta) second =
      (∑ x, activeEndpointDifference cutoffScale parameter beta x second) / actualPrimary cutoffScale parameter beta second := by
    simp only [MixedKernel.columnAverage, hprimary, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    unfold activeEndpointDensity
    field_simp [ne_of_gt (hp x), ne_of_gt (hp second)]
  rw [hrow, hcol]
  unfold activeEndpointDensity
  ring

theorem actual_active_pair_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (activeCanonicalPairInput cutoffScale parameter (beta parameter)) ≤
      activePairActivityBound parameter (Real.sqrt primaryPool)⁻¹ := by
  filter_upwards [actual_active_endpoint_density_eventually cutoffScale hscale beta hbeta,
    actual_reference_primary_density_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hd hr hp primary body hprimary primaryPool bodyPool radius
  dsimp only at hd hr
  rw [activeCanonicalPairInput, RepresentedPolynomial.primaryPairInput_weight,
    activeCanonicalPairDensity_centered cutoffScale parameter (beta parameter) primary hprimary hp.1 hd.1]
  exact MixedKernel.centeredPair_activity_le primary _ _ (Real.sqrt primaryPool)⁻¹
    (Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter))
    (36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)
    (by positivity) (by positivity) (by positivity) hr.1
    (by rw [hprimary]; norm_num; exact hr.2.trans (by norm_num))
    (by rw [hprimary, Real.sq_sqrt (by positivity)]; exact hd.2.2.1) hd.2.1

def actualActiveTripleKernel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    (Fin 3 → Fin (Parameters.modulus parameter)) → ℝ :=
  MixedKernel.tripleProductKernel (activeCanonicalPairDensity cutoffScale parameter beta)
    (inactiveAttachedBodyDensity cutoffScale parameter beta queue 0)

def actualActiveTripleInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  RepresentedPolynomial.primaryTripleInput (actualActiveTripleKernel cutoffScale parameter beta queue)

def activeEndpointMarginalDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (side : Bool)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  (∑ other, if side then activeEndpointDifference cutoffScale parameter beta color other
    else activeEndpointDifference cutoffScale parameter beta other color) /
      actualPrimary cutoffScale parameter beta color

def actualActiveMarginalBodyKernel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) (side : Bool)
    (color attached : Fin (Parameters.modulus parameter)) : ℝ :=
  activeEndpointMarginalDensity cutoffScale parameter beta side color *
    inactiveAttachedBodyDensity cutoffScale parameter beta queue 0 attached

def actualActiveMarginalBodyInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ) (side : Bool) :
    RepresentedPolynomial.InputSeed (Fin (Parameters.modulus parameter)) :=
  RepresentedPolynomial.primaryPairInput (actualActiveMarginalBodyKernel cutoffScale parameter beta queue side)

theorem activeEndpointMarginalDensity_average (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (primary : FiniteDist (Fin (Parameters.modulus parameter)))
    (hprimary : primary.weight = actualPrimary cutoffScale parameter beta)
    (hp : ∀ color, 0 < actualPrimary cutoffScale parameter beta color) (side : Bool) :
    activeEndpointMarginalDensity cutoffScale parameter beta side =
      if side then MixedKernel.rowAverage primary (activeEndpointDensity cutoffScale parameter beta)
      else MixedKernel.columnAverage primary (activeEndpointDensity cutoffScale parameter beta) := by
  funext color
  cases side <;> simp only [Bool.false_eq_true, if_false, if_true, activeEndpointMarginalDensity,
    MixedKernel.rowAverage, MixedKernel.columnAverage, hprimary, Finset.sum_div]
  all_goals
    apply Finset.sum_congr rfl
    intro other _
    unfold activeEndpointDensity
    field_simp [ne_of_gt (hp color), ne_of_gt (hp other)]

/-- The marked branch keeps the exact centered zero-source body profile;
its complete cubic activity is controlled before multiplying by rho(1-rho). -/
theorem actual_active_triple_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (actualActiveTripleInput cutoffScale parameter (beta parameter) queue) ≤
      activePairActivityBound parameter (Real.sqrt primaryPool)⁻¹ *
        inactiveBodyActivityBound cutoffScale parameter (Real.sqrt primaryPool)⁻¹ := by
  filter_upwards [actual_active_pair_activity_eventually cutoffScale hscale beta hbeta,
    actual_inactive_body_difference_eventually cutoffScale hscale beta hbeta]
    with parameter hpair hbody queue primary body hp primaryPool bodyPool radius
  let a := (Real.sqrt primaryPool)⁻¹
  have ha : 0 ≤ a := by positivity
  letI : Nonempty (Fin (Parameters.modulus parameter)) := ⟨⟨0, (Parameters.modulus_prime parameter).pos⟩⟩
  have hP := hpair primary body hp primaryPool bodyPool radius
  rw [activeCanonicalPairInput, RepresentedPolynomial.primaryPairInput_weight] at hP
  have hzero := hbody queue (windowZero (legCutoff cutoffScale parameter - 1))
  have hB := MixedKernel.singleton_activity_le primary
    (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue 0) a
    (Real.sqrt (384*(legCutoff cutoffScale parameter : ℝ)/Parameters.modulus parameter)) 16
    ha (Real.sqrt_nonneg _) (by norm_num)
    (by rw [hp, Real.sq_sqrt (by positivity)]; exact hzero.2) hzero.1
  have hB' : MixedKernel.activity (fun _ : Fin 1 => a) (fun _ => primary)
      (MixedKernel.singletonKernel (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue 0)) ≤
      inactiveBodyActivityBound cutoffScale parameter a := hB.trans_eq (by unfold inactiveBodyActivityBound; ring)
  rw [actualActiveTripleInput, RepresentedPolynomial.primaryTripleInput_weight]
  apply (MixedKernel.tripleProduct_activity_le primary _ _ a ha).trans
  exact mul_le_mul hP hB' (MixedKernel.activity_nonneg _ _ _ (fun _ => ha))
    (by unfold activePairActivityBound; positivity)

theorem actual_active_marginal_body_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ queue : ℤ, ∀ side : Bool,
      ∀ primary body : FiniteDist (Fin (Parameters.modulus parameter)),
      primary.weight = actualPrimary cutoffScale parameter (beta parameter) →
      ∀ primaryPool bodyPool radius : ℝ,
      RepresentedPolynomial.inputWeight primary body primaryPool bodyPool radius
        (actualActiveMarginalBodyInput cutoffScale parameter (beta parameter) queue side) ≤
      let a := (Real.sqrt primaryPool)⁻¹
      let F := Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)
      let X := 36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter
      a*(F+a*X)*inactiveBodyActivityBound cutoffScale parameter a := by
  filter_upwards [actual_active_endpoint_density_eventually cutoffScale hscale beta hbeta,
    actual_inactive_body_difference_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta]
    with parameter hd hbody hpositive queue side primary body hp primaryPool bodyPool radius
  dsimp only at hd ⊢
  let a := (Real.sqrt primaryPool)⁻¹
  let F := Real.sqrt (72*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter)
  let X := 36*(Parameters.modulus parameter : ℝ)/Parameters.anchorWidth parameter
  let H := Real.sqrt (384*(legCutoff cutoffScale parameter : ℝ)/Parameters.modulus parameter)
  have ha : 0 ≤ a := by positivity
  have hfull : (∑ x, ∑ y, primary.weight x*primary.weight y*
      activeEndpointDensity cutoffScale parameter (beta parameter) x y^2) ≤ F^2 := by
    rw [hp, Real.sq_sqrt (by positivity)]
    exact hd.2.2.1
  have hm : (∑ color, primary.weight color * activeEndpointMarginalDensity cutoffScale parameter (beta parameter) side color^2) ≤ F^2 ∧
      ∀ color, |activeEndpointMarginalDensity cutoffScale parameter (beta parameter) side color| ≤ X := by
    rw [activeEndpointMarginalDensity_average cutoffScale parameter (beta parameter) primary hp hpositive.1 side]
    cases side
    · exact MixedKernel.columnAverage_bounds primary _ F X hfull hd.2.1
    · exact MixedKernel.rowAverage_bounds primary _ F X hfull hd.2.1
  have hzero := hbody queue (windowZero (legCutoff cutoffScale parameter - 1))
  rw [actualActiveMarginalBodyInput, RepresentedPolynomial.primaryPairInput_weight]
  have hh := MixedKernel.pair_product_activity_le primary primary
    (activeEndpointMarginalDensity cutoffScale parameter (beta parameter) side)
    (inactiveAttachedBodyDensity cutoffScale parameter (beta parameter) queue 0)
    a a F X H 16 ha ha (by positivity) (by positivity) (by positivity) (by norm_num)
    hm.1 hm.2 (by rw [hp]; dsimp only [H]; rw [Real.sq_sqrt (by positivity)]; exact hzero.2) hzero.1
  exact hh.trans_eq (by dsimp only [a,F,X,H,inactiveBodyActivityBound]; ring)

/-- Exact decomposition of the entire active covariance. It has two
distinct endpoint/body quadratic terms, since the marked pair is ordered. -/
theorem actual_active_residual_input_identity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (hmass : (∑ first, ∑ second, activeEndpointDifference cutoffScale parameter beta first second) = 0)
    (first second attached : Fin (Parameters.modulus parameter)) :
    activeEndpointDifference cutoffScale parameter beta first second *
        inactiveAttachedBodyDifference cutoffScale parameter beta queue 0 attached /
      (actualPrimary cutoffScale parameter beta first * actualPrimary cutoffScale parameter beta second *
        actualPrimary cutoffScale parameter beta attached) =
      actualActiveTripleKernel cutoffScale parameter beta queue ![first,second,attached] +
        (actualReferenceMean cutoffScale parameter beta first / actualPrimary cutoffScale parameter beta first) *
          actualActiveMarginalBodyKernel cutoffScale parameter beta queue false second attached +
        actualActiveMarginalBodyKernel cutoffScale parameter beta queue true first attached *
          (actualReferenceMean cutoffScale parameter beta second / actualPrimary cutoffScale parameter beta second) := by
  have ht : Matrix.vecHead (Matrix.vecTail ![second, attached]) = attached := rfl
  simp only [actualActiveTripleKernel, MixedKernel.tripleProductKernel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, ht, actualActiveMarginalBodyKernel,
    activeEndpointMarginalDensity, Bool.false_eq_true, if_false, if_true,
    activeCanonicalPairDensity, SafePair.canonicalPair, hmass, zero_mul, add_zero,
    inactiveAttachedBodyDensity]
  ring

end
end AFT.V7Calibration

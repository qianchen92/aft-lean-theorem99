import CurrentAFT.CycleMatching
import AFT.HilbertConcentration
import AFT.ProfileHilbert

/-!
# Dimension-free square-exponential moments of the real dependent cycle

The cyclic sum is decomposed into three matchings. Independence is proved
for the complete latent pairs within each matching; the three matching
sums need not be independent. Convexity of the exponential combines them.
-/

namespace CurrentAFT.CycleMeanMGF

open AFT FiniteConcentration CurrentAFT.CycleMatching
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

omit [InnerProductSpace ℝ Hilbert] in
/-- Cauchy--Schwarz for three arbitrary, possibly dependent, vector sums. -/
theorem norm_three_sum_sq_le (value : Fin 3 → Hilbert) :
    ‖∑ index, value index‖ ^ 2 ≤ 3 * ∑ index, ‖value index‖ ^ 2 := by
  have hnorm := norm_sum_le Finset.univ value
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun _ => (1 : ℝ)) (fun index => ‖value index‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

omit [InnerProductSpace ℝ Hilbert] in
/-- No independence between the three vector sums is required here. -/
theorem exp_norm_three_sum_le (value : Fin 3 → Hilbert) (parameter : ℝ) (hparameter : 0 ≤ parameter) :
    Real.exp (parameter * ‖∑ index, value index‖ ^ 2) ≤
      (1 / 3 : ℝ) * ∑ index, Real.exp ((9 * parameter) * ‖value index‖ ^ 2) := by
  have hconvex := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset (Fin 3))) (w := fun _ => (1 / 3 : ℝ))
    (p := fun index => (9 * parameter) * ‖value index‖ ^ 2)
    (by intro _ _; norm_num) (by norm_num) (by intro _ _; exact Set.mem_univ _)
  simp only [smul_eq_mul] at hconvex
  have hequal : (∑ index : Fin 3, (1 / 3 : ℝ) * ((9 * parameter) * ‖value index‖ ^ 2)) =
      3 * parameter * ∑ index : Fin 3, ‖value index‖ ^ 2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [hequal, ← Finset.mul_sum] at hconvex
  apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_three_sum_sq_le value) hparameter)).trans
  convert hconvex using 1
  congr 1
  ring

/-- The genuine iid finite Hilbert sum estimate, reindexed to an arbitrary
finite matching vertex set with a constant coordinate bound. -/
theorem finite_hilbert_sum_square_mgf {Selected Sample : Type*} [Fintype Selected] [Fintype Sample]
    (law : FiniteDist Sample) (value : Selected → Sample → Hilbert)
    (bound parameter : ℝ) (hbound : 0 ≤ bound) (hparameter : 0 ≤ parameter)
    (hcenter : ∀ selected, vectorMean law (value selected) = 0)
    (hvalue : ∀ selected sample, ‖value selected sample‖ ≤ bound)
    (hsmall : 16 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2) < 1) :
    (FiniteDist.independent (fun _ : Selected => law)).expectation
      (fun word => Real.exp (parameter * ‖∑ selected, value selected (word selected)‖ ^ 2)) ≤
      Real.exp (2 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2)) *
        (Real.sqrt (1 - 16 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2)))⁻¹ := by
  let names : Selected ≃ Fin (Fintype.card Selected) := Fintype.equivFin Selected
  have h := hilbert_sum_square_mgf (Fintype.card Selected)
    (fun _ => law) (fun index => value (names.symm index)) (fun _ => bound)
    (fun index => hcenter _) (fun _ => hbound) (fun index sample => hvalue _ sample)
    parameter hparameter (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsmall)
  have hreindex := CanonicalMoments.independent_equiv_expectation_general names.symm
    (fun _ : Selected => law)
    (fun word : Fin (Fintype.card Selected) → Sample =>
      Real.exp (parameter * ‖∑ index, value (names.symm index) (word index)‖ ^ 2))
  have hfunction (word : Selected → Sample) :
      Real.exp (parameter * ‖∑ index : Fin (Fintype.card Selected), value (names.symm index) ((word ∘ names.symm) index)‖ ^ 2) =
        Real.exp (parameter * ‖∑ selected, value selected (word selected)‖ ^ 2) := by
    simp only [Function.comp_apply]
    rw [names.symm.sum_comp (fun selected => value selected (word selected))]
  simp_rw [hfunction] at hreindex
  have hleft : (FiniteDist.independent (fun _ : Selected => law)).expectation
      (fun word => Real.exp (parameter * ‖∑ selected, value selected (word selected)‖ ^ 2)) =
      (FiniteDist.independent (fun _ : Fin (Fintype.card Selected) => law)).expectation
        (fun word => Real.exp (parameter * ‖∑ index, value (names.symm index) (word index)‖ ^ 2)) := by
    convert hreindex using 1
  rw [hleft]
  convert h using 1 <;> simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- Enlarging the scalar variance budget only enlarges the proved finite
Hilbert square-exponential bound. -/
theorem finite_hilbert_sum_square_mgf_budget {Selected Sample : Type*} [Fintype Selected] [Fintype Sample]
    (law : FiniteDist Sample) (value : Selected → Sample → Hilbert)
    (bound parameter budget : ℝ) (hbound : 0 ≤ bound) (hparameter : 0 ≤ parameter)
    (hcenter : ∀ selected, vectorMean law (value selected) = 0)
    (hvalue : ∀ selected sample, ‖value selected sample‖ ≤ bound)
    (hbudget : (Fintype.card Selected : ℝ) * bound ^ 2 ≤ budget)
    (hsmall : 16 * parameter * budget < 1) :
    (FiniteDist.independent (fun _ : Selected => law)).expectation
      (fun word => Real.exp (parameter * ‖∑ selected, value selected (word selected)‖ ^ 2)) ≤
      Real.exp (2 * parameter * budget) * (Real.sqrt (1 - 16 * parameter * budget))⁻¹ := by
  have hsmallActual : 16 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbudget (by positivity)) hsmall
  apply (finite_hilbert_sum_square_mgf law value bound parameter hbound hparameter hcenter hvalue hsmallActual).trans
  have hexp : Real.exp (2 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2)) ≤
      Real.exp (2 * parameter * budget) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (by positivity))
  have hdenominator : Real.sqrt (1 - 16 * parameter * budget) ≤
      Real.sqrt (1 - 16 * parameter * ((Fintype.card Selected : ℝ) * bound ^ 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 16 * parameter)]
  have hinv := inv_anti₀ (Real.sqrt_pos.mpr (by linarith : 0 < 1 - 16 * parameter * budget)) hdenominator
  exact mul_le_mul hexp hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _)

/-- Actual matching sum, with its complete latent-pair product law and a
population budget at most the full body size. -/
theorem matching_sum_square_mgf {Scalar : Type*} [Fintype Scalar]
    (body : ℕ) (hbody : 2 ≤ body) (source : FiniteDist Scalar)
    (selected : Finset (Fin body)) (hmatching : IsMatching selected)
    (value : selected → Scalar × Scalar → Hilbert) (bound parameter : ℝ)
    (hbound : 0 ≤ bound) (hparameter : 0 ≤ parameter)
    (hcenter : ∀ vertex, vectorMean (source.prod source) (value vertex) = 0)
    (hvalue : ∀ vertex pair, ‖value vertex pair‖ ≤ bound)
    (hsmall : 16 * parameter * ((body : ℝ) * bound ^ 2) < 1) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation
      (fun latent => Real.exp (parameter * ‖∑ vertex : selected,
        value vertex (latent ((finRotate body).symm vertex.val), latent vertex.val)‖ ^ 2)) ≤
      Real.exp (2 * parameter * ((body : ℝ) * bound ^ 2)) *
        (Real.sqrt (1 - 16 * parameter * ((body : ℝ) * bound ^ 2)))⁻¹ := by
  rw [matching_expectation body hbody source selected hmatching
    (fun word => Real.exp (parameter * ‖∑ vertex, value vertex (word vertex)‖ ^ 2))]
  have hbudget : (Fintype.card selected : ℝ) * bound ^ 2 ≤ (body : ℝ) * bound ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg bound)
    exact_mod_cast (show Fintype.card selected ≤ body by simpa only [Fintype.card_coe, Fintype.card_fin] using Finset.card_le_univ selected)
  have h := finite_hilbert_sum_square_mgf_budget (source.prod source) value bound parameter
    ((body : ℝ) * bound ^ 2) hbound hparameter hcenter hvalue hbudget hsmall
  convert h using 1
  unfold FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- The complete cyclic sum has a dimension-free square-exponential
moment. Its actual root pairs overlap on the closing cycle; only the
three matching restrictions use independent scalar pairs. -/
theorem cycle_sum_square_mgf {Scalar : Type*} [Fintype Scalar]
    (body : ℕ) (hbody : 2 ≤ body) (source : FiniteDist Scalar)
    (value : Fin body → Scalar × Scalar → Hilbert) (bound parameter : ℝ)
    (hbound : 0 ≤ bound) (hparameter : 0 ≤ parameter)
    (hcenter : ∀ vertex, vectorMean (source.prod source) (value vertex) = 0)
    (hvalue : ∀ vertex pair, ‖value vertex pair‖ ≤ bound)
    (hsmall : 144 * parameter * ((body : ℝ) * bound ^ 2) < 1) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation
      (fun latent => Real.exp (parameter * ‖∑ vertex : Fin body,
        value vertex (latent ((finRotate body).symm vertex), latent vertex)‖ ^ 2)) ≤
      Real.exp (18 * parameter * ((body : ℝ) * bound ^ 2)) *
        (Real.sqrt (1 - 144 * parameter * ((body : ℝ) * bound ^ 2)))⁻¹ := by
  let product := FiniteDist.independent (fun _ : Fin body => source)
  let groupValue := fun (color : Fin 3) (latent : Fin body → Scalar) =>
    ∑ vertex : colorClass body color,
      value vertex.val (latent ((finRotate body).symm vertex.val), latent vertex.val)
  let estimate : ℝ := Real.exp (18 * parameter * ((body : ℝ) * bound ^ 2)) *
    (Real.sqrt (1 - 144 * parameter * ((body : ℝ) * bound ^ 2)))⁻¹
  have hgroup (color : Fin 3) : product.expectation
      (fun latent => Real.exp ((9 * parameter) * ‖groupValue color latent‖ ^ 2)) ≤ estimate := by
    have h := matching_sum_square_mgf body hbody source (colorClass body color)
      (colorClass_matching body hbody color) (fun vertex => value vertex.val) bound (9 * parameter)
      hbound (by positivity) (fun vertex => hcenter _) (fun vertex pair => hvalue _ pair)
      (by nlinarith [hsmall])
    have hfirst : 2 * (9 * parameter) * ((body : ℝ) * bound ^ 2) =
        18 * parameter * ((body : ℝ) * bound ^ 2) := by ring
    have hsecond : 16 * (9 * parameter) * ((body : ℝ) * bound ^ 2) =
        144 * parameter * ((body : ℝ) * bound ^ 2) := by ring
    simpa only [hfirst, hsecond] using h
  have hpoint (latent : Fin body → Scalar) :
      Real.exp (parameter * ‖∑ vertex : Fin body,
        value vertex (latent ((finRotate body).symm vertex), latent vertex)‖ ^ 2) ≤
        (1 / 3 : ℝ) * ∑ color : Fin 3, Real.exp ((9 * parameter) * ‖groupValue color latent‖ ^ 2) := by
    have h := exp_norm_three_sum_le (fun color => groupValue color latent) parameter hparameter
    have hsum : (∑ color : Fin 3, groupValue color latent) =
        ∑ vertex : Fin body, value vertex (latent ((finRotate body).symm vertex), latent vertex) := by
      dsimp only [groupValue]
      exact sum_colorClasses body (fun vertex => value vertex (latent ((finRotate body).symm vertex), latent vertex))
    rwa [hsum] at h
  have haverage := Finset.sum_le_sum (fun latent (_ : latent ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint latent) (product.nonneg latent))
  change product.expectation _ ≤ _ at haverage
  apply haverage.trans
  calc
    _ = (1 / 3 : ℝ) * ∑ color : Fin 3,
        product.expectation (fun latent => Real.exp ((9 * parameter) * ‖groupValue color latent‖ ^ 2)) := by
      unfold FiniteDist.expectation
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro color _
      apply Finset.sum_congr rfl
      intro latent _
      ring
    _ ≤ (1 / 3 : ℝ) * ∑ _color : Fin 3, estimate :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun color _ => hgroup color) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp only [estimate]; ring

/-- A larger declared cyclic variance budget is allowed, with its
smallness checked numerically rather than supplied as a moment bound. -/
theorem cycle_sum_square_mgf_budget {Scalar : Type*} [Fintype Scalar]
    (body : ℕ) (hbody : 2 ≤ body) (source : FiniteDist Scalar)
    (value : Fin body → Scalar × Scalar → Hilbert) (bound parameter budget : ℝ)
    (hbound : 0 ≤ bound) (hparameter : 0 ≤ parameter)
    (hcenter : ∀ vertex, vectorMean (source.prod source) (value vertex) = 0)
    (hvalue : ∀ vertex pair, ‖value vertex pair‖ ≤ bound)
    (hbudget : (body : ℝ) * bound ^ 2 ≤ budget)
    (hsmall : 144 * parameter * budget < 1) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation
      (fun latent => Real.exp (parameter * ‖∑ vertex : Fin body,
        value vertex (latent ((finRotate body).symm vertex), latent vertex)‖ ^ 2)) ≤
      Real.exp (18 * parameter * budget) * (Real.sqrt (1 - 144 * parameter * budget))⁻¹ := by
  have hactualSmall : 144 * parameter * ((body : ℝ) * bound ^ 2) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbudget (by positivity)) hsmall
  apply (cycle_sum_square_mgf body hbody source value bound parameter hbound hparameter hcenter hvalue hactualSmall).trans
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget
    (by positivity : 0 ≤ 18 * parameter))
  have hdenominator : Real.sqrt (1 - 144 * parameter * budget) ≤
      Real.sqrt (1 - 144 * parameter * ((body : ℝ) * bound ^ 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 144 * parameter)]
  have hinv := inv_anti₀ (Real.sqrt_pos.mpr (by linarith : 0 < 1 - 144 * parameter * budget)) hdenominator
  exact mul_le_mul hexp hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _)

/-- Actual normalized cycle fluctuations of bounded local profile vectors.
The centering is their true pair-law mean, and no joint-root law is
replaced by a product. This applies directly to protected Gaussian edges. -/
theorem normalized_centered_cycle_square_mgf {Scalar : Type*} [Fintype Scalar]
    (body population : ℕ) (hbody : 2 ≤ body) (hpopulation : body ≤ population)
    (source : FiniteDist Scalar) (response : Fin body → Scalar × Scalar → Hilbert)
    (deviation parameter : ℝ) (hdeviation : 0 ≤ deviation) (hparameter : 0 ≤ parameter)
    (hresponse : ∀ vertex pair, ‖response vertex pair‖ ≤ deviation)
    (hsmall : 576 * parameter * deviation ^ 2 < 1) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation
      (fun latent => Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
        (∑ vertex : Fin body,
          (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
            vectorMean (source.prod source) (response vertex)))‖ ^ 2)) ≤
      Real.exp (72 * parameter * deviation ^ 2) *
        (Real.sqrt (1 - 576 * parameter * deviation ^ 2))⁻¹ := by
  have hpop : (0 : ℝ) < population := by exact_mod_cast (by omega : 0 < population)
  let value := fun (vertex : Fin body) (pair : Scalar × Scalar) =>
    (Real.sqrt (population : ℝ))⁻¹ • (response vertex pair - vectorMean (source.prod source) (response vertex))
  let bound := 2 * deviation / Real.sqrt (population : ℝ)
  have hbound : 0 ≤ bound := by dsimp only [bound]; positivity
  have hcenter (vertex : Fin body) : vectorMean (source.prod source) (value vertex) = 0 := by
    have h := vectorMean_centered (source.prod source) (response vertex)
    calc
      _ = (Real.sqrt (population : ℝ))⁻¹ • vectorMean (source.prod source)
          (fun pair => response vertex pair - vectorMean (source.prod source) (response vertex)) := by
        simp only [value, vectorMean, Finset.smul_sum, smul_smul, mul_comm]
      _ = 0 := by rw [h, smul_zero]
  have hvalue (vertex : Fin body) (pair : Scalar × Scalar) : ‖value vertex pair‖ ≤ bound := by
    dsimp only [value, bound]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have h := mul_le_mul_of_nonneg_left
      (centered_value_norm_le (source.prod source) (response vertex) deviation (hresponse vertex) pair)
      (inv_nonneg.mpr (Real.sqrt_nonneg (population : ℝ)))
    exact h.trans_eq (by ring)
  have hbudget : (body : ℝ) * bound ^ 2 ≤ 4 * deviation ^ 2 := by
    have hratio : (body : ℝ) / population ≤ 1 := (div_le_one hpop).mpr (by exact_mod_cast hpopulation)
    calc
      _ = 4 * deviation ^ 2 * ((body : ℝ) / population) := by
        dsimp only [bound]
        rw [div_pow, Real.sq_sqrt hpop.le]
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * deviation ^ 2)]
  have h := cycle_sum_square_mgf_budget body hbody source value bound parameter (4 * deviation ^ 2)
    hbound hparameter hcenter hvalue hbudget (by nlinarith [hsmall])
  have hsum (latent : Fin body → Scalar) :
      (∑ vertex : Fin body, value vertex (latent ((finRotate body).symm vertex), latent vertex)) =
        (Real.sqrt (population : ℝ))⁻¹ • (∑ vertex : Fin body,
          (response vertex (latent ((finRotate body).symm vertex), latent vertex) - vectorMean (source.prod source) (response vertex))) := by
    dsimp only [value]
    rw [Finset.smul_sum]
  simp_rw [hsum] at h
  have hfirst : 18 * parameter * (4 * deviation ^ 2) = 72 * parameter * deviation ^ 2 := by ring
  have hsecond : 144 * parameter * (4 * deviation ^ 2) = 576 * parameter * deviation ^ 2 := by ring
  simpa only [hfirst, hsecond] using h

/- Packing the finite product expectation also keeps its dependent `Fintype`
instance fixed when the body is a large public parameter expression. -/
def normalizedCycleMoment {Scalar : Type*} [Fintype Scalar]
    (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (parameter : ℝ) : ℝ :=
  (FiniteDist.independent (fun _ : Fin body => source)).expectation
    (fun latent => Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
      (∑ vertex : Fin body,
        (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
          vectorMean (source.prod source) (response vertex)))‖ ^ 2))

theorem normalizedCycleMoment_nonneg {Scalar : Type*} [Fintype Scalar]
    (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (parameter : ℝ) :
    0 ≤ normalizedCycleMoment body population source response parameter :=
  Finset.sum_nonneg (fun latent _ =>
    mul_nonneg ((FiniteDist.independent (fun _ : Fin body => source)).nonneg latent) (Real.exp_nonneg _))

theorem normalizedCycleMoment_le {Scalar : Type*} [Fintype Scalar]
    (body population : ℕ) (hbody : 2 ≤ body) (hpopulation : body ≤ population)
    (source : FiniteDist Scalar) (response : Fin body → Scalar × Scalar → Hilbert)
    (deviation parameter : ℝ) (hdeviation : 0 ≤ deviation) (hparameter : 0 ≤ parameter)
    (hresponse : ∀ vertex pair, ‖response vertex pair‖ ≤ deviation)
    (hsmall : 576 * parameter * deviation ^ 2 < 1) :
    normalizedCycleMoment body population source response parameter ≤
      Real.exp (72 * parameter * deviation ^ 2) *
        (Real.sqrt (1 - 576 * parameter * deviation ^ 2))⁻¹ :=
  normalized_centered_cycle_square_mgf body population hbody hpopulation source response
    deviation parameter hdeviation hparameter hresponse hsmall

end

end CurrentAFT.CycleMeanMGF

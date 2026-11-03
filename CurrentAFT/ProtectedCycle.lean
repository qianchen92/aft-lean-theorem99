import AFT.Hoeffding
import AFT.ClippedSource
import AFT.GaussianReflection
import CurrentAFT.PublicCharge
import CurrentAFT.AmbientFourier

/-!
# The actual protected latent cycle and its Fourier response

Independent latent edge scalars are sampled first, and every root is their
cyclic difference, including the closing edge. The endpoint law is a
pushforward of this whole product experiment; its roots are not replaced by
independent samples of their one-coordinate marginal.

The identities below are exact finite-distribution identities. Quantitative
centered likelihood bounds for randomly selected paths and the complete
calibration response-norm estimate remain separate obligations.
-/

namespace CurrentAFT.ProtectedCycle

open AFT
open scoped BigOperators Classical

noncomputable section

/-- The entire cyclic difference law of independent finite latent scalars. -/
def cycleLaw {Scalar : Type*} [Fintype Scalar] (body modulus : ℕ) [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus) :
    FiniteDist (Fin body → ZMod modulus) :=
  (FiniteDist.independent (fun _ : Fin body => edgeLaw)).map
    (fun latent => PublicCharge.cycleDifference (fun vertex => value (latent vertex)))

/-- Concrete protected cycle using the current finite Gaussian interval. -/
def gaussianCycleLaw (body modulus cutoff : ℕ) [NeZero modulus] (width : ℝ) :
    FiniteDist (Fin body → ZMod modulus) :=
  cycleLaw body modulus (GaussianSource.windowGaussian width cutoff)
    (fun scalar => ((scalar : ℤ) : ZMod modulus))

/-- The finite law retains the closing edge and has total charge zero
pointwise, before any conditioning or final permutation. -/
theorem cycleLaw_charge {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (root : Fin body → ZMod modulus)
    (hnonzero : (cycleLaw body modulus edgeLaw value).weight root ≠ 0) :
    (∑ vertex, root vertex) = 0 := by
  by_contra hcharge
  apply hnonzero
  unfold cycleLaw
  simp only [FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro latent _
  have hne : PublicCharge.cycleDifference (fun vertex => value (latent vertex)) ≠ root := by
    intro hequal
    apply hcharge
    rw [← hequal]
    exact PublicCharge.sum_cycleDifference _
  simp [hne]

/-- Expectation of a complex test under a finite deterministic pushforward. -/
theorem complex_expectation_map {First Second : Type*} [Fintype First] [Fintype Second]
    (law : FiniteDist First) (output : First → Second) (test : Second → ℂ) :
    (∑ point, ((law.map output).weight point : ℂ) * test point) =
      ∑ seed, (law.weight seed : ℂ) * test (output seed) := by
  simp only [FiniteDist.map_weight, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  simp [ite_mul]

/-- Integrating a product test against the actual independent latent law. -/
theorem complex_independent_product {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar] (laws : Index → FiniteDist Scalar)
    (test : Index → Scalar → ℂ) :
    (∑ latent, ((FiniteDist.independent laws).weight latent : ℂ) *
      ∏ index, test index (latent index)) =
      ∏ index, ∑ scalar, ((laws index).weight scalar : ℂ) * test index scalar := by
  simp only [FiniteDist.independent, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index scalar => ((laws index).weight scalar : ℂ) * test index scalar)).symm

/-- One-coordinate positive-sign transform of the latent scalar law. -/
def scalarFourier {Scalar : Type*} [Fintype Scalar] {modulus : ℕ} [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (frequency : ZMod modulus) : ℂ :=
  ∑ scalar, (edgeLaw.weight scalar : ℂ) * AddChar.zmodAddEquiv frequency (value scalar)

@[simp] theorem scalarFourier_zero {Scalar : Type*} [Fintype Scalar]
    {modulus : ℕ} [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) : scalarFourier edgeLaw value 0 = 1 := by
  simp only [scalarFourier, map_zero, AddChar.zero_apply, mul_one,
    ← Complex.ofReal_sum, edgeLaw.sum_one, Complex.ofReal_one]

/-- The actual scalar transform is bounded by one because the latent law is
positive and normalized, rather than by an assumed Fourier estimate. -/
theorem norm_scalarFourier_le_one {Scalar : Type*} [Fintype Scalar]
    {modulus : ℕ} [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (frequency : ZMod modulus) :
    ‖scalarFourier edgeLaw value frequency‖ ≤ 1 := by
  unfold scalarFourier
  calc
    _ ≤ ∑ scalar, ‖(edgeLaw.weight scalar : ℂ) *
        AddChar.zmodAddEquiv frequency (value scalar)‖ := norm_sum_le _ _
    _ = ∑ scalar, edgeLaw.weight scalar := by
      apply Finset.sum_congr rfl
      intro scalar _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (edgeLaw.nonneg scalar), AddChar.norm_apply, mul_one]
    _ = 1 := edgeLaw.sum_one

/-- Scalar character in its explicit circle-valued implementation. -/
theorem scalar_character_circle {modulus : ℕ} [NeZero modulus]
    (frequency point : ZMod modulus) :
    AddChar.zmodAddEquiv frequency point =
      ((AddChar.zmod modulus frequency point : Circle) : ℂ) := rfl

theorem zmod_character_evaluation {modulus : ℕ} [NeZero modulus]
    (frequency point : ZMod modulus) :
    AddChar.zmod modulus frequency point =
      AddCircle.toCircle (ZMod.toAddCircle (frequency * point)) := rfl

/-- Bilinearity of the actual positive-sign scalar character. -/
theorem scalar_character_mul {modulus : ℕ} [NeZero modulus]
    (frequency point : ZMod modulus) :
    AddChar.zmodAddEquiv frequency point = AddChar.zmodAddEquiv (1 : ZMod modulus)
      (frequency * point) := by
  simp only [scalar_character_circle, zmod_character_evaluation, one_mul]

/-- A character sends a finite sum to the product of its values. -/
theorem character_sum {Index Group : Type*} [Fintype Index] [AddCommGroup Group]
    (character : AddChar Group ℂ) (point : Index → Group) :
    character (∑ index, point index) = ∏ index, character (point index) := by
  have hsum (indices : Finset Index) :
      character (∑ index ∈ indices, point index) = ∏ index ∈ indices, character (point index) := by
    induction indices using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    | @insert index indices hnot ih =>
      rw [Finset.sum_insert hnot, Finset.prod_insert hnot, AddChar.map_add_eq_mul, ih]
  exact hsum Finset.univ

/-- Dot-product form of the current coordinate character. -/
theorem coordinateCharacter_dot {Index : Type*} [Fintype Index]
    {modulus : ℕ} [NeZero modulus] (frequency point : Index → ZMod modulus) :
    coordinateCharacter frequency point = AddChar.zmodAddEquiv (1 : ZMod modulus)
      (∑ index, frequency index * point index) := by
  rw [coordinateCharacter_apply, character_sum]
  apply Finset.prod_congr rfl
  intro index _
  exact scalar_character_mul _ _

/-- Taking cyclic differences transfers the discrete derivative onto the
frequency, in the opposite direction. The closing edge is present in both. -/
theorem cycle_dot_adjoint {body modulus : ℕ} [NeZero modulus]
    (frequency latent : Fin body → ZMod modulus) :
    (∑ vertex, frequency vertex * PublicCharge.cycleDifference latent vertex) =
      ∑ vertex, (frequency vertex - frequency (finRotate body vertex)) * latent vertex := by
  have hreindex :
      (∑ vertex, frequency vertex * latent ((finRotate body).symm vertex)) =
      ∑ vertex, frequency (finRotate body vertex) * latent vertex := by
    rw [← Equiv.sum_comp (finRotate body)
      (fun vertex => frequency vertex * latent ((finRotate body).symm vertex))]
    simp only [Equiv.symm_apply_apply]
  simp only [PublicCharge.cycleDifference, mul_sub, sub_mul,
    Finset.sum_sub_distrib, hreindex]

/-- Exact pointwise pullback of the full joint character. -/
theorem cycle_character_adjoint {body modulus : ℕ} [NeZero modulus]
    (frequency latent : Fin body → ZMod modulus) :
    coordinateCharacter frequency (PublicCharge.cycleDifference latent) =
      coordinateCharacter
        (fun vertex => frequency vertex - frequency (finRotate body vertex)) latent := by
  rw [coordinateCharacter_dot, coordinateCharacter_dot, cycle_dot_adjoint]

/-- Exact complete Fourier transform of the dependent protected cycle.
Independence is used only for the latent edges after the adjoint derivative;
the roots themselves share latent variables and sum to zero. -/
theorem cycleLaw_fourier {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (frequency : Fin body → ZMod modulus) :
    signedFourier (cycleLaw body modulus edgeLaw value).weight (coordinateCharacter frequency) =
      ∏ vertex, scalarFourier edgeLaw value
        (frequency vertex - frequency (finRotate body vertex)) := by
  unfold signedFourier characterFourier cycleLaw
  rw [complex_expectation_map]
  simp_rw [cycle_character_adjoint, coordinateCharacter_apply]
  exact complex_independent_product (fun _ : Fin body => edgeLaw)
    (fun vertex scalar => AddChar.zmodAddEquiv
      (frequency vertex - frequency (finRotate body vertex)) (value scalar))

/-- Exact coordinate splitting using the same decidability and product
space instances as the latent law. -/
theorem independent_expectation_split {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (index : Index) (test : (Index → Scalar) → ℝ) :
    (FiniteDist.independent reference).expectation test =
      ∑ rest : {other : Index // other ≠ index} → Scalar,
        (∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other)) *
          ∑ value, (reference index).weight value *
            test ((Equiv.funSplitAt index Scalar).symm (value, rest)) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← (Equiv.funSplitAt index Scalar).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  have hproduct :
      (∏ other, (reference other).weight ((Equiv.funSplitAt index Scalar).symm (value, rest) other)) =
      (reference index).weight value *
        ∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ index]
    apply congrArg₂ (· * ·)
    · simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro other _
      simp [Equiv.funSplitAt, Equiv.piSplitAt, other.property]
  change (∏ other, (reference other).weight
    ((Equiv.funSplitAt index Scalar).symm (value, rest) other)) * _ = _
  rw [hproduct]
  ring

/-- A single latent coordinate has its prescribed independent marginal. -/
theorem independent_single_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (index : Index) (test : Scalar → ℝ) :
    (FiniteDist.independent reference).expectation (fun latent => test (latent index)) =
      (reference index).expectation test := by
  rw [independent_expectation_split reference index]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_true]
  rw [← Finset.sum_mul]
  have hmass := (FiniteDist.independent
    (fun rest : {other : Index // other ≠ index} => reference rest)).sum_one
  change (∑ rest : {other : Index // other ≠ index} → Scalar,
    ∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other)) = 1 at hmass
  rw [hmass, one_mul]
  rfl

/-- Any two different latent coordinates have their actual product law. -/
theorem independent_pair_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first)
    (test : Scalar → Scalar → ℝ) :
    (FiniteDist.independent reference).expectation
        (fun latent => test (latent first) (latent second)) =
      ∑ firstValue, ∑ secondValue, (reference first).weight firstValue *
        (reference second).weight secondValue * test firstValue secondValue := by
  rw [independent_expectation_split reference first]
  have heval (value : Scalar) (rest : {other : Index // other ≠ first} → Scalar) :
      test ((Equiv.funSplitAt first Scalar).symm (value, rest) first)
        ((Equiv.funSplitAt first Scalar).symm (value, rest) second) =
      test value (rest ⟨second, hdistinct⟩) := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hdistinct]
  simp_rw [heval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstValue _
  let restReference := fun other : {other : Index // other ≠ first} => reference other
  have hsingle := independent_single_expectation restReference ⟨second, hdistinct⟩
    (test firstValue)
  have hrewrite :
      (∑ rest : {other : Index // other ≠ first} → Scalar,
        (∏ other : {other : Index // other ≠ first}, (reference other).weight (rest other)) *
          ((reference first).weight firstValue * test firstValue (rest ⟨second, hdistinct⟩))) =
      (reference first).weight firstValue *
        (FiniteDist.independent restReference).expectation
          (fun rest => test firstValue (rest ⟨second, hdistinct⟩)) := by
    unfold FiniteDist.expectation FiniteDist.independent restReference
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rest _
    ring
  rw [hrewrite, hsingle, FiniteDist.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondValue _
  ring

/-- The entire two-coordinate marginal, rather than only product tests. -/
theorem independent_pair_law {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first) :
    (FiniteDist.independent reference).map (fun latent => (latent first, latent second)) =
      (reference first).prod (reference second) := by
  ext values
  have htest := independent_pair_expectation reference first second hdistinct
    (fun firstValue secondValue => if (firstValue, secondValue) = values then 1 else 0)
  have hleft : (FiniteDist.independent reference).expectation
      (fun latent => if (latent first, latent second) = values then 1 else 0) =
      ((FiniteDist.independent reference).map
        (fun latent => (latent first, latent second))).weight values := by
    simp only [FiniteDist.expectation, FiniteDist.map_weight, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro latent _
    by_cases hequal : (latent first, latent second) = values <;> simp [hequal]
  rw [hleft] at htest
  rw [htest]
  rcases values with ⟨firstValue, secondValue⟩
  simp [mul_ite, FiniteDist.prod_weight, ite_and]

/-- Actual one-root difference convolution. -/
def differenceLaw {Scalar : Type*} [Fintype Scalar] {modulus : ℕ} [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus) : FiniteDist (ZMod modulus) :=
  (edgeLaw.prod edgeLaw).map (fun pair => value pair.1 - value pair.2)

/-- Every nondegenerate cycle root has the independent two-edge difference
marginal. The theorem explicitly excludes a self-predecessor. -/
theorem cycleLaw_marginal {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (vertex : Fin body)
    (hdistinct : (finRotate body).symm vertex ≠ vertex) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value := by
  unfold cycleLaw differenceLaw
  rw [FiniteDist.map_map]
  have hpair := independent_pair_law (fun _ : Fin body => edgeLaw) vertex
    ((finRotate body).symm vertex) hdistinct
  rw [← hpair, FiniteDist.map_map]
  rfl

/-- In an actual cycle with at least two vertices, the predecessor is different. -/
theorem cycle_predecessor_ne (body : ℕ) (hbody : 2 ≤ body) (vertex : Fin body) :
    (finRotate body).symm vertex ≠ vertex := by
  intro hfixed
  have hnext : finRotate body vertex = vertex := by
    have h := congrArg (finRotate body) hfixed
    simpa only [Equiv.apply_symm_apply] using h.symm
  cases body with
  | zero => omega
  | succ length =>
    have hvalue := congrArg Fin.val hnext
    by_cases hlast : vertex = Fin.last length
    · subst vertex
      simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hvalue
      omega
    · rw [coe_finRotate, if_neg hlast] at hvalue
      omega

/-- The one-root convolution holds for every actual body population at least two. -/
theorem cycleLaw_marginal_of_two_le {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (hbody : 2 ≤ body) (vertex : Fin body) :
    (cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      differenceLaw edgeLaw value :=
  cycleLaw_marginal body modulus edgeLaw value vertex (cycle_predecessor_ne body hbody vertex)

/-- The actual protected integer differences satisfy the cutoff pointwise. -/
theorem protected_integer_difference_bound (body cutoff : ℕ)
    (latent : Fin body → GaussianSource.Window cutoff) (vertex : Fin body) :
    |PublicCharge.cycleDifference (fun index => (latent index : ℤ)) vertex| ≤ 2 * (cutoff : ℤ) := by
  have hfirst := Finset.mem_Icc.mp (latent vertex).property
  have hsecond := Finset.mem_Icc.mp (latent ((finRotate body).symm vertex)).property
  dsimp only [PublicCharge.cycleDifference]
  apply abs_le.mpr
  constructor <;> omega

/-- The reflected protected Gaussian is exactly the same finite law. -/
theorem gaussianEdgeLaw_reflected (width : ℝ) (cutoff : ℕ) :
    (GaussianSource.windowGaussian width cutoff).map (GaussianSource.windowNegateEquiv cutoff) =
      GaussianSource.windowGaussian width cutoff := by
  ext scalar
  rw [FiniteDist.map_equiv_weight]
  change (GaussianSource.windowGaussian width cutoff).weight
    (GaussianSource.windowNegateEquiv cutoff scalar) = _
  exact GaussianSource.windowGaussian_reflection width cutoff scalar

/-- Symmetry identifies the difference marginal with the convolution used
in the manuscript's definition of the protected root marginal. -/
theorem gaussian_difference_eq_sum (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    differenceLaw (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus)) =
      ((GaussianSource.windowGaussian width cutoff).prod
        (GaussianSource.windowGaussian width cutoff)).map
          (fun pair => (((pair.1 : ℤ) + (pair.2 : ℤ)) : ZMod modulus)) := by
  let edge := GaussianSource.windowGaussian width cutoff
  let reverse := (Equiv.refl (GaussianSource.Window cutoff)).prodCongr
    (GaussianSource.windowNegateEquiv cutoff)
  have hid : edge.map (Equiv.refl _) = edge := by
    ext scalar
    rw [FiniteDist.map_equiv_weight]
    rfl
  have hpair : (edge.prod edge).map reverse = edge.prod edge := by
    rw [FiniteDist.prod_map_equiv, hid, gaussianEdgeLaw_reflected]
  unfold differenceLaw
  change (edge.prod edge).map (fun pair =>
    ((pair.1 : ℤ) : ZMod modulus) - ((pair.2 : ℤ) : ZMod modulus)) = _
  conv_lhs => rw [← hpair, FiniteDist.map_map]
  congr 1
  funext pair
  simp [reverse, Equiv.prodCongr_apply, GaussianSource.windowNegateEquiv_val]

/-- Actual Gaussian cycle marginals use the same window law and convolution
as the current diffuse-profile construction. -/
theorem gaussianCycleLaw_marginal (body cutoff modulus : ℕ) [NeZero modulus]
    (width : ℝ) (hbody : 2 ≤ body) (vertex : Fin body) :
    (gaussianCycleLaw body modulus cutoff width).map (fun root => root vertex) =
      ((GaussianSource.windowGaussian width cutoff).prod
        (GaussianSource.windowGaussian width cutoff)).map
          (fun pair => (((pair.1 : ℤ) + (pair.2 : ℤ)) : ZMod modulus)) := by
  rw [gaussianCycleLaw, cycleLaw_marginal_of_two_le body modulus _ _ hbody vertex,
    gaussian_difference_eq_sum]

end

end CurrentAFT.ProtectedCycle

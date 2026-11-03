import AFT.MixedSymmetry
import AFT.QueueNormalization

/-!
# Finite polynomials in specified input seeds

Different seed labels remain different formal variables even when their
leading output tensors agree.  The activity is the coefficient L1 sum
weighted by the product of the actual seed activities.  This is an upper
bound for the fully expanded, symmetrized input representation by
`MixedTensor` and `MixedSymmetry`; no quotient by output tensors is used.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

abbrev Table (Seed : Type*) := MvPolynomial Seed ℝ

def monomialWeight (weight : Seed → ℝ) (powers : Seed →₀ ℕ) : ℝ :=
  powers.prod fun seed power => weight seed ^ power

def activity (weight : Seed → ℝ) (table : Table Seed) : ℝ :=
  table.sum fun powers coefficient => |coefficient| * monomialWeight weight powers

theorem monomialWeight_nonneg (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (powers : Seed →₀ ℕ) : 0 ≤ monomialWeight weight powers :=
  Finset.prod_nonneg fun seed _ => pow_nonneg (hweight seed) _

@[simp] theorem monomialWeight_zero (weight : Seed → ℝ) : monomialWeight weight 0 = 1 := by
  simp [monomialWeight]

theorem monomialWeight_add (weight : Seed → ℝ) (first second : Seed →₀ ℕ) :
    monomialWeight weight (first + second) = monomialWeight weight first * monomialWeight weight second :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem activity_nonneg (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed) (table : Table Seed) :
    0 ≤ activity weight table :=
  Finset.sum_nonneg fun powers _ => mul_nonneg (abs_nonneg _) (monomialWeight_nonneg weight hweight powers)

@[simp] theorem activity_zero (weight : Seed → ℝ) : activity weight (0 : Table Seed) = 0 := by
  simp [activity, MvPolynomial.sum_def]

@[simp] theorem activity_monomial (weight : Seed → ℝ) (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    activity weight (MvPolynomial.monomial powers coefficient) = |coefficient| * monomialWeight weight powers :=
  MvPolynomial.sum_monomial_eq (by simp)

@[simp] theorem activity_one (weight : Seed → ℝ) : activity weight (1 : Table Seed) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, activity_monomial, monomialWeight_zero]
  norm_num

theorem activity_add_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (first second : Table Seed) :
    activity weight (first + second) ≤ activity weight first + activity weight second := by
  let support := first.support ∪ second.support
  have hf := Finsupp.sum_of_support_subset first (s := first.support ∪ second.support) (Finset.subset_union_left)
    (fun powers coefficient => |coefficient| * monomialWeight weight powers) (by simp)
  have hs := Finsupp.sum_of_support_subset second (s := first.support ∪ second.support) (Finset.subset_union_right)
    (fun powers coefficient => |coefficient| * monomialWeight weight powers) (by simp)
  have ha := Finsupp.sum_of_support_subset (first + second) Finsupp.support_add
    (fun powers coefficient => |coefficient| * monomialWeight weight powers) (by simp)
  unfold activity
  rw [hf, hs, ha, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro powers _
  simpa only [Finsupp.add_apply, add_mul] using
    mul_le_mul_of_nonneg_right (abs_add_le (MvPolynomial.coeff powers first) (MvPolynomial.coeff powers second)) (monomialWeight_nonneg weight hweight powers)

theorem activity_sum_le {Tag : Type*} (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (tables : Tag → Table Seed) (tags : Finset Tag) :
    activity weight (∑ tag ∈ tags, tables tag) ≤ ∑ tag ∈ tags, activity weight (tables tag) := by
  induction tags using Finset.induction_on with
  | empty => simp
  | @insert tag tags hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (activity_add_le weight hweight _ _).trans (add_le_add le_rfl ih)

/-- Submultiplicativity follows from the literal monomial multiplication
and triangle inequality for coefficient collisions. -/
theorem activity_mul_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (first second : Table Seed) :
    activity weight (first * second) ≤ activity weight first * activity weight second := by
  rw [MvPolynomial.mul_def]
  change activity weight (∑ powers ∈ first.support, ∑ other ∈ second.support,
    MvPolynomial.monomial (powers + other) (MvPolynomial.coeff powers first * MvPolynomial.coeff other second)) ≤ _
  calc
    _ ≤ ∑ powers ∈ first.support, activity weight (∑ other ∈ second.support,
        MvPolynomial.monomial (powers + other) (MvPolynomial.coeff powers first * MvPolynomial.coeff other second)) := activity_sum_le weight hweight _ _
    _ ≤ ∑ powers ∈ first.support, ∑ other ∈ second.support,
        activity weight (MvPolynomial.monomial (powers + other) (MvPolynomial.coeff powers first * MvPolynomial.coeff other second)) :=
      Finset.sum_le_sum fun powers _ => activity_sum_le weight hweight _ _
    _ = _ := by
      simp only [activity_monomial, abs_mul, monomialWeight_add]
      simp only [activity, Finsupp.sum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro powers _
      apply Finset.sum_congr rfl
      intro other _
      simp only [MvPolynomial.coeff]
      ring

/-- A seed's polynomial variable carries precisely its supplied activity. -/
@[simp] theorem activity_X (weight : Seed → ℝ) (seed : Seed) :
    activity weight (MvPolynomial.X seed : Table Seed) = weight seed := by
  simp [MvPolynomial.X, activity_monomial, monomialWeight, Finsupp.prod_single_index]

end

end AFT.RepresentedPolynomial

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Color : Type*} [Fintype Color]

/-- The literal primary/body input table, before output evaluation. -/
structure InputSeed (Color : Type*) where
  primaryOrder : ℕ
  bodyOrder : ℕ
  kernel : (Fin (primaryOrder + bodyOrder) → Color) → ℝ

def inputReference (primary body : FiniteDist Color) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → FiniteDist Color :=
  Fin.addCases (fun _ => primary) (fun _ => body)

def inputRate (primaryPool bodyPool : ℝ) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → ℝ :=
  Fin.addCases (fun _ => (Real.sqrt primaryPool)⁻¹) (fun _ => (Real.sqrt bodyPool)⁻¹)

def inputWeight (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seed : InputSeed Color) : ℝ :=
  MixedKernel.analyticActivity radius seed.bodyOrder (inputRate primaryPool bodyPool seed)
    (inputReference primary body seed) seed.kernel

theorem inputWeight_nonneg (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seed : InputSeed Color) (hradius : 0 ≤ radius) :
    0 ≤ inputWeight primary body primaryPool bodyPool radius seed := by
  apply mul_nonneg (pow_nonneg hradius _) (MixedKernel.activity_nonneg _ _ _ _)
  intro slot
  unfold inputRate
  cases slot using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right]
  all_goals exact inv_nonneg.mpr (Real.sqrt_nonneg _)

omit [Fintype Color] in
@[simp] theorem activity_C (weight : Seed → ℝ) (scalar : ℝ) :
    activity weight (MvPolynomial.C scalar : Table Seed) = |scalar| := by
  rw [MvPolynomial.C_apply, activity_monomial, monomialWeight_zero, mul_one]

omit [Fintype Color] in
@[simp] theorem activity_neg (weight : Seed → ℝ) (table : Table Seed) :
    activity weight (-table) = activity weight table := by
  simp only [activity, MvPolynomial.sum_def, MvPolynomial.support_neg,
    MvPolynomial.coeff_neg, abs_neg]

omit [Fintype Color] in
theorem activity_pow_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (table : Table Seed) (power : ℕ) :
    activity weight (table ^ power) ≤ activity weight table ^ power := by
  induction power with
  | zero => simp
  | succ power ih =>
    rw [pow_succ, pow_succ]
    exact (activity_mul_le weight hweight _ _).trans
      (mul_le_mul_of_nonneg_right ih (activity_nonneg weight hweight table))

omit [Fintype Color] in
/-- An explicit finite exponential in the formal seed algebra. -/
def exponential (table : Table Seed) (degree : ℕ) : Table Seed :=
  ∑ index ∈ Finset.range (degree + 1), MvPolynomial.C ((index.factorial : ℝ)⁻¹) * table ^ index

omit [Fintype Color] in
theorem exponential_sub_one (table : Table Seed) (degree : ℕ) :
    exponential table degree - 1 =
      ∑ index ∈ Finset.range degree, MvPolynomial.C (((index + 1).factorial : ℝ)⁻¹) * table ^ (index + 1) := by
  rw [exponential, Finset.sum_range_succ']
  simp

omit [Fintype Color] in
theorem activity_exponential_sub_one (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (table : Table Seed) (degree : ℕ) :
    activity weight (exponential table degree - 1) ≤ Real.exp (activity weight table) - 1 := by
  rw [exponential_sub_one]
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index ∈ Finset.range degree, activity weight table ^ (index + 1) / (index + 1).factorial := by
      apply Finset.sum_le_sum
      intro index _
      have hh := (activity_mul_le weight hweight (MvPolynomial.C (((index + 1).factorial : ℝ)⁻¹))
        (table ^ (index + 1))).trans
        (mul_le_mul_of_nonneg_left (activity_pow_le weight hweight table (index + 1))
          (activity_nonneg weight hweight _))
      simpa only [activity_C, abs_of_nonneg (by positivity : 0 ≤ (((index + 1).factorial : ℝ)⁻¹)),
        div_eq_mul_inv, mul_comm] using hh
    _ ≤ _ := by
      have hh := Real.sum_le_exp_of_nonneg (activity_nonneg weight hweight table) (degree + 1)
      rw [Finset.sum_range_succ'] at hh
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hh
      linarith

omit [Fintype Color] in
/-- Finite inversion preserves the small input activity before truncation;
the algebraic residual is still the exact next power. -/
theorem activity_finiteCorrection_le_two (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (error : Table Seed) (depth : ℕ) (hsmall : activity weight error ≤ 1 / 2) :
    activity weight (finiteCorrection error depth) ≤ 2 := by
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index ∈ Finset.range (depth + 1), (1 / 2 : ℝ) ^ index := by
      apply Finset.sum_le_sum
      intro index _
      exact (activity_pow_le weight hweight (-error) index).trans
        (pow_le_pow_left₀ (activity_nonneg weight hweight _) (by simpa only [activity_neg] using hsmall) _)
    _ ≤ ∑' index : ℕ, (1 / 2 : ℝ) ^ index :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum _ (fun _ _ => by positivity)
    _ = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num

end

end AFT.RepresentedPolynomial

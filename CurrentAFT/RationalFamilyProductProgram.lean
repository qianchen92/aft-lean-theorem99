import CurrentAFT.CalibrationCoordinateError

/-! # Literal rational truncated products of joint coefficient tables

All ordered slot permutations and their factorial normalizers are retained.
The finite arity convolution agrees with the actual canonical family product.
The input arrays need not themselves be centered or symmetric.
-/
namespace CurrentAFT.RationalFamilyProductProgram
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

abbrev Kernel (Scalar Primary Body : Type*) (r s : ℕ) := (Fin r → Primary) → (Fin s → Body) → Scalar
abbrev Table (Scalar Primary Body : Type*) (order : ℕ) :=
  (arity : TruncatedArity order) → Kernel Scalar Primary Body arity.val.1.val arity.val.2.val

def average {Scalar : Type*} [Field Scalar] (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → Scalar) : Scalar :=
  (r.factorial : Scalar)⁻¹ * (s.factorial : Scalar)⁻¹ * ∑ first, ∑ second, value first second

def tensor {Scalar Primary Body : Type*} [Mul Scalar] {r s r' s' : ℕ}
    (first : Kernel Scalar Primary Body r s) (second : Kernel Scalar Primary Body r' s') :
    Kernel Scalar Primary Body (r+r') (s+s') :=
  fun colors centers =>
    first (fun index => colors (finSumFinEquiv (Sum.inl index)))
      (fun index => centers (finSumFinEquiv (Sum.inl index))) *
    second (fun index => colors (finSumFinEquiv (Sum.inr index)))
      (fun index => centers (finSumFinEquiv (Sum.inr index)))

def homogeneous {Scalar Primary Body : Type*} [Field Scalar] {r s r' s' : ℕ}
    (first : Kernel Scalar Primary Body r s) (second : Kernel Scalar Primary Body r' s') :
    Kernel Scalar Primary Body (r+r') (s+s') :=
  fun colors centers => average (r+r') (s+s')
    (fun primaryOrder bodyOrder => tensor first second (colors ∘ primaryOrder) (centers ∘ bodyOrder))

def product {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ)
    (first second : Table Scalar Primary Body order) : Table Scalar Primary Body order :=
  fun output colors centers => ∑ left : TruncatedArity order, ∑ right : TruncatedArity order,
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      homogeneous (first left) (second right) (colors ∘ finCongr hmatch.1) (centers ∘ finCongr hmatch.2)
    else 0

def realTable {Primary Body : Type*} (order : ℕ) (table : Table ℚ Primary Body order) :
    Table ℝ Primary Body order := fun arity colors centers => table arity colors centers

noncomputable section
open scoped Classical
local instance productFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem average_cast (r s : ℕ) (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℚ) :
    ((average r s value : ℚ) : ℝ) = average r s (fun first second => (value first second : ℝ)) := by
  simp only [average, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum]

theorem homogeneous_cast {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℚ Primary Body r s) (second : Kernel ℚ Primary Body r' s')
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    ((homogeneous first second colors centers : ℚ) : ℝ) =
      homogeneous (fun colors centers => (first colors centers : ℝ))
        (fun colors centers => (second colors centers : ℝ)) colors centers := by
  rw [homogeneous, average_cast]
  simp only [tensor, Rat.cast_mul, homogeneous]

theorem product_cast {Primary Body : Type*} (order : ℕ) (first second : Table ℚ Primary Body order) :
    realTable order (product order first second) = product order (realTable order first) (realTable order second) := by
  funext output colors centers
  simp only [realTable, product, Rat.cast_sum]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · exact homogeneous_cast (first left) (second right) _ _
  · exact Rat.cast_zero

theorem homogeneous_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) {r s r' s' : ℕ}
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    homogeneous first.val second.val = (homogeneousProduct primary body first second).val := by
  funext colors centers
  rw [homogeneousProduct_apply]
  unfold homogeneous average
  apply congrArg (fun total : ℝ => ((r+r').factorial : ℝ)⁻¹ * ((s+s').factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro firstOrder _
  apply Finset.sum_congr (by ext second; simp)
  intro secondOrder _
  rfl

theorem product_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    product order (fun arity => (first arity).val) (fun arity => (second arity).val) =
      fun arity => (familyProduct primary body order first second arity).val := by
  funext output colors centers
  simp only [product, familyProduct, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr (by ext left; simp)
  intro left _
  apply Finset.sum_congr (by ext right; simp)
  intro right _
  split_ifs with hmatch
  · rw [homogeneous_actual, transportKernel_val]
    rfl
  · rfl

theorem average_bound (r s : ℕ)
    (value : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) (bound : ℝ)
    (hvalue : ∀ first second, |value first second| ≤ bound) : |average r s value| ≤ bound := by
  have h := CalibrationCoordinateError.expectation_abs_bound
    ((FiniteDist.uniform (Equiv.Perm (Fin r))).prod (FiniteDist.uniform (Equiv.Perm (Fin s))))
    (fun pair => value pair.1 pair.2) bound (fun pair => hvalue pair.1 pair.2)
  convert h using 1
  congr 1
  simp only [average, FiniteDist.expectation, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, Fintype.card_perm, Fintype.card_fin, ← Finset.mul_sum]
  apply congrArg (fun total : ℝ => (r.factorial : ℝ)⁻¹ * (s.factorial : ℝ)⁻¹ * total)
  apply Finset.sum_congr (by ext first; simp)
  intro first _
  apply Finset.sum_congr (by ext second; simp)
  intro second _
  rfl

theorem average_sub (r s : ℕ) (first second : Equiv.Perm (Fin r) → Equiv.Perm (Fin s) → ℝ) :
    average r s first - average r s second = average r s (fun p b => first p b - second p b) := by
  simp only [average, Finset.sum_sub_distrib, mul_sub]

theorem multiply_error (first second computedFirst computedSecond A B e f : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (he : 0 ≤ e) (_hf : 0 ≤ f)
    (ha : |first| ≤ A) (hb : |second| ≤ B)
    (hea : |computedFirst-first| ≤ e) (heb : |computedSecond-second| ≤ f) :
    |computedFirst*computedSecond-first*second| ≤ e*B + (A+e)*f := by
  have hcomputed : |computedFirst| ≤ A+e := by
    have h := abs_add_le first (computedFirst-first)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add ha hea)
  have hequal : computedFirst*computedSecond-first*second =
      (computedFirst-first)*second + computedFirst*(computedSecond-second) := by ring
  rw [hequal]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hea hb (abs_nonneg _) he)
      (mul_le_mul hcomputed heb (abs_nonneg _) (add_nonneg hA he)))

theorem homogeneous_bound {Primary Body : Type*} {r s r' s' : ℕ}
    (first : Kernel ℝ Primary Body r s) (second : Kernel ℝ Primary Body r' s')
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |homogeneous first second colors centers| ≤ A*B := by
  apply average_bound
  intro p b
  unfold tensor
  rw [abs_mul]
  exact mul_le_mul (ha _ _) (hb _ _) (abs_nonneg _) hA

theorem homogeneous_error {Primary Body : Type*} {r s r' s' : ℕ}
    (first computedFirst : Kernel ℝ Primary Body r s) (second computedSecond : Kernel ℝ Primary Body r' s')
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ colors centers, |first colors centers| ≤ A)
    (hb : ∀ colors centers, |second colors centers| ≤ B)
    (hea : ∀ colors centers, |computedFirst colors centers-first colors centers| ≤ e)
    (heb : ∀ colors centers, |computedSecond colors centers-second colors centers| ≤ f)
    (colors : Fin (r+r') → Primary) (centers : Fin (s+s') → Body) :
    |homogeneous computedFirst computedSecond colors centers - homogeneous first second colors centers| ≤
      e*B + (A+e)*f := by
  unfold homogeneous
  rw [average_sub]
  apply average_bound
  intro p b
  exact multiply_error _ _ _ _ A B e f hA hB he hf (ha _ _) (hb _ _) (hea _ _) (heb _ _)

theorem product_error {Primary Body : Type*} (order : ℕ)
    (first computedFirst second computedSecond : Table ℝ Primary Body order)
    (A B e f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e) (hf : 0 ≤ f)
    (ha : ∀ arity colors centers, |first arity colors centers| ≤ A)
    (hb : ∀ arity colors centers, |second arity colors centers| ≤ B)
    (hea : ∀ arity colors centers, |computedFirst arity colors centers-first arity colors centers| ≤ e)
    (heb : ∀ arity colors centers, |computedSecond arity colors centers-second arity colors centers| ≤ f)
    (output : TruncatedArity order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    |product order computedFirst computedSecond output colors centers - product order first second output colors centers| ≤
      (Fintype.card (TruncatedArity order) : ℝ)^2 * (e*B + (A+e)*f) := by
  unfold product
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _left : TruncatedArity order, ∑ _right : TruncatedArity order, (e*B + (A+e)*f) := by
      apply Finset.sum_le_sum
      intro left _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro right _
      split_ifs with hmatch
      · exact homogeneous_error _ _ _ _ A B e f hA hB he hf (ha left) (hb right) (hea left) (heb right) _ _
      · simp only [sub_self, abs_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end
end CurrentAFT.RationalFamilyProductProgram

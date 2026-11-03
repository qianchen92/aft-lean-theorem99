import AFT.CoreProjectionEnergy
import AFT.SafeFiniteNeumann

/-! # Fixed-coordinate bounds for the literal finite safe pair input -/

open scoped BigOperators

namespace AFT.SafeConvolution

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

/-- Finite probability averaging contracts counting L2, also when the
profiles are signed and have arbitrary internal dependencies. -/
theorem probability_mixture_L2_le (source : FiniteDist σ) (profiles : σ → ι → ℝ)
    (bound : ℝ) (hbound : ∀ sample, countingL2 (profiles sample) ≤ bound) :
    countingL2 (fun x => ∑ sample, source.weight sample * profiles sample x) ≤ bound := by
  classical
  have heq : (fun x => ∑ sample, source.weight sample * profiles sample x) =
      ∑ sample, source.weight sample • profiles sample := by ext; simp
  rw [heq]
  calc
    _ ≤ ∑ sample, countingL2 (source.weight sample • profiles sample) := countingL2_sum _ _
    _ = ∑ sample, source.weight sample * countingL2 (profiles sample) := by
      simp only [countingL2_smul, abs_of_nonneg (source.nonneg _)]
    _ ≤ ∑ sample, source.weight sample * bound :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hbound sample) (source.nonneg sample)
    _ = bound := by rw [← Finset.sum_mul, source.sum_one, one_mul]

end AFT.SafeConvolution

namespace AFT.SafePair

open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coreSeed_row_L2_le (core : Finset ι) (mass : ι → ι → ℝ)
    (hne : core.Nonempty) (bound : ℝ) (hbound : ∀ x, countingL2 (mass x) ≤ bound) (x : ι) :
    countingL2 (coreSeed core mass x) ≤ 2 * bound := by
  classical
  let centered : ι → ι → ℝ := fun a => centerOnCore core (restrictPair core mass a)
  have hcenter (a : ι) : countingL2 (centered a) ≤ bound := by
    apply le_trans (Real.sqrt_le_sqrt (centerOnCore_square_le core _ hne
      (by intro c hc; simp [restrictPair, hc])))
    apply le_trans (Real.sqrt_le_sqrt (show (∑ c, restrictPair core mass a c ^ 2) ≤ ∑ c, mass a c ^ 2 from ?_))
    · exact hbound a
    · exact Finset.sum_le_sum fun c _ => by simp only [restrictPair]; split_ifs <;> simp [sq_nonneg]
  have hzero (a : ι) (ha : a ∉ core) : centered a = 0 := by
    funext c
    simp [centered, centerOnCore, restrictPair, ha]
  let average : ι → ℝ := fun c => ∑ a, uniformFiniteProfile core a * centered a c
  have havg : countingL2 average ≤ bound :=
    probability_mixture_L2_le ⟨uniformFiniteProfile core,
      (by intro a; simp [uniformFiniteProfile]; split_ifs <;> positivity),
      uniformFiniteProfile_mass core hne⟩ centered bound hcenter
  have hnonneg : 0 ≤ bound := (countingL2_nonneg (mass x)).trans (hbound x)
  by_cases hx : x ∈ core
  · have heq : coreSeed core mass x = centered x - average := by
      funext c
      rw [coreSeed_eq_centers]
      change centered x c - uniformFiniteProfile core x * ∑ a, centered a c = _
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ core
      · simp [uniformFiniteProfile, hx, ha]
      · simp [uniformFiniteProfile, ha, hzero a ha]
    rw [heq, sub_eq_add_neg]
    exact (countingL2_add _ _).trans (by rw [countingL2_neg]; linarith [hcenter x])
  · have heq : coreSeed core mass x = 0 := by
      funext c
      exact coreSeed_supported core mass x c (Or.inl hx)
    rw [heq]
    simp only [countingL2, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    positivity

end AFT.SafePair

namespace AFT.SafeConvolution

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- A uniform bound on every fixed first-coordinate Hilbert fiber. -/
def RowBound (bound : ℝ) (profile : G × G → ℝ) : Prop :=
  ∀ first, countingL2 (fun second => profile (first, second)) ≤ bound

omit [AddCommGroup G] in
theorem RowBound.add {firstBound secondBound : ℝ} {first second : G × G → ℝ}
    (hfirst : RowBound firstBound first) (hsecond : RowBound secondBound second) :
    RowBound (firstBound + secondBound) (first + second) := by
  intro x
  exact (countingL2_add (fun y => first (x,y)) (fun y => second (x,y))).trans
    (add_le_add (hfirst x) (hsecond x))

omit [AddCommGroup G] in
theorem RowBound.neg {bound : ℝ} {profile : G × G → ℝ} (h : RowBound bound profile) :
    RowBound bound (-profile) := by
  intro x
  change countingL2 (-(fun y => profile (x,y))) ≤ bound
  rw [countingL2_neg]
  exact h x

theorem RowBound.probability_convolution {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) (source : FiniteDist (G × G)) :
    RowBound bound (convolution source.weight profile) := by
  intro x
  apply probability_mixture_L2_le source (fun shift y => profile ((x,y) - shift)) bound
  intro shift
  change Real.sqrt (∑ y, profile (x - shift.1, y - shift.2) ^ 2) ≤ bound
  rw [translated_sum (fun y => profile (x - shift.1,y) ^ 2)]
  exact h (x - shift.1)

theorem RowBound.probability_power {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) (source : FiniteDist (G × G)) (order : ℕ) :
    RowBound bound ((convolution source.weight ^ order) profile) := by
  induction order with
  | zero => simpa using h
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact ih.probability_convolution source

theorem RowBound.probability_defect {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) (source : FiniteDist (G × G)) :
    RowBound (2 * bound) ((1 - convolution source.weight) profile) := by
  simpa only [two_mul] using h.add (h.probability_convolution source).neg

theorem RowBound.probability_defect_power {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) (source : FiniteDist (G × G)) (order : ℕ) :
    RowBound (2 ^ order * bound) (((1 - convolution source.weight) ^ order) profile) := by
  induction order with
  | zero => simpa using h
  | succ order ih =>
    simp only [pow_succ', Module.End.mul_apply]
    convert ih.probability_defect source using 1; ring

omit [AddCommGroup G] in
theorem RowBound.sum {α : Type*} (indices : Finset α) (profiles : α → G × G → ℝ)
    (bounds : α → ℝ) (h : ∀ i ∈ indices, RowBound (bounds i) (profiles i)) :
    RowBound (∑ i ∈ indices, bounds i) (∑ i ∈ indices, profiles i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => intro x; simp [countingL2]
  | @insert i indices hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Every retained term has its fixed-fiber cost; the finite inverse costs
only the actual geometric sum, independently of the palette size. -/
theorem RowBound.compactRootInput {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) (root smooth : FiniteDist (G × G)) (depth : ℕ) :
    RowBound ((∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i) * bound)
      (SafeConvolution.compactRootInput root smooth depth profile) := by
  classical
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  have heq : SafeConvolution.compactRootInput root smooth depth profile =
      ∑ i ∈ Finset.range (depth + 1), ((1 - convolution root.weight) ^ i)
        ((convolution smooth.weight ^ (depth + 1)) profile) := by
    simp only [SafeConvolution.compactRootInput, finiteCorrection, LinearMap.sum_apply, hb]
  rw [heq, Finset.sum_mul]
  apply RowBound.sum
  intro i _
  exact (h.probability_power smooth (depth + 1)).probability_defect_power root i

end AFT.SafeConvolution

namespace AFT.SafePair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem centerOnCore_abs_le (core : Finset ι) (profile : ι → ℝ)
    (hne : core.Nonempty) (bound : ℝ) (hbound : ∀ x, |profile x| ≤ bound)
    (hsupport : ∀ x, x ∉ core → profile x = 0) (x : ι) :
    |centerOnCore core profile x| ≤ 2 * bound := by
  classical
  have hnonneg : 0 ≤ bound := (abs_nonneg (profile x)).trans (hbound x)
  by_cases hx : x ∈ core
  · have heq : uniformFiniteProfile core x * ∑ a, profile a =
        ∑ a, uniformFiniteProfile core a * profile a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ core
      · simp [uniformFiniteProfile, hx, ha]
      · simp [uniformFiniteProfile, hx, ha, hsupport a ha]
    have havg : |∑ a, uniformFiniteProfile core a * profile a| ≤ bound := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ = ∑ a, uniformFiniteProfile core a * |profile a| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg (by simp [uniformFiniteProfile]; split_ifs <;> positivity)]
        _ ≤ ∑ a, uniformFiniteProfile core a * bound :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hbound a)
            (by simp [uniformFiniteProfile]; split_ifs <;> positivity)
        _ = bound := by rw [← Finset.sum_mul, uniformFiniteProfile_mass core hne, one_mul]
    unfold centerOnCore
    rw [heq]
    exact (abs_sub _ _).trans (by linarith [hbound x])
  · rw [centerOnCore_supported core profile hsupport x hx, abs_zero]
    positivity

theorem coreSeed_abs_le (core : Finset ι) (mass : ι → ι → ℝ)
    (hne : core.Nonempty) (bound : ℝ) (hbound : ∀ x y, |mass x y| ≤ bound)
    (x y : ι) : |coreSeed core mass x y| ≤ 4 * bound := by
  have hnonneg : 0 ≤ bound := (abs_nonneg (mass x y)).trans (hbound x y)
  rw [coreSeed_eq_centers]
  have h := centerOnCore_abs_le core
    (fun a => centerOnCore core (restrictPair core mass a) y) hne (2 * bound)
    (fun a => centerOnCore_abs_le core _ hne bound (fun b => by
      simp only [restrictPair]
      split_ifs
      · exact hbound a b
      · simpa only [abs_zero] using hnonneg)
      (by intro b hb; simp [restrictPair, hb]) y)
    (by intro a ha; simp [centerOnCore, restrictPair, ha]) x
  linarith

end AFT.SafePair

namespace AFT.SafeConvolution

variable {G : Type*} [Fintype G] [AddCommGroup G]

def SupBound (bound : ℝ) (profile : G → ℝ) : Prop := ∀ x, |profile x| ≤ bound

omit [Fintype G] [AddCommGroup G] in
theorem SupBound.add {a b : ℝ} {first second : G → ℝ}
    (ha : SupBound a first) (hb : SupBound b second) : SupBound (a + b) (first + second) :=
  fun x => (abs_add_le (first x) (second x)).trans (add_le_add (ha x) (hb x))

omit [Fintype G] [AddCommGroup G] in
theorem SupBound.neg {bound : ℝ} {profile : G → ℝ} (h : SupBound bound profile) :
    SupBound bound (-profile) := by intro x; simpa only [Pi.neg_apply, abs_neg] using h x

theorem SupBound.probability_convolution {bound : ℝ} {profile : G → ℝ}
    (h : SupBound bound profile) (source : FiniteDist G) :
    SupBound bound (convolution source.weight profile) := by
  intro x
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ = ∑ shift, source.weight shift * |profile (x - shift)| := by
      simp only [abs_mul, abs_of_nonneg (source.nonneg _)]
    _ ≤ ∑ shift, source.weight shift * bound :=
      Finset.sum_le_sum fun shift _ => mul_le_mul_of_nonneg_left (h _) (source.nonneg shift)
    _ = bound := by rw [← Finset.sum_mul, source.sum_one, one_mul]

theorem SupBound.probability_power {bound : ℝ} {profile : G → ℝ}
    (h : SupBound bound profile) (source : FiniteDist G) (order : ℕ) :
    SupBound bound ((convolution source.weight ^ order) profile) := by
  induction order with
  | zero => simpa using h
  | succ order ih => rw [pow_succ', Module.End.mul_apply]; exact ih.probability_convolution source

theorem SupBound.probability_defect {bound : ℝ} {profile : G → ℝ}
    (h : SupBound bound profile) (source : FiniteDist G) :
    SupBound (2 * bound) ((1 - convolution source.weight) profile) := by
  simpa only [two_mul] using h.add (h.probability_convolution source).neg

theorem SupBound.probability_defect_power {bound : ℝ} {profile : G → ℝ}
    (h : SupBound bound profile) (source : FiniteDist G) (order : ℕ) :
    SupBound (2 ^ order * bound) (((1 - convolution source.weight) ^ order) profile) := by
  induction order with
  | zero => simpa using h
  | succ order ih =>
    simp only [pow_succ', Module.End.mul_apply]
    convert ih.probability_defect source using 1; ring

omit [Fintype G] [AddCommGroup G] in
theorem SupBound.sum {α : Type*} (indices : Finset α) (profiles : α → G → ℝ)
    (bounds : α → ℝ) (h : ∀ i ∈ indices, SupBound (bounds i) (profiles i)) :
    SupBound (∑ i ∈ indices, bounds i) (∑ i ∈ indices, profiles i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => intro x; simp
  | @insert i indices hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem SupBound.compactRootInput {bound : ℝ} {profile : G → ℝ}
    (h : SupBound bound profile) (root smooth : FiniteDist G) (depth : ℕ) :
    SupBound ((∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i) * bound)
      (SafeConvolution.compactRootInput root smooth depth profile) := by
  classical
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  have heq : SafeConvolution.compactRootInput root smooth depth profile =
      ∑ i ∈ Finset.range (depth + 1), ((1 - convolution root.weight) ^ i)
        ((convolution smooth.weight ^ (depth + 1)) profile) := by
    simp only [SafeConvolution.compactRootInput, finiteCorrection, LinearMap.sum_apply, hb]
  rw [heq, Finset.sum_mul]
  apply SupBound.sum
  intro i _
  exact (h.probability_power smooth (depth + 1)).probability_defect_power root i

end AFT.SafeConvolution

namespace AFT.SafeConvolution

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem convolution_transpose (source : FiniteDist (G × G)) (profile : G × G → ℝ) :
    (fun point : G × G => convolution source.weight profile point.swap) =
      convolution (source.map Prod.swap).weight (fun point : G × G => profile point.swap) := by
  funext point
  rw [convolution_map_apply, convolution_apply]
  rfl

theorem convolution_power_transpose (source : FiniteDist (G × G)) (order : ℕ)
    (profile : G × G → ℝ) :
    (fun point : G × G => ((convolution source.weight ^ order) profile) point.swap) =
      ((convolution (source.map Prod.swap).weight ^ order) (fun point : G × G => profile point.swap)) := by
  induction order with
  | zero => rfl
  | succ order ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [convolution_transpose, ih]

theorem convolution_defect_power_transpose (source : FiniteDist (G × G)) (order : ℕ)
    (profile : G × G → ℝ) :
    (fun point : G × G => (((1 - convolution source.weight) ^ order) profile) point.swap) =
      (((1 - convolution (source.map Prod.swap).weight) ^ order) (fun point : G × G => profile point.swap)) := by
  induction order with
  | zero => rfl
  | succ order ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change ((fun point : G × G => (((1 - convolution source.weight) ^ order) profile) point.swap) -
      (fun point : G × G => convolution source.weight (((1 - convolution source.weight) ^ order) profile) point.swap)) = _
    rw [convolution_transpose, ih]
    rfl

theorem compactRootInput_transpose (root smooth : FiniteDist (G × G)) (depth : ℕ) (profile : G × G → ℝ) :
    (fun point : G × G => compactRootInput root smooth depth profile point.swap) =
      compactRootInput (root.map Prod.swap) (smooth.map Prod.swap) depth (fun point : G × G => profile point.swap) := by
  have hrepr (root smooth : FiniteDist (G × G)) (profile : G × G → ℝ) :
      compactRootInput root smooth depth profile =
      ∑ i ∈ Finset.range (depth + 1), ((1 - convolution root.weight) ^ i)
        ((convolution smooth.weight ^ (depth + 1)) profile) := by
    have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
    simp only [compactRootInput, finiteCorrection, LinearMap.sum_apply, hb]
  rw [hrepr, hrepr]
  funext point
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun ((convolution_defect_power_transpose root i _).trans
    (congrArg (((1 - convolution (root.map Prod.swap).weight) ^ i) ·)
      (convolution_power_transpose smooth (depth + 1) profile))) point

/-- The second fixed coordinate has exactly the same finite cost, with no
symmetry assumption on the actual joint root channel. -/
theorem column_compactRootInput {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound (fun point : G × G => profile point.swap))
    (root smooth : FiniteDist (G × G)) (depth : ℕ) :
    RowBound ((∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i) * bound)
      (fun point : G × G => compactRootInput root smooth depth profile point.swap) := by
  rw [compactRootInput_transpose]
  exact h.compactRootInput _ _ _

end AFT.SafeConvolution

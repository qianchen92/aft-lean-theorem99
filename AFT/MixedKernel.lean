import AFT.Hoeffding
import AFT.InverseMixedActivity

/-!
# The full mixed input activity on actual finite kernels

The coordinate rates are `pool⁻¹/²`; allowing a rate for each coordinate
covers both primary and body pools.  Every fixed-coordinate set is included.
The norm is taken on input kernels themselves, without identifying equal
images under an output evaluation map.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def freeze (fixed : Finset Slot) (values integrated : Slot → Color) : Slot → Color :=
  fun slot => if slot ∈ fixed then values slot else integrated slot

def fiberSq (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) : ℝ :=
  (FiniteDist.independent reference).l2Sq fun integrated => kernel (freeze fixed values integrated)

def fiberNorm (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) : ℝ :=
  ‖fun values => Real.sqrt (fiberSq reference kernel fixed values)‖

def activity (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) : ℝ :=
  (∏ slot, rate slot) * ∑ fixed : Finset Slot, (∏ slot ∈ fixed, rate slot) *
    fiberNorm reference kernel fixed

theorem fiberSq_nonneg (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) : 0 ≤ fiberSq reference kernel fixed values :=
  FiniteDist.l2Sq_nonneg _ _

theorem fiberNorm_nonneg (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) : 0 ≤ fiberNorm reference kernel fixed := norm_nonneg _

theorem fiberSq_le_norm_sq (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) :
    fiberSq reference kernel fixed values ≤ fiberNorm reference kernel fixed ^ 2 := by
  have h := norm_le_pi_norm (fun values => Real.sqrt (fiberSq reference kernel fixed values)) values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hh := sq_le_sq₀ (Real.sqrt_nonneg _) (fiberNorm_nonneg reference kernel fixed) |>.mpr h
  rwa [Real.sq_sqrt (fiberSq_nonneg reference kernel fixed values)] at hh

theorem fiberNorm_add_le (reference : Slot → FiniteDist Color)
    (first second : (Slot → Color) → ℝ) (fixed : Finset Slot) :
    fiberNorm reference (first + second) fixed ≤
      fiberNorm reference first fixed + fiberNorm reference second fixed := by
  apply (pi_norm_le_iff_of_nonneg
    (add_nonneg (fiberNorm_nonneg reference first fixed) (fiberNorm_nonneg reference second fixed))).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh := weightedDensity_sqrt_add_le (FiniteDist.independent reference).weight
    (fun integrated => first (freeze fixed values integrated))
    (fun integrated => second (freeze fixed values integrated)) (FiniteDist.independent reference).nonneg
  have hf := norm_le_pi_norm (fun x => Real.sqrt (fiberSq reference first fixed x)) values
  have hs := norm_le_pi_norm (fun x => Real.sqrt (fiberSq reference second fixed x)) values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hf hs
  exact hh.trans (add_le_add hf hs)

@[simp] theorem fiberNorm_zero (reference : Slot → FiniteDist Color) (fixed : Finset Slot) :
    fiberNorm reference (0 : (Slot → Color) → ℝ) fixed = 0 := by
  simp [fiberNorm, fiberSq, FiniteDist.l2Sq, FiniteDist.expectation]
  rfl

theorem fiberNorm_smul (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (scalar : ℝ) :
    fiberNorm reference (scalar • kernel) fixed = |scalar| * fiberNorm reference kernel fixed := by
  have heq (values : Slot → Color) :
      fiberSq reference (scalar • kernel) fixed values = scalar ^ 2 * fiberSq reference kernel fixed values := by
    simp only [fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro integrated _
    ring
  have hfun : (fun values => Real.sqrt (fiberSq reference (scalar • kernel) fixed values)) =
      |scalar| • (fun values => Real.sqrt (fiberSq reference kernel fixed values)) := by
    funext values
    rw [heq, Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]
    rfl
  unfold fiberNorm
  rw [hfun, norm_smul, Real.norm_eq_abs, abs_abs]

theorem activity_nonneg (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    0 ≤ activity rate reference kernel := by
  exact mul_nonneg (Finset.prod_nonneg fun slot _ => hrate slot)
    (Finset.sum_nonneg fun fixed _ => mul_nonneg
      (Finset.prod_nonneg fun slot _ => hrate slot) (fiberNorm_nonneg reference kernel fixed))

@[simp] theorem activity_zero (rate : Slot → ℝ) (reference : Slot → FiniteDist Color) :
    activity rate reference (0 : (Slot → Color) → ℝ) = 0 := by simp [activity]

theorem activity_add_le (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (first second : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    activity rate reference (first + second) ≤ activity rate reference first + activity rate reference second := by
  unfold activity
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun slot _ => hrate slot)
  apply Finset.sum_le_sum
  intro fixed _
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (fiberNorm_add_le reference first second fixed)
    (Finset.prod_nonneg fun slot _ => hrate slot)

theorem activity_smul (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (scalar : ℝ) :
    activity rate reference (scalar • kernel) = |scalar| * activity rate reference kernel := by
  unfold activity
  simp only [fiberNorm_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro fixed _
  ring

/-- The two-pool analytic activity includes the prescribed body-radius
factor at the input, before evaluation or root averaging. -/
def analyticActivity (radius : ℝ) (bodyOrder : ℕ) (rate : Slot → ℝ)
    (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ) : ℝ :=
  radius ^ bodyOrder * activity rate reference kernel

/-- Every displayed input representation is retained separately, even if
another representation happens to have the same leading output. -/
def representedActivity {Tag : Type*} [Fintype Tag]
    (rate : Tag → Slot → ℝ) (reference : Tag → Slot → FiniteDist Color)
    (kernel : Tag → (Slot → Color) → ℝ) (radius : ℝ) (bodyOrder : Tag → ℕ) : ℝ :=
  ∑ tag, analyticActivity radius (bodyOrder tag) (rate tag) (reference tag) (kernel tag)

end

end AFT.MixedKernel

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

@[simp] theorem fiberSq_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel Finset.univ values = kernel values ^ 2 := by
  have hf (integrated : Slot → Color) : freeze Finset.univ values integrated = values := by
    ext slot
    simp [freeze]
  simp only [fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, hf, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]

@[simp] theorem fiberNorm_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel Finset.univ = ‖kernel‖ := by
  simp only [fiberNorm, fiberSq_univ, Real.sqrt_sq_eq_abs]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg kernel)).mpr
    intro values
    rw [Real.norm_eq_abs, abs_abs]
    exact norm_le_pi_norm kernel values
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    have h := norm_le_pi_norm (fun values => |kernel values|) values
    simpa only [Real.norm_eq_abs, abs_abs] using h

/-- The fully fixed fiber prevents degeneracy even when a reference atom
has mass zero. -/
theorem sup_norm_le_activity (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 < rate slot) :
    (∏ slot, rate slot) ^ 2 * ‖kernel‖ ≤ activity rate reference kernel := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Slot)))
    (f := fun fixed => (∏ slot ∈ fixed, rate slot) * fiberNorm reference kernel fixed)
    (fun fixed _ => mul_nonneg (Finset.prod_nonneg fun slot _ => (hrate slot).le)
      (fiberNorm_nonneg reference kernel fixed)) (Finset.mem_univ Finset.univ)
  have hh := mul_le_mul_of_nonneg_left (a := ∏ slot, rate slot) h (Finset.prod_nonneg fun slot _ => (hrate slot).le)
  simpa only [fiberNorm_univ, sq, mul_assoc] using hh

theorem activity_eq_zero_iff (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 < rate slot) :
    activity rate reference kernel = 0 ↔ kernel = 0 := by
  constructor
  · intro hzero
    have h := sup_norm_le_activity rate reference kernel hrate
    rw [hzero] at h
    have hp : 0 < (∏ slot, rate slot) ^ 2 := pow_pos (Finset.prod_pos fun slot _ => hrate slot) _
    have hn : ‖kernel‖ ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · intro hzero
    subst kernel
    exact activity_zero _ _

/-- The empty fixed set is the full integrated L2 fiber. -/
@[simp] theorem fiberSq_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel ∅ values = (FiniteDist.independent reference).l2Sq kernel := by
  have hf (integrated : Slot → Color) : freeze ∅ values integrated = integrated := by
    ext slot
    simp [freeze]
  simp only [fiberSq, hf]

@[simp] theorem fiberNorm_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel ∅ = Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  haveI : Nonempty (Slot → Color) := by
    by_contra hn
    haveI : IsEmpty (Slot → Color) := not_nonempty_iff.mp hn
    have h := (FiniteDist.independent reference).sum_one
    simp at h
  simp only [fiberNorm, fiberSq_empty, pi_norm_const, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The integrated component retains exactly one inverse-square-root pool
factor per argument. -/
theorem integrated_norm_le_activity (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    (∏ slot, rate slot) * Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) ≤
      activity rate reference kernel := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Slot)))
    (f := fun fixed => (∏ slot ∈ fixed, rate slot) * fiberNorm reference kernel fixed)
    (fun fixed _ => mul_nonneg (Finset.prod_nonneg fun slot _ => hrate slot)
      (fiberNorm_nonneg reference kernel fixed)) (Finset.mem_univ (∅ : Finset Slot))
  have hh := mul_le_mul_of_nonneg_left (a := ∏ slot, rate slot) h (Finset.prod_nonneg fun slot _ => hrate slot)
  simpa only [fiberNorm_empty, Finset.prod_empty, one_mul] using hh

end

end AFT.MixedKernel

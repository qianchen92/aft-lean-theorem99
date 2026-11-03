import CurrentAFT.PairedScoreApproximation
import CurrentAFT.CalibrationPointCoordinates

/-! # Uniform numerical error for the actual public weight

The entire joint coefficient table is evaluated with the computed paired
reference. Distinct choices are averaged before summing all arities. No
factorization of a joint kernel or independence of endpoints is used.
-/
namespace CurrentAFT.NumericalWeightEvaluation
open AFT ActualControls ProposalPrimary ControlCoordinates GradedControlAlgebra
  CalibrationPointCoordinates PairedScoreApproximation TensorSupApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance weightFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def factor (security : ℕ) : ℝ := 1 + 2 * Parameters.modulus security
def localError (security bits : ℕ) : ℝ := RationalPairedLiftProgram.errorConstant security / (2 : ℝ)^bits

theorem factor_ge_one (security : ℕ) : 1 ≤ factor security := by
  unfold factor
  linarith [Nat.cast_nonneg (Parameters.modulus security) (α := ℝ)]
theorem localError_nonneg (security bits : ℕ) : 0 ≤ localError security bits := by
  unfold localError RationalPairedLiftProgram.errorConstant
  positivity

theorem actual_tensor_physical (security count : ℕ)
    (kernel : (Fin count → ActualControls.Palette security) → ℝ)
    (groups : Fin count → SafeControlGroups.SafeGroup security) :
    TensorChannel.apply count (fun _ => actual security) kernel groups =
      TensorChannel.apply count (fun _ => PhysicalSynthesis.pairedChannel security) kernel
        (fun index => SafeControlGroups.unwrap security (groups index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change actual security (fun first => TensorChannel.apply count (fun _ => actual security)
        (fun rest => kernel (Fin.cons first rest)) (fun index => groups index.succ)) (groups 0) = _
      rw [actual_eq_physical]
      apply congrArg (fun score => PhysicalSynthesis.pairedChannel security score
        (SafeControlGroups.unwrap security (groups 0)))
      funext first
      exact ih _ _

theorem joint_error (security bits count : ℕ)
    (kernel computed : (Fin count → ActualControls.Palette security) → ℝ)
    (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hkernel : ∀ word, |kernel word| ≤ bound)
    (hcomputed : ∀ word, |computed word - kernel word| ≤ error)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (groups : Fin count → SafeControlGroups.SafeGroup security) :
    |TensorChannel.apply count (fun _ => approximate security bits) computed groups -
      TensorChannel.apply count (fun _ => actual security) kernel groups| ≤
        factor security^count * (error + count * localError security bits * bound) := by
  have hlocal := tensor_difference (actual security) (approximate security bits)
    (factor security) (localError security bits) (factor_ge_one security) (localError_nonneg security bits)
    (actual_bound security) (approximate_bound security bits)
    (fun score bound hb hs point => difference security bits score bound hb hs hprecision hbudget point)
    count kernel bound hb hkernel groups
  have htable := tensor_bound (approximate security bits) (factor security)
    ((show (0:ℝ) ≤ 1 by norm_num).trans (factor_ge_one security)) (approximate_bound security bits)
    count (computed - kernel) error he hcomputed groups
  have hsub : TensorChannel.apply count (fun _ => approximate security bits) (computed - kernel) groups =
      TensorChannel.apply count (fun _ => approximate security bits) computed groups -
        TensorChannel.apply count (fun _ => approximate security bits) kernel groups := by
    exact congrFun ((TensorChannel.applyLinear count (fun _ => approximate security bits)).map_sub computed kernel) groups
  rw [hsub] at htable
  have htriangle := abs_sub_le
    (TensorChannel.apply count (fun _ => approximate security bits) computed groups)
    (TensorChannel.apply count (fun _ => approximate security bits) kernel groups)
    (TensorChannel.apply count (fun _ => actual security) kernel groups)
  exact htriangle.trans ((add_le_add htable hlocal).trans_eq (by ring))

theorem twoPool_bound {Primary Body : Type*} {r s primaryPool bodyPool : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (bound : ℝ) (hb : 0 ≤ bound) (hkernel : ∀ colors centers, |kernel colors centers| ≤ bound)
    (colors : Fin primaryPool → Primary) (centers : Fin bodyPool → Body) :
    |twoPoolUStatistic primaryPool bodyPool kernel colors centers| ≤ bound := by
  let count := primaryPool.descFactorial r * bodyPool.descFactorial s
  have hcard : Fintype.card ((Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool)) = count := by
    simp only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin, count]
  change |(∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
    kernel (colors ∘ selection.1) (centers ∘ selection.2)) /
      ((primaryPool.descFactorial r : ℝ) * (bodyPool.descFactorial s : ℝ))| ≤ bound
  simp only [abs_div, ← Nat.cast_mul]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (primaryPool.descFactorial r * bodyPool.descFactorial s : ℕ) by positivity)]
  have hsum : |∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
      kernel (colors ∘ selection.1) (centers ∘ selection.2)| ≤ count * bound := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool), bound :=
        Finset.sum_le_sum (fun selection _ => hkernel _ _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  change _ / (count : ℝ) ≤ bound
  by_cases hz : count = 0
  · simp only [hz, Nat.cast_zero, div_zero]; exact hb
  · have hc : (0 : ℝ) < count := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (div_le_iff₀ hc).mpr (hsum.trans_eq (mul_comm _ _))

theorem twoPool_difference {Primary Body : Type*} {r s primaryPool bodyPool : ℕ}
    (first second : DensityKernel (Primary := Primary) (Body := Body) r s)
    (error : ℝ) (he : 0 ≤ error)
    (herror : ∀ colors centers, |second colors centers - first colors centers| ≤ error)
    (colors : Fin primaryPool → Primary) (centers : Fin bodyPool → Body) :
    |twoPoolUStatistic primaryPool bodyPool second colors centers -
      twoPoolUStatistic primaryPool bodyPool first colors centers| ≤ error := by
  have h := twoPool_bound (second - first) error he herror colors centers
  simpa only [twoPoolUStatistic, Pi.sub_apply, Finset.sum_sub_distrib, sub_div] using h

def evaluate (security bits order primaryPool bodyPool : ℕ)
    (table : PointTable (ActualControls.Palette security) (SafePalette security) order)
    (groups : Fin primaryPool → SafeControlGroups.SafeGroup security)
    (centers : Fin bodyPool → SafePalette security) : ℝ :=
  table ⟨zeroArity order, Fin.elim0, Fin.elim0⟩ +
    ∑ arity : PositiveArity order,
      twoPoolUStatistic primaryPool bodyPool
        (fun selected selectedCenters => TensorChannel.apply arity.val.1.val
          (fun _ => approximate security bits)
          (fun colors => table ⟨positiveArity order arity, colors, selectedCenters⟩) selected)
        groups centers

theorem evaluate_error (security bits order primaryPool bodyPool : ℕ)
    (family : KernelFamily (primaryLaw security) (bodyReference security) order)
    (table : PointTable (ActualControls.Palette security) (SafePalette security) order)
    (bound error : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hfamily : ∀ point, |encode (primaryLaw security) (bodyReference security) order family point| ≤ bound)
    (htable : ∀ point, |table point - encode (primaryLaw security) (bodyReference security) order family point| ≤ error)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (groups : Fin primaryPool → SafeControlGroups.SafeGroup security)
    (centers : Fin bodyPool → SafePalette security) :
    |evaluate security bits order primaryPool bodyPool table groups centers -
      PhysicalSynthesis.coefficientWeight security order primaryPool bodyPool
        (familyToCoefficients (primaryLaw security) (bodyReference security) order family)
        (fun index => SafeControlGroups.unwrap security (groups index)) centers| ≤
      error + (Fintype.card (PositiveArity order) : ℝ) *
        (factor security^order * (error + order * localError security bits * bound)) := by
  have hterm (arity : PositiveArity order) :
      |twoPoolUStatistic primaryPool bodyPool
          (fun selected selectedCenters => TensorChannel.apply arity.val.1.val
            (fun _ => approximate security bits)
            (fun colors => table ⟨positiveArity order arity, colors, selectedCenters⟩) selected) groups centers -
        twoPoolUStatistic primaryPool bodyPool
          (PhysicalSynthesis.pairedKernel security arity.val.1.val arity.val.2.val
            (family (positiveArity order arity)).val)
          (fun index => SafeControlGroups.unwrap security (groups index)) centers| ≤
        factor security^order * (error + order * localError security bits * bound) := by
    have hpoint (selected : Fin arity.val.1.val → SafeControlGroups.SafeGroup security)
        (selectedCenters : Fin arity.val.2.val → SafePalette security) :=
      joint_error security bits arity.val.1.val
        (fun colors => (family (positiveArity order arity)).val colors selectedCenters)
        (fun colors => table ⟨positiveArity order arity, colors, selectedCenters⟩)
        bound error hb he (fun colors => hfamily ⟨positiveArity order arity, colors, selectedCenters⟩)
        (fun colors => htable ⟨positiveArity order arity, colors, selectedCenters⟩)
        hprecision hbudget selected
    have h := twoPool_difference
      (fun selected selectedCenters => TensorChannel.apply arity.val.1.val (fun _ => actual security)
        (fun colors => (family (positiveArity order arity)).val colors selectedCenters) selected)
      _ _ (by positivity [factor_ge_one security, localError_nonneg security bits]) hpoint groups centers
    simp only [actual_tensor_physical] at h
    change |_ - _| ≤ _ at h
    apply h.trans
    have hr : arity.val.1.val ≤ order := by have := arity.property.2; omega
    have hf : 0 ≤ factor security := (by norm_num : (0:ℝ) ≤ 1).trans (factor_ge_one security)
    have hl := localError_nonneg security bits
    apply mul_le_mul (pow_le_pow_right₀ (factor_ge_one security) hr) _ (by positivity) (pow_nonneg hf order)
    have hrreal : (arity.val.1.val : ℝ) ≤ order := by exact_mod_cast hr
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrreal hl) hb)
  have hzero := htable ⟨zeroArity order, Fin.elim0, Fin.elim0⟩
  unfold evaluate PhysicalSynthesis.coefficientWeight
  change |table ⟨zeroArity order, Fin.elim0, Fin.elim0⟩ + _ -
    ((family (zeroArity order)).val Fin.elim0 Fin.elim0 + _)| ≤ _
  rw [show ∀ (a b c d : ℝ), a + b - (c + d) = (a-c)+(b-d) by intros; ring,
    ← Finset.sum_sub_distrib]
  apply (abs_add_le _ _).trans
  apply (add_le_add hzero ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun arity _ => hterm arity)))).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end
end CurrentAFT.NumericalWeightEvaluation

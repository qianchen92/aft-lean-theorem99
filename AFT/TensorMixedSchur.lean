import AFT.MixedLawFreeze
import AFT.ThreeFiberActivity
import AFT.TensorChannelFormula

/-! # Alphabet-independent mixed-fiber bounds for finite signed tensor channels -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Slot Input Output : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Input] [Fintype Output]

/-- The literal joint matrix action, for an arbitrary finite coordinate set. -/
def matrixApply (matrix : Slot → Input → Output → ℝ)
    (kernel : (Slot → Input) → ℝ) (output : Slot → Output) : ℝ :=
  ∑ word, kernel word * ∏ slot, matrix slot (word slot) (output slot)

omit [Fintype Output] in
private theorem matrixApply_square_le (matrix : Slot → Input → Output → ℝ)
    (bound : ℝ)
    (hrow : ∀ slot output, (∑ input, |matrix slot input output|) ≤ bound)
    (kernel : (Slot → Input) → ℝ) (output : Slot → Output) :
    matrixApply matrix kernel output ^ 2 ≤
      bound ^ Fintype.card Slot * ∑ word, (∏ slot, |matrix slot (word slot) (output slot)|) * kernel word ^ 2 := by
  have hc : matrixApply matrix kernel output ^ 2 ≤
      (∑ word : Slot → Input, ∏ slot, |matrix slot (word slot) (output slot)|) *
        ∑ word, (∏ slot, |matrix slot (word slot) (output slot)|) * kernel word ^ 2 := by
    unfold matrixApply
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro word _; exact Finset.prod_nonneg fun slot _ => abs_nonneg _
    · intro word _; exact mul_nonneg (Finset.prod_nonneg fun slot _ => abs_nonneg _) (sq_nonneg _)
    · intro word _
      rw [mul_pow, ← Finset.abs_prod]
      nlinarith only [sq_abs (∏ slot, matrix slot (word slot) (output slot))]
  have hr : (∑ word : Slot → Input, ∏ slot, |matrix slot (word slot) (output slot)|) ≤ bound ^ Fintype.card Slot := by
    have he : (∑ word : Slot → Input, ∏ slot, |matrix slot (word slot) (output slot)|) =
        ∏ slot, ∑ point, |matrix slot point (output slot)| := by
      have hh := Fintype.prod_sum (fun slot point => |matrix slot point (output slot)|)
      refine Eq.trans ?_ hh.symm
      apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
    rw [he]
    calc
      _ ≤ ∏ _slot : Slot, bound := Finset.prod_le_prod
        (fun slot _ => Finset.sum_nonneg fun input _ => abs_nonneg _) (fun slot _ => hrow slot _)
      _ = _ := by simp
  exact hc.trans (mul_le_mul_of_nonneg_right hr
    (Finset.sum_nonneg fun word _ => mul_nonneg (Finset.prod_nonneg fun slot _ => abs_nonneg _) (sq_nonneg _)))

/-- Both Schur estimates tensorize in every genuine mixed fiber. The
conservative fixed-order constant avoids any minimum atom probability. -/
theorem matrixApply_fiberSq_le (input : Slot → FiniteDist Input)
    (output : Slot → FiniteDist Output) (matrix : Slot → Input → Output → ℝ)
    (bound : ℝ) (hbound : 1 ≤ bound)
    (hrow : ∀ slot value, 1 + (∑ point, |matrix slot point value|) ≤ bound)
    (hcolumn : ∀ slot point, (output slot).expectation (fun value => |matrix slot point value|) ≤
      bound * (input slot).weight point)
    (kernel : (Slot → Input) → ℝ) (fixed : Finset Slot) (values : Slot → Output) :
    fiberSq output (matrixApply matrix kernel) fixed values ≤
      (bound ^ (2 * Fintype.card Slot) * fiberNorm input kernel fixed) ^ 2 := by
  let weight (slot : Slot) (point : Input) :=
    if slot ∈ fixed then (input slot).weight point + |matrix slot point (values slot)| else (input slot).weight point
  have hn (slot) (point) : 0 ≤ weight slot point := by
    dsimp only [weight]
    split_ifs
    · exact add_nonneg ((input slot).nonneg point) (abs_nonneg _)
    · exact (input slot).nonneg point
  have hp (slot) : 0 < ∑ point, weight slot point := by
    by_cases hs : slot ∈ fixed
    · simp only [weight, hs, if_true, Finset.sum_add_distrib, FiniteDist.sum_one]
      have hh : 0 ≤ ∑ point, |matrix slot point (values slot)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · simpa only [weight, hs, if_false, FiniteDist.sum_one] using (by norm_num : (0 : ℝ) < 1)
  have hm (slot) : (∑ point, weight slot point) ≤ bound := by
    by_cases hs : slot ∈ fixed
    · simpa only [weight, hs, if_true, Finset.sum_add_distrib, FiniteDist.sum_one] using hrow slot (values slot)
    · simpa only [weight, hs, if_false, FiniteDist.sum_one] using hbound
  have hw := mixedWeight_energy_le input fixed weight hn hp
    (fun slot hs => by funext point; simp only [weight, hs, if_false]) kernel
  have hmass : (∏ slot, ∑ point, weight slot point) ≤ bound ^ Fintype.card Slot := by
    calc
      _ ≤ ∏ _slot : Slot, bound := Finset.prod_le_prod (fun slot _ => (hp slot).le) (fun slot _ => hm slot)
      _ = _ := by simp
  have henergy : (∑ word, (∏ slot, weight slot (word slot)) * kernel word ^ 2) ≤
      bound ^ Fintype.card Slot * fiberNorm input kernel fixed ^ 2 :=
    hw.trans (mul_le_mul_of_nonneg_right hmass (sq_nonneg _))
  have hpoint (word : Slot → Input) :
      (FiniteDist.independent output).expectation (fun integrated =>
        ∏ slot, |matrix slot (word slot) (freeze fixed values integrated slot)|) ≤
      bound ^ Fintype.card Slot * ∏ slot, weight slot (word slot) := by
    change (FiniteDist.independent output).expectation (productKernel (fun slot value =>
      |matrix slot (word slot) (if slot ∈ fixed then values slot else value)|)) ≤ _
    rw [expectation_productKernel]
    calc
      _ ≤ ∏ slot, bound * weight slot (word slot) := by
        apply Finset.prod_le_prod
        · intro slot _; exact Finset.sum_nonneg fun point _ => mul_nonneg ((output slot).nonneg point) (abs_nonneg _)
        · intro slot _
          by_cases hs : slot ∈ fixed
          · simp only [hs, if_true, FiniteDist.expectation_const, weight]
            have hl : |matrix slot (word slot) (values slot)| ≤
                (input slot).weight (word slot) + |matrix slot (word slot) (values slot)| :=
              le_add_of_nonneg_left ((input slot).nonneg _)
            exact hl.trans (le_mul_of_one_le_left (add_nonneg ((input slot).nonneg _) (abs_nonneg _)) hbound)
          · simpa only [hs, if_false, weight] using hcolumn slot (word slot)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hrows (slot) (value) : (∑ point, |matrix slot point value|) ≤ bound := by
    linarith [hrow slot value]
  calc
    _ ≤ (FiniteDist.independent output).expectation (fun integrated =>
        bound ^ Fintype.card Slot * ∑ word, (∏ slot, |matrix slot (word slot) (freeze fixed values integrated slot)|) * kernel word ^ 2) := by
      exact Finset.sum_le_sum fun integrated _ => mul_le_mul_of_nonneg_left
        (matrixApply_square_le matrix bound hrows kernel _) ((FiniteDist.independent output).nonneg integrated)
    _ = bound ^ Fintype.card Slot * ∑ word,
        (FiniteDist.independent output).expectation (fun integrated =>
          ∏ slot, |matrix slot (word slot) (freeze fixed values integrated slot)|) * kernel word ^ 2 := by
      rw [FiniteDist.expectation_const_mul, FiniteDist.expectation_sum]
      simp only [FiniteDist.expectation_mul_const]
    _ ≤ bound ^ Fintype.card Slot * ∑ word,
        (bound ^ Fintype.card Slot * ∏ slot, weight slot (word slot)) * kernel word ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_trans zero_le_one hbound) _)
      exact Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_right (hpoint word) (sq_nonneg _)
    _ = bound ^ Fintype.card Slot * (bound ^ Fintype.card Slot *
        ∑ word, (∏ slot, weight slot (word slot)) * kernel word ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ bound ^ Fintype.card Slot * (bound ^ Fintype.card Slot *
        (bound ^ Fintype.card Slot * fiberNorm input kernel fixed ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy
        (pow_nonneg (le_trans zero_le_one hbound) _)) (pow_nonneg (le_trans zero_le_one hbound) _)
    _ ≤ (bound ^ Fintype.card Slot)^4 * fiberNorm input kernel fixed ^ 2 := by
      have hh : 1 ≤ bound ^ Fintype.card Slot := one_le_pow₀ hbound
      have hprod : (bound ^ Fintype.card Slot)^3 ≤ (bound ^ Fintype.card Slot)^4 := pow_le_pow_right₀ hh (by omega)
      exact (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)).trans_eq' (by ring)
    _ = _ := by rw [pow_mul]; ring

/-- Every fixed set is retained, with a uniform constant. -/
theorem matrixApply_fiberNorm_le (input : Slot → FiniteDist Input)
    (output : Slot → FiniteDist Output) (matrix : Slot → Input → Output → ℝ)
    (bound : ℝ) (hbound : 1 ≤ bound)
    (hrow : ∀ slot value, 1 + (∑ point, |matrix slot point value|) ≤ bound)
    (hcolumn : ∀ slot point, (output slot).expectation (fun value => |matrix slot point value|) ≤
      bound * (input slot).weight point)
    (kernel : (Slot → Input) → ℝ) (fixed : Finset Slot) :
    fiberNorm output (matrixApply matrix kernel) fixed ≤
      bound ^ (2 * Fintype.card Slot) * fiberNorm input kernel fixed :=
  fiberNorm_le_square_bound output _ fixed _
    (mul_nonneg (pow_nonneg (le_trans zero_le_one hbound) _) (fiberNorm_nonneg _ _ _))
    (matrixApply_fiberSq_le input output matrix bound hbound hrow hcolumn kernel fixed)

/-- Signed tensor channels with both Schur bounds preserve the full
literal activity, including all fixed coordinates. -/
theorem matrixApply_activity_le (input : Slot → FiniteDist Input)
    (output : Slot → FiniteDist Output) (matrix : Slot → Input → Output → ℝ)
    (bound : ℝ) (hbound : 1 ≤ bound)
    (hrow : ∀ slot value, 1 + (∑ point, |matrix slot point value|) ≤ bound)
    (hcolumn : ∀ slot point, (output slot).expectation (fun value => |matrix slot point value|) ≤
      bound * (input slot).weight point)
    (rates : Slot → ℝ) (hrates : ∀ slot, 0 ≤ rates slot) (kernel : (Slot → Input) → ℝ) :
    activity rates output (matrixApply matrix kernel) ≤
      bound ^ (2 * Fintype.card Slot) * activity rates input kernel := by
  unfold activity
  calc
    _ ≤ (∏ slot, rates slot) * ∑ fixed : Finset Slot, (∏ slot ∈ fixed, rates slot) *
        (bound ^ (2 * Fintype.card Slot) * fiberNorm input kernel fixed) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun slot _ => hrates slot)
      apply Finset.sum_le_sum
      intro fixed _
      exact mul_le_mul_of_nonneg_left (matrixApply_fiberNorm_le input output matrix bound hbound hrow hcolumn kernel fixed)
        (Finset.prod_nonneg fun slot _ => hrates slot)
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro fixed _; ring
end
end AFT.MixedKernel

import AFT.TotalVariation
import Mathlib

/-!
# The integer beta identity in the calibrated reference

The beta mixture in V7, Lemma `accuracy-beta-reference`, is a genuine
integral identity, not an assumed closeness property.  The lemmas here prove
its integer-parameter integral from mathlib's Gamma/Beta integral.
-/
namespace AFT
namespace BetaReference

open MeasureTheory

/-- The elementary integer beta integral, with no analytic estimates assumed. -/
theorem integer_beta_integral (m n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  have hc : (∫ x : ℝ in (0 : ℝ)..1,
      (x : ℂ) ^ m * (1 - (x : ℂ)) ^ n) =
      (m.factorial : ℂ) * n.factorial / (m + n + 1).factorial := by
    have h := Complex.betaIntegral_eq_Gamma_mul_div
      ((m : ℂ) + 1) ((n : ℂ) + 1) (by simp; positivity) (by simp; positivity)
    simp only [Complex.betaIntegral, add_sub_cancel_right,
      Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial] at h
    convert h using 1
    congr 2
    rw [show (m : ℂ) + 1 + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hr : Complex.ofReal (∫ x : ℝ in (0 : ℝ)..1,
      x ^ m * (1 - x) ^ n) =
      ((m.factorial : ℝ) * n.factorial / (m + n + 1).factorial : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    simpa using hc
  exact Complex.ofReal_injective hr

/-- The affine substitution used in the inverse-beta identity. -/
theorem shifted_integer_beta_integral (m n : ℕ) (b : ℝ) :
    (∫ x : ℝ in b..1, (x - b) ^ m * (1 - x) ^ n) =
      (1 - b) ^ (m + n + 1) *
        ((m.factorial : ℝ) * n.factorial / (m + n + 1).factorial) := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (fun x : ℝ => (x - b) ^ m * (1 - x) ^ n)
    (a := 0) (b := 1) (1 - b) b
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at h
  rw [← h]
  have heq : (fun x : ℝ => ((1 - b) * x + b - b) ^ m *
      (1 - ((1 - b) * x + b)) ^ n) =
      fun x : ℝ => (1 - b) ^ (m + n) * (x ^ m * (1 - x) ^ n) := by
    funext x
    rw [add_sub_cancel_right, show 1 - ((1 - b) * x + b) =
      (1 - b) * (1 - x) by ring, mul_pow, mul_pow, pow_add]
    ring
  rw [heq]
  change (1 - b) * (∫ x : ℝ in (0 : ℝ)..1,
      (1 - b) ^ (m + n) * (x ^ m * (1 - x) ^ n)) = _
  rw [intervalIntegral.integral_const_mul ((1 - b) ^ (m + n))
    (fun x : ℝ => x ^ m * (1 - x) ^ n), integer_beta_integral]
  rw [pow_succ]
  ring

/-- The polynomial density of `Beta(K + 1, n + 1)` on `[0,1]`. -/
noncomputable def density (K n : ℕ) (x : ℝ) : ℝ :=
  ((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial) *
    x ^ K * (1 - x) ^ n

/-- Conditional boundary-count probability when the activation is `b / x`. -/
noncomputable def inverseBinomial (K k : ℕ) (b x : ℝ) : ℝ :=
  (K.choose k : ℝ) * (b / x) ^ k * (1 - b / x) ^ (K - k)

/-- The cancellation of inverse powers is valid at each nonzero parameter. -/
theorem inverseBinomial_mul_density (K n k : ℕ) (hk : k ≤ K)
    (b x : ℝ) (hx : x ≠ 0) :
    inverseBinomial K k b x * density K n x =
      ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
        (K.factorial * n.factorial) * b ^ k) *
      ((x - b) ^ (K - k) * (1 - x) ^ n) := by
  have hp : (b / x) ^ k * (1 - b / x) ^ (K - k) * x ^ K =
      b ^ k * (x - b) ^ (K - k) := by
    rw [show 1 - b / x = (x - b) / x by field_simp]
    rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add,
      Nat.add_sub_of_le hk, div_mul_cancel₀ _ (pow_ne_zero _ hx)]
  unfold inverseBinomial density
  calc
    _ = ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
        (K.factorial * n.factorial)) *
        ((b / x) ^ k * (1 - b / x) ^ (K - k) * x ^ K) *
        (1 - x) ^ n := by ring
    _ = _ := by rw [hp]; ring

/-- The exact inverse-beta/binomial identity of V7.  The target has
`N = K + n + 1` trials; `n + 1 = N - K` is the second beta parameter. -/
theorem inverse_beta_binomial_integral (K n k : ℕ) (hk : k ≤ K)
    (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫ x : ℝ in b..1, inverseBinomial K k b x * density K n x) =
      ((K + n + 1).choose k : ℝ) * b ^ k *
        (1 - b) ^ (K + n + 1 - k) := by
  have hi : (∫ x : ℝ in b..1, inverseBinomial K k b x * density K n x) =
      ∫ x : ℝ in b..1,
        ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
          (K.factorial * n.factorial) * b ^ k) *
        ((x - b) ^ (K - k) * (1 - x) ^ n) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hb1] at hx
    exact inverseBinomial_mul_density K n k hk b x (ne_of_gt (lt_of_lt_of_le hb hx.1))
  rw [hi, intervalIntegral.integral_const_mul
    ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
      (K.factorial * n.factorial) * b ^ k)
    (fun x : ℝ => (x - b) ^ (K - k) * (1 - x) ^ n),
    shifted_integer_beta_integral]
  have hsub : K - k + n + 1 = K + n + 1 - k := by omega
  rw [hsub, Nat.cast_choose ℝ hk, Nat.cast_choose ℝ (show k ≤ K + n + 1 by omega)]
  have hK : (K.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr K.factorial_ne_zero
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hKk : ((K - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (K - k).factorial_ne_zero
  have hNk : ((K + n + 1 - k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (K + n + 1 - k).factorial_ne_zero
  field_simp

/-- The beta density is normalized on the unit interval. -/
theorem density_integral_one (K n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, density K n x) = 1 := by
  have heq : density K n = fun x : ℝ =>
      (((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial)) *
      (x ^ K * (1 - x) ^ n) := by funext x; unfold density; ring
  rw [heq, intervalIntegral.integral_const_mul _ (fun x : ℝ => x ^ K * (1 - x) ^ n),
    integer_beta_integral]
  have hK : (K.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr K.factorial_ne_zero
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hN : ((K + n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (K + n + 1).factorial_ne_zero
  field_simp

/-- Polynomial form of one boundary-count contribution after a legal cutoff. -/
noncomputable def retainedCount (K n k : ℕ) (b c : ℝ) : ℝ :=
  ∫ x : ℝ in c..1,
    ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
      (K.factorial * n.factorial) * b ^ k) *
      ((x - b) ^ (K - k) * (1 - x) ^ n)

/-- The polynomial definition is exactly the probability-kernel integral. -/
theorem retainedCount_eq_integral (K n k : ℕ) (hk : k ≤ K)
    (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) (hc1 : c ≤ 1) :
    retainedCount K n k b c =
      ∫ x : ℝ in c..1, inverseBinomial K k b x * density K n x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hc1] at hx
  exact (inverseBinomial_mul_density K n k hk b x
    (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hb hbc) hx.1))).symm

/-- Cutting the beta parameter below `c` loses positive mass only: each retained
count probability is dominated by the target binomial count probability. -/
theorem retainedCount_bounds (K n k : ℕ) (hk : k ≤ K)
    (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) (hc1 : c ≤ 1) :
    0 ≤ retainedCount K n k b c ∧
    retainedCount K n k b c ≤
      ((K + n + 1).choose k : ℝ) * b ^ k * (1 - b) ^ (K + n + 1 - k) := by
  let f := fun x : ℝ =>
    ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
      (K.factorial * n.factorial) * b ^ k) *
      ((x - b) ^ (K - k) * (1 - x) ^ n)
  have hnonneg : ∀ x ∈ Set.Icc b 1, 0 ≤ f x := by
    intro x hx
    dsimp [f]
    exact mul_nonneg (mul_nonneg (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (pow_nonneg hb.le _))
      (mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.1) _)
        (pow_nonneg (sub_nonneg.mpr hx.2) _))
  constructor
  · exact intervalIntegral.integral_nonneg hc1
      (fun x hx => hnonneg x ⟨hbc.trans hx.1, hx.2⟩)
  · have hle : (∫ x : ℝ in c..1, f x) ≤ ∫ x : ℝ in b..1, f x := by
      apply intervalIntegral.integral_mono_interval hbc hc1 le_rfl
      · exact ae_restrict_of_forall_mem measurableSet_Ioc
          (fun x hx => hnonneg x ⟨hx.1.le, hx.2⟩)
      · exact (by fun_prop : Continuous f).intervalIntegrable _ _
    have heq : (∫ x : ℝ in b..1, f x) =
        ((K + n + 1).choose k : ℝ) * b ^ k * (1 - b) ^ (K + n + 1 - k) := by
      calc
        _ = ∫ x : ℝ in b..1, inverseBinomial K k b x * density K n x :=
          retainedCount_eq_integral K n k hk b b hb le_rfl (hbc.trans hc1)
        _ = _ := inverse_beta_binomial_integral K n k hk b hb (hbc.trans hc1)
    exact hle.trans_eq heq

/-- Normalizing a nonzero subprobability dominated pointwise by a probability
changes it by at most the deleted mass.  No reciprocal-survival loss is needed. -/
theorem normalized_dominated_tv {α : Type*} [Fintype α]
    (q : FiniteDist α) (w : α → ℝ) (a : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hdom : ∀ x, w x ≤ q.weight x)
    (hsum : ∑ x, w x = a) (ha : 0 < a) :
    ∃ p : FiniteDist α, (∀ x, p.weight x = w x / a) ∧
      FiniteDist.TVBound p q (1 - a) := by
  let p : FiniteDist α := {
    weight := fun x => w x / a
    nonneg := fun x => div_nonneg (hw x) ha.le
    sum_one := by rw [← Finset.sum_div, hsum, div_self ha.ne'] }
  refine ⟨p, fun _ => rfl, ?_⟩
  have ha1 : a ≤ 1 := by
    rw [← hsum, ← q.sum_one]
    exact Finset.sum_le_sum (fun x _ => hdom x)
  apply (FiniteDist.tvBound_iff_totalVariation_le p q (1 - a)).mpr
  calc
    FiniteDist.totalVariation p q ≤ ∑ x, (1 - a) * p.weight x := by
      apply Finset.sum_le_sum
      intro x _
      apply max_le
      · change w x / a - q.weight x ≤ (1 - a) * (w x / a)
        have heq : (1 - a) * (w x / a) = w x / a - w x := by
          field_simp
        rw [heq]
        linarith [hdom x]
      · exact mul_nonneg (sub_nonneg.mpr ha1) (p.nonneg x)
    _ = 1 - a := by rw [← Finset.mul_sum, p.sum_one, mul_one]

/-- The same exact deleted-mass bound holds for the complete histogram obtained
from the count by any common conditional uniform-label kernel. -/
theorem normalized_dominated_histogram_tv {α β : Type*} [Fintype α] [Fintype β]
    (q : FiniteDist α) (w : α → ℝ) (a : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hdom : ∀ x, w x ≤ q.weight x)
    (hsum : ∑ x, w x = a) (ha : 0 < a) (kernel : α → FiniteDist β) :
    ∃ p : FiniteDist α, (∀ x, p.weight x = w x / a) ∧
      FiniteDist.TVBound (p.mix kernel) (q.mix kernel) (1 - a) := by
  obtain ⟨p, hp, htv⟩ := normalized_dominated_tv q w a hw hdom hsum ha
  exact ⟨p, hp, htv.mix kernel⟩

/-- The ordinary finite binomial count law. -/
noncomputable def binomialCount (N : ℕ) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FiniteDist (Fin (N + 1)) where
  weight k := (N.choose k : ℝ) * b ^ (k : ℕ) * (1 - b) ^ (N - k)
  nonneg k := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb _))
    (pow_nonneg (sub_nonneg.mpr hb1) _)
  sum_one := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (N.choose k : ℝ) * b ^ k * (1 - b) ^ (N - k))]
    have h := add_pow b (1 - b) N
    simpa only [add_sub_cancel, one_pow, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- The retained law, with zeros in the counts that `K` activatable coordinates
cannot produce. -/
noncomputable def retainedWeights (K n : ℕ) (b c : ℝ)
    (k : Fin (K + n + 2)) : ℝ :=
  if (k : ℕ) ≤ K then retainedCount K n k b c else 0

/-- Actual inverse-beta retained count weights are dominated by the actual
`Binomial(K+n+1,b)` law, including all counts above `K`. -/
theorem retainedWeights_dominated (K n : ℕ) (b c : ℝ)
    (hb : 0 < b) (hbc : b ≤ c) (hc1 : c ≤ 1) :
    ∀ k, 0 ≤ retainedWeights K n b c k ∧
      retainedWeights K n b c k ≤
        (binomialCount (K + n + 1) b hb.le (hbc.trans hc1)).weight k := by
  intro k
  unfold retainedWeights
  split_ifs with hk
  · exact retainedCount_bounds K n k hk b c hb hbc hc1
  · exact ⟨le_rfl, (binomialCount (K + n + 1) b hb.le (hbc.trans hc1)).nonneg k⟩

/-- The concrete reference count mixture, and hence every common conditional
histogram kernel, has TV error at most its deleted beta mass. -/
theorem retained_histogram_tv {α : Type*} [Fintype α]
    (K n : ℕ) (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) (hc1 : c ≤ 1)
    (ha : 0 < ∑ k, retainedWeights K n b c k)
    (kernel : Fin (K + n + 2) → FiniteDist α) :
    ∃ p : FiniteDist (Fin (K + n + 2)),
      (∀ k, p.weight k = retainedWeights K n b c k /
        (∑ j, retainedWeights K n b c j)) ∧
      FiniteDist.TVBound (p.mix kernel)
        ((binomialCount (K + n + 1) b hb.le (hbc.trans hc1)).mix kernel)
        (1 - ∑ k, retainedWeights K n b c k) := by
  have h := retainedWeights_dominated K n b c hb hbc hc1
  exact normalized_dominated_histogram_tv _ _ _
    (fun k => (h k).1) (fun k => (h k).2) rfl ha kernel

/-- Conditional boundary-count probabilities sum to one. -/
theorem inverseBinomial_sum (K : ℕ) (b x : ℝ) :
    (∑ k ∈ Finset.range (K + 1), inverseBinomial K k b x) = 1 := by
  unfold inverseBinomial
  have h := add_pow (b / x) (1 - b / x) K
  simpa only [add_sub_cancel, one_pow, mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Summing the zero-extended retained weights uses exactly the `K+1` possible
boundary counts. -/
theorem retainedWeights_sum (K n : ℕ) (b c : ℝ) :
    (∑ k, retainedWeights K n b c k) =
      ∑ k ∈ Finset.range (K + 1), retainedCount K n k b c := by
  classical
  unfold retainedWeights
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    if k ≤ K then retainedCount K n k b c else 0)]
  calc
    _ = ∑ k ∈ Finset.range (K + 1),
        if k ≤ K then retainedCount K n k b c else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hkn
      simp only [Finset.mem_range] at hkn
      simp [show ¬ k ≤ K by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [show k ≤ K by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk]

/-- The survival mass is exactly the beta survival integral.  In particular,
the loss in `retained_histogram_tv` is the deleted beta lower tail. -/
theorem retainedWeights_mass (K n : ℕ) (b c : ℝ)
    (hb : 0 < b) (hbc : b ≤ c) (hc1 : c ≤ 1) :
    (∑ k, retainedWeights K n b c k) =
      ∫ x : ℝ in c..1, density K n x := by
  rw [retainedWeights_sum]
  unfold retainedCount
  rw [← intervalIntegral.integral_finset_sum]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc1] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hb hbc) hx.1)
    calc
      _ = ∑ k ∈ Finset.range (K + 1),
          inverseBinomial K k b x * density K n x := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (inverseBinomial_mul_density K n k
          (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk) b x hx0).symm
      _ = density K n x := by rw [← Finset.sum_mul, inverseBinomial_sum, one_mul]
  · intro k _
    exact (by fun_prop : Continuous (fun x : ℝ =>
      ((K.choose k : ℝ) * ((K + n + 1).factorial : ℝ) /
        (K.factorial * n.factorial) * b ^ k) *
        ((x - b) ^ (K - k) * (1 - x) ^ n))).intervalIntegrable _ _

/-- Positivity of the beta polynomial on the open unit interval. -/
theorem density_pos (K n : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 < density K n x := by
  unfold density
  exact mul_pos (mul_pos (div_pos
    (Nat.cast_pos.mpr (Nat.factorial_pos _))
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (Nat.cast_pos.mpr (Nat.factorial_pos _)))) (pow_pos hx _))
      (pow_pos (sub_pos.mpr hx1) _)

/-- The legal beta survival probability is nonzero whenever the cutoff is below one. -/
theorem beta_survival_pos (K n : ℕ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) :
    0 < ∫ x : ℝ in c..1, density K n x := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (by unfold density; exact (by fun_prop : Continuous _).intervalIntegrable _ _)
    (fun x hx => density_pos K n x (lt_of_le_of_lt hc hx.1) hx.2) hc1

/-- The complete inverse-beta reference conclusion with the exact lower-tail
error.  The common kernel may output the whole histogram, not just its boundary
count, and no continuity of a subsequent correction is assumed. -/
theorem inverse_beta_reference_tv {α : Type*} [Fintype α]
    (K n : ℕ) (b c : ℝ) (hb : 0 < b) (hbc : b ≤ c) (hc1 : c < 1)
    (kernel : Fin (K + n + 2) → FiniteDist α) :
    ∃ p : FiniteDist (Fin (K + n + 2)),
      (∀ k, p.weight k = retainedWeights K n b c k /
        (∫ x : ℝ in c..1, density K n x)) ∧
      FiniteDist.TVBound (p.mix kernel)
        ((binomialCount (K + n + 1) b hb.le (hbc.trans hc1.le)).mix kernel)
        (∫ x : ℝ in (0 : ℝ)..c, density K n x) := by
  have hm := retainedWeights_mass K n b c hb hbc hc1.le
  have ha : 0 < ∑ k, retainedWeights K n b c k := by
    rw [hm]
    exact beta_survival_pos K n c (hb.le.trans hbc) hc1
  obtain ⟨p, hp, htv⟩ := retained_histogram_tv K n b c hb hbc hc1.le ha kernel
  have hcont : Continuous (density K n) := by unfold density; fun_prop
  have hs : (∫ x : ℝ in (0 : ℝ)..c, density K n x) +
      (∫ x : ℝ in c..1, density K n x) = 1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), density_integral_one]
  refine ⟨p, ?_, ?_⟩
  · simpa only [hm] using hp
  · have he : 1 - ∑ k, retainedWeights K n b c k =
        ∫ x : ℝ in (0 : ℝ)..c, density K n x := by rw [hm]; linarith
    simpa only [he] using htv

end BetaReference
end AFT

import AFT.TwoPoolActivity
import AFT.CanonicalMomentBound

/-! # Palette-independent high moments with two unequal sample pools -/

set_option maxHeartbeats 800000

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

section Counting

variable {Copy PS BS PP BP : Type*}
  [Fintype Copy] [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]

theorem twoPool_noSingletonPatterns_card_le (primaryUsed bodyUsed : ℕ) :
    (Finset.univ.filter (fun pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP) =>
      (NoSingleton pattern.1 ∧ NoSingleton pattern.2) ∧
        ((usedLabels pattern.1).card, (usedLabels pattern.2).card) = (primaryUsed, bodyUsed))).card ≤
      ((Fintype.card PP).descFactorial primaryUsed *
        (Fintype.card Copy * Fintype.card PS) ^ (Fintype.card Copy * Fintype.card PS)) *
      ((Fintype.card BP).descFactorial bodyUsed *
        (Fintype.card Copy * Fintype.card BS) ^ (Fintype.card Copy * Fintype.card BS)) := by
  have heq : Finset.univ.filter (fun pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP) =>
      (NoSingleton pattern.1 ∧ NoSingleton pattern.2) ∧
        ((usedLabels pattern.1).card, (usedLabels pattern.2).card) = (primaryUsed, bodyUsed)) =
      (Finset.univ.filter (fun pattern : Copy → PS ↪ PP => NoSingleton pattern ∧ (usedLabels pattern).card = primaryUsed)).product
        (Finset.univ.filter (fun pattern : Copy → BS ↪ BP => NoSingleton pattern ∧ (usedLabels pattern).card = bodyUsed)) := by
    ext pattern
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.product_eq_sprod, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [heq, Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul (noSingletonPatterns_card_le primaryUsed) (noSingletonPatterns_card_le bodyUsed)

end Counting

variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]

/-- Complete two-pool canonical moment estimate. Both actual reference laws,
all arbitrary joint-kernel fibers, and the distinct falling-factorial
normalizers are retained. The constant depends only on the three fixed orders. -/
theorem twoPoolStatistic_moment_le_activity (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (power : ℕ) (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => twoPoolStatistic kernel word ^ power) ≤
      (momentConstant (Fintype.card PS) power * momentConstant (Fintype.card BS) power) *
        MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
          (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
          (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ power := by
  let lp := power * Fintype.card PS
  let lb := power * Fintype.card BS
  let activity := MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
    (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel
  let denominator : ℝ := (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
    ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power
  let survivors := Finset.univ.filter (fun pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP) =>
    NoSingleton pattern.1 ∧ NoSingleton pattern.2)
  let support (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) :=
    ((usedLabels pattern.1).card, (usedLabels pattern.2).card)
  let term (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) :=
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (patternProduct kernel (sumPattern pattern)) / denominator
  have ha : 0 ≤ activity := MixedKernel.activity_nonneg _ _ _ (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hden : 0 < denominator := by
    apply pow_pos
    apply mul_pos
    · exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : Fintype.card PS ≤ Fintype.card PP))
    · exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : Fintype.card BS ≤ Fintype.card BP))
  have hmaps (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) (_ : pattern ∈ survivors) :
      support pattern ∈ (Finset.range (lp + 1)).product (Finset.range (lb + 1)) := by
    have hp := usedLabels_card_le_occurrences pattern.1
    have hb := usedLabels_card_le_occurrences pattern.2
    simp only [Fintype.card_fin] at hp hb
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps term
  have hused (used : ℕ × ℕ) (hused : used ∈ (Finset.range (lp + 1)).product (Finset.range (lb + 1))) :
      (∑ pattern ∈ survivors.filter (fun pattern => support pattern = used), term pattern) ≤
        (2 : ℝ) ^ (power * (Fintype.card PS + Fintype.card BS)) *
          ((lp : ℝ) ^ lp * (lb : ℝ) ^ lb * activity ^ power) := by
    let selected := survivors.filter (fun pattern => support pattern = used)
    have hcount : (selected.card : ℝ) ≤
        (((Fintype.card PP).descFactorial used.1 : ℝ) * (lp : ℝ) ^ lp) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (lb : ℝ) ^ lb) := by
      have hh := twoPool_noSingletonPatterns_card_le (Copy := Fin power) (PS := PS) (BS := BS)
        (PP := PP) (BP := BP) used.1 used.2
      simp only [Fintype.card_fin] at hh
      have hh' : selected.card ≤
          ((Fintype.card PP).descFactorial used.1 * lp ^ lp) *
            ((Fintype.card BP).descFactorial used.2 * lb ^ lb) := by
        convert hh using 1
        congr 1
        ext pattern
        simp only [selected, survivors, support, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.eta]
      exact_mod_cast hh'
    have hterm (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) (hpattern : pattern ∈ selected) :
        term pattern ≤ (Fintype.card PP : ℝ) ^ (lp - used.1) *
          (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator := by
      have hm := Finset.mem_filter.mp hpattern
      have hs : NoSingleton pattern.1 ∧ NoSingleton pattern.2 := (Finset.mem_filter.mp hm.1).2
      have hh := twoPool_pattern_expectation_activity_le primary body kernel pattern hs hprimary hbody
      have heqP : (usedLabels pattern.1).card = used.1 := congrArg Prod.fst hm.2
      have heqB : (usedLabels pattern.2).card = used.2 := congrArg Prod.snd hm.2
      rw [heqP, heqB] at hh
      apply div_le_div_of_nonneg_right _ hden.le
      exact (le_abs_self _).trans hh
    calc
      _ ≤ (selected.card : ℝ) * ((Fintype.card PP : ℝ) ^ (lp - used.1) *
          (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul selected term _ hterm
      _ ≤ ((((Fintype.card PP).descFactorial used.1 : ℝ) * (lp : ℝ) ^ lp) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (lb : ℝ) ^ lb)) *
          ((Fintype.card PP : ℝ) ^ (lp - used.1) *
            (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = ((((Fintype.card PP).descFactorial used.1 : ℝ) * (Fintype.card PP : ℝ) ^ (lp - used.1) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (Fintype.card BP : ℝ) ^ (lb - used.2))) / denominator) *
          ((lp : ℝ) ^ lp * (lb : ℝ) ^ lb * activity ^ power) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (twoPool_collision_normalizer_bound (Fintype.card PP) (Fintype.card BP) (Fintype.card PS) (Fintype.card BS)
          power used.1 used.2 hprimary hbody hprimaryLarge hbodyLarge
          (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hused).1))
          (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hused).2))) (by positivity)
  rw [twoPoolStatistic_moment_surviving_expansion primary body kernel hcanonical power]
  change (∑ pattern ∈ survivors, _) / denominator ≤ _
  rw [Finset.sum_div]
  change (∑ pattern ∈ survivors, term pattern) ≤ _
  rw [← hgroup]
  apply (Finset.sum_le_sum hused).trans_eq
  simp only [Finset.sum_const, Finset.product_eq_sprod, Finset.card_product, Finset.card_range, nsmul_eq_mul, momentConstant]
  dsimp only [lp, lb, activity]
  rw [Nat.mul_add power (Fintype.card PS) (Fintype.card BS), pow_add]
  push_cast
  ring

/-- Every fixed even absolute moment has the same complete two-pool bound. -/
theorem twoPoolStatistic_even_moment_le_activity (primary body : FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (moment : ℕ) (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => |twoPoolStatistic kernel word| ^ (2 * moment)) ≤
      (momentConstant (Fintype.card PS) (2 * moment) * momentConstant (Fintype.card BS) (2 * moment)) *
        MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
          (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
          (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ (2 * moment) := by
  simpa only [pow_mul, sq_abs] using twoPoolStatistic_moment_le_activity
    primary body kernel hcanonical (2 * moment) hprimary hbody hprimaryLarge hbodyLarge

end

end AFT.CanonicalMoments

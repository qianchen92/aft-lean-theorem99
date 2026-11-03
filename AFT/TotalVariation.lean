import AFT.TransportBound
import AFT.PositiveRepair

/-! Exact finite total variation and contraction by a stochastic kernel. -/

namespace AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A bounded test cannot distinguish a zero-mass signed measure better than
its positive mass. -/
theorem signed_test_bound (weight test : α → ℝ)
    (hzero : signedMass weight = 0) (htest : ∀ a, 0 ≤ test a ∧ test a ≤ 1) :
    |∑ a, weight a * test a| ≤ positiveMass weight := by
  have hpoint (a : α) :
      -max (-weight a) 0 ≤ weight a * test a ∧
        weight a * test a ≤ max (weight a) 0 := by
    obtain ⟨ht0, ht1⟩ := htest a
    by_cases hw : 0 ≤ weight a
    · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
      constructor <;> nlinarith
    · have hw' : weight a ≤ 0 := le_of_not_ge hw
      rw [max_eq_right hw', max_eq_left (neg_nonneg.mpr hw')]
      constructor <;> nlinarith
  have hmass : positiveMass weight = negativeMass weight := by
    simpa [hzero] using positiveMass_eq weight
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => (hpoint a).1)
    rw [hmass]
    simpa only [Finset.sum_neg_distrib, negativeMass] using h
  · exact Finset.sum_le_sum (fun a _ => (hpoint a).2)

namespace FiniteDist

/-- Positive mass of the difference, equal to half the `L¹` distance. -/
noncomputable def totalVariation (p q : FiniteDist α) : ℝ :=
  positiveMass (fun a => p.weight a - q.weight a)

theorem signedMass_difference (p q : FiniteDist α) :
    signedMass (fun a => p.weight a - q.weight a) = 0 := by
  simp [signedMass, Finset.sum_sub_distrib, p.sum_one, q.sum_one]

/-- The eventwise definition used by V7 equals the positive-mass definition. -/
theorem tvBound_iff_totalVariation_le (p q : FiniteDist α) (error : ℝ) :
    TVBound p q error ↔ totalVariation p q ≤ error := by
  classical
  constructor
  · intro h
    let s := Finset.univ.filter (fun a => 0 ≤ p.weight a - q.weight a)
    have hevent : p.event s - q.event s = totalVariation p q := by
      simp only [event, s, Finset.sum_filter, ← Finset.sum_sub_distrib,
        totalVariation, positiveMass]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 ≤ p.weight a - q.weight a
      · simp [ha]
      · simp [ha, max_eq_right (le_of_not_ge ha)]
    have hn : 0 ≤ totalVariation p q :=
      Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have he := h s
    rwa [hevent, abs_of_nonneg hn] at he
  · intro h s
    have ht : ∀ a : α, 0 ≤ (if a ∈ s then (1 : ℝ) else 0) ∧
        (if a ∈ s then (1 : ℝ) else 0) ≤ 1 := by
      intro a
      split_ifs <;> norm_num
    have hb := signed_test_bound (fun a => p.weight a - q.weight a)
      (fun a => if a ∈ s then 1 else 0) (signedMass_difference p q) ht
    have he : (∑ a, (p.weight a - q.weight a) * (if a ∈ s then (1 : ℝ) else 0)) =
        p.event s - q.event s := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      simp [event, Finset.sum_sub_distrib]
    rw [he] at hb
    exact hb.trans h

/-- Conventional half-`L¹` formula, proved from the normalized weights. -/
theorem totalVariation_eq_half_l1 (p q : FiniteDist α) :
    totalVariation p q = (∑ a, |p.weight a - q.weight a|) / 2 := by
  let weight := fun a => p.weight a - q.weight a
  have hmass : positiveMass weight = negativeMass weight := by
    have hz : signedMass weight = 0 := signedMass_difference p q
    simpa only [hz, zero_add] using positiveMass_eq weight
  have habs (a : α) : |weight a| = max (weight a) 0 + max (-weight a) 0 := by
    by_cases ha : 0 ≤ weight a
    · simp [abs_of_nonneg ha, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    · have ha' : weight a ≤ 0 := le_of_not_ge ha
      simp [abs_of_nonpos ha', max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
  change positiveMass weight = (∑ a, |weight a|) / 2
  simp_rw [habs]
  rw [Finset.sum_add_distrib]
  change positiveMass weight = (positiveMass weight + negativeMass weight) / 2
  rw [← hmass]
  ring

theorem event_le_one (p : FiniteDist α) (s : Finset α) : p.event s ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => p.nonneg a)

theorem event_mix (p : FiniteDist α) (kernel : α → FiniteDist β) (s : Finset β) :
    (p.mix kernel).event s = ∑ a, p.weight a * (kernel a).event s := by
  simp only [event, mix_weight, Finset.mul_sum]
  exact Finset.sum_comm

/-- A stochastic channel contracts total variation, including the final
uniform random relabeling of a histogram and the physical output channel. -/
theorem TVBound.mix {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) (kernel : α → FiniteDist β) :
    TVBound (p.mix kernel) (q.mix kernel) error := by
  intro s
  rw [event_mix, event_mix, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hb := signed_test_bound (fun a => p.weight a - q.weight a)
    (fun a => (kernel a).event s) (signedMass_difference p q)
    (fun a => ⟨event_nonneg _ _, event_le_one _ _⟩)
  exact hb.trans ((tvBound_iff_totalVariation_le p q error).mp h)

/-- A stochastic kernel also contracts the `L¹` norm of an arbitrary signed
measure. This applies before clipping, where `TVBound.mix` alone would not. -/
theorem signed_kernel_l1_contraction (weight : α → ℝ) (kernel : α → FiniteDist β) :
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
      ∑ input, |weight input| := by
  calc
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
        ∑ output, ∑ input, |weight input| * (kernel input).weight output := by
      apply Finset.sum_le_sum
      intro output _
      have h := Finset.abs_sum_le_sum_abs
        (fun input => weight input * (kernel input).weight output) Finset.univ
      simpa only [abs_mul, abs_of_nonneg ((kernel _).nonneg _)] using h
    _ = ∑ input, |weight input| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_one, mul_one]

/-- V7's conditional positive-repair error survives any actual output
channel, including one with shared internal randomness. The kernel is already
normalized; there is no additional conditioning loss. -/
theorem positive_repair_kernel_l1_bound (weight : α → ℝ)
    (hmean : 0 < signedMass weight) (kernel : α → FiniteDist β) :
    (∑ output, |∑ input,
      (max (weight input) 0 / positiveMass weight - weight input / signedMass weight) *
        (kernel input).weight output|) ≤
      2 * negativeMass weight / signedMass weight := by
  exact (signed_kernel_l1_contraction _ kernel).trans_eq (positive_repair_l1 weight hmean)

end FiniteDist
end AFT

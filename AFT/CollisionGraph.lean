import AFT.GraphTransfer

/-! # The exact transfer chain of a finite joint-kernel collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label Color : Type*} [Fintype Label] [Fintype Color]

/-- Coordinate sets that remain active after each actual integration step. -/
noncomputable def graphActive (scope ending : ℕ → Finset Label) : ℕ → Finset Label
  | 0 => ∅
  | index + 1 => (scope index ∪ graphActive scope ending index) \ ending index

/-- Actual partially integrated product of the first kernel copies. -/
noncomputable def graphMessage (reference : Label → FiniteDist Color)
    (ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ) : ℕ → (Label → Color) → ℝ
  | 0 => fun _ => 1
  | index + 1 => refresh reference (ending index)
      (fun word => kernel index word * graphMessage reference ending kernel index word)

/-- Middle occurrences are the coordinates fixed by a graph step. -/
noncomputable def graphFixed (scope ending : ℕ → Finset Label) (index : ℕ) : Finset Label :=
  scope index \ ((scope index \ graphActive scope ending index) ∪ ending index)

/-- Every graph message depends only on its actual remaining active labels. -/
theorem graphMessage_dependsOn (reference : Label → FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, Hoeffding.DependsOn (scope index) (kernel index)) (count : ℕ) :
    Hoeffding.DependsOn (graphActive scope ending count) (graphMessage reference ending kernel count) := by
  induction count with
  | zero => intro first second _; rfl
  | succ index ih =>
    apply refresh_dependsOn
    intro first second hequal
    dsimp only
    rw [hkernel index first second (fun label hlabel => hequal label (Finset.mem_union_left _ hlabel)),
      ih first second (fun label hlabel => hequal label (Finset.mem_union_right _ hlabel))]

/-- The complete chain retains every actual mixed fiber, and introduces no
palette-dependent or state-space-dependent factor. -/
theorem graphMessage_energy_le (reference : Label → FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, Hoeffding.DependsOn (scope index) (kernel index)) (count : ℕ) :
    (FiniteDist.independent reference).l2Sq (graphMessage reference ending kernel count) ≤
      ∏ index ∈ Finset.range count, MixedKernel.fiberNorm reference (kernel index) (graphFixed scope ending index) ^ 2 := by
  induction count with
  | zero =>
    simp only [graphMessage, FiniteDist.l2Sq, FiniteDist.expectation, one_pow, mul_one,
      FiniteDist.sum_one, Finset.range_zero, Finset.prod_empty, le_refl]
  | succ index ih =>
    have h := graph_step_energy_le reference (graphActive scope ending index) (scope index) (ending index)
      (kernel index) (graphMessage reference ending kernel index) (hkernel index)
      (graphMessage_dependsOn reference scope ending kernel hkernel index)
    have hh := mul_le_mul_of_nonneg_left ih
      (sq_nonneg (MixedKernel.fiberNorm reference (kernel index) (graphFixed scope ending index)))
    apply h.trans
    rw [Finset.prod_range_succ]
    simpa only [graphFixed, mul_comm] using hh

/-- The exact unprocessed kernel product. -/
noncomputable def graphSuffix (kernel : ℕ → (Label → Color) → ℝ) (length start : ℕ)
    (word : Label → Color) : ℝ := ∏ index ∈ Finset.Ico start length, kernel index word

omit [Fintype Color] in
/-- Remaining scopes are disjoint from eliminated labels, so the unprocessed
product passes unchanged through that integration step. -/
theorem graphSuffix_fixed (scope ending : ℕ → Finset Label)
    (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, Hoeffding.DependsOn (scope index) (kernel index))
    (length index : ℕ) (hending : ∀ later, index < later → later < length →
      Disjoint (ending index) (scope later)) :
    Hoeffding.DependsOn (ending index)ᶜ (graphSuffix kernel length (index + 1)) := by
  intro first second hequal
  apply Finset.prod_congr rfl
  intro later hlater
  apply hkernel later
  intro label hlabel
  apply hequal label
  exact Finset.mem_compl.mpr (fun he =>
    Finset.disjoint_left.mp (hending later (by have := (Finset.mem_Ico.mp hlater).1; omega)
      (Finset.mem_Ico.mp hlater).2) he hlabel)

/-- Integrating the actual graph messages preserves the original full joint
product expectation exactly. -/
theorem graphMessage_expectation (reference : Label → FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, Hoeffding.DependsOn (scope index) (kernel index)) (length : ℕ)
    (hending : ∀ index later, index < later → later < length → Disjoint (ending index) (scope later)) :
    (FiniteDist.independent reference).expectation (graphMessage reference ending kernel length) =
      (FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) := by
  have hinvariant (count : ℕ) (hcount : count ≤ length) :
      (FiniteDist.independent reference).expectation (fun word => graphMessage reference ending kernel count word *
        graphSuffix kernel length count word) =
      (FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) := by
    induction count with
    | zero => simp only [graphMessage, graphSuffix, Nat.Ico_zero_eq_range, one_mul]
    | succ index ih =>
      have hi : index < length := by omega
      have hfixed := graphSuffix_fixed scope ending kernel hkernel length index (hending index)
      have heq (word : Label → Color) : graphMessage reference ending kernel (index + 1) word *
          graphSuffix kernel length (index + 1) word =
          refresh reference (ending index) (fun values => graphMessage reference ending kernel index values *
            graphSuffix kernel length index values) word := by
        rw [graphMessage, ← refresh_mul_fixed reference (ending index) _ _ hfixed]
        congr 1
        funext values
        unfold graphSuffix
        rw [Finset.prod_eq_prod_Ico_succ_bot hi]
        ring
      simp_rw [heq]
      rw [expectation_refresh]
      exact ih (by omega)
  simpa only [graphSuffix, Finset.Ico_self, Finset.prod_empty, mul_one] using hinvariant length le_rfl

/-- The genuine finite factor-graph contraction bound for arbitrary joint
kernels. Structural disjointness is the only graph premise. -/
theorem graph_product_expectation_sq_le (reference : Label → FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, Hoeffding.DependsOn (scope index) (kernel index)) (length : ℕ)
    (hending : ∀ index later, index < later → later < length → Disjoint (ending index) (scope later)) :
    (FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) ^ 2 ≤
      ∏ index ∈ Finset.range length, MixedKernel.fiberNorm reference (kernel index) (graphFixed scope ending index) ^ 2 := by
  rw [← graphMessage_expectation reference scope ending kernel hkernel length hending]
  have h := expectation_mul_sq_le (FiniteDist.independent reference)
    (graphMessage reference ending kernel length) (fun _ => 1)
  have hone : (FiniteDist.independent reference).l2Sq (fun _ => (1 : ℝ)) = 1 := by
    simp [FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.sum_one]
  simp only [mul_one, hone] at h
  exact h.trans (graphMessage_energy_le reference scope ending kernel hkernel length)

end AFT.CanonicalMoments

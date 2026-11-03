import AFT.ChargeMarginal

/-! # Charge transfer for a literal finite sum of local input terms -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Slot Index G : Type*} [Fintype Slot] [Fintype Index] [Fintype G] [AddCommGroup G]

/-- A power of a local sum retains at most `power * degree` actual centers.
The envelope is the absolute coefficient/supremum sum, not the number of terms. -/
theorem chargeWordLaw_local_sum_power_deviation (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required)
    (scope : Index → Finset Slot) (term : Index → (Slot → G) → ℝ)
    (hdepends : ∀ index, Hoeffding.DependsOn (scope index) (term index))
    (bound : Index → ℝ) (_hbound : ∀ index, 0 ≤ bound index)
    (hsup : ∀ index word, |term index word| ≤ bound index)
    (degree power : ℕ) (hdegree : ∀ index, (scope index).card ≤ degree)
    (error : ℝ) (herror : 0 ≤ error)
    (hratio : ∀ selected : Finset Slot, selected.card ≤ power * degree → ∀ partialCharge,
      |(center.sumLaw (Fintype.card Slot - selected.card)).weight (required - partialCharge) /
        (center.sumLaw (Fintype.card Slot)).weight required - 1| ≤ error) :
    |(chargeWordLaw center required hpos).expectation (fun word => (∑ index, term index word)^power) -
      (independent (fun _ : Slot => center)).expectation (fun word => (∑ index, term index word)^power)| ≤
      error * (∑ index, bound index)^power := by
  let scopeOf (pattern : Fin power → Index) := Finset.univ.biUnion (fun copy => scope (pattern copy))
  let productOf (pattern : Fin power → Index) (word : Slot → G) := ∏ copy, term (pattern copy) word
  have hscope (pattern : Fin power → Index) : (scopeOf pattern).card ≤ power * degree := by
    calc
      _ ≤ ∑ copy : Fin power, (scope (pattern copy)).card := Finset.card_biUnion_le
      _ ≤ ∑ _copy : Fin power, degree := Finset.sum_le_sum fun copy _ => hdegree (pattern copy)
      _ = _ := by simp
  have hprodDepends (pattern : Fin power → Index) : Hoeffding.DependsOn (scopeOf pattern) (productOf pattern) := by
    intro first second heq
    apply Finset.prod_congr rfl
    intro copy _
    apply hdepends (pattern copy)
    intro slot hs
    exact heq slot (Finset.mem_biUnion.mpr ⟨copy, Finset.mem_univ _, hs⟩)
  have hprodBound (pattern : Fin power → Index) (word : Slot → G) :
      |productOf pattern word| ≤ ∏ copy, bound (pattern copy) := by
    unfold productOf
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun copy _ => hsup (pattern copy) word)
  have hterm (pattern : Fin power → Index) :
      |(chargeWordLaw center required hpos).expectation (productOf pattern) -
        (independent (fun _ : Slot => center)).expectation (productOf pattern)| ≤
        error * ∏ copy, bound (pattern copy) := by
    apply (chargeWordLaw_local_deviation center required hpos (scopeOf pattern) (productOf pattern)
      (hprodDepends pattern) error (hratio _ (hscope pattern))).trans
    apply mul_le_mul_of_nonneg_left _ herror
    change (∑ word, (independent (fun _ : Slot => center)).weight word * |productOf pattern word|) ≤ _
    calc
      _ ≤ ∑ word, (independent (fun _ : Slot => center)).weight word * (∏ copy, bound (pattern copy)) :=
        Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left (hprodBound pattern word) ((independent _).nonneg _)
      _ = _ := by rw [← Finset.sum_mul, sum_one, one_mul]
  have hexpand (law : FiniteDist (Slot → G)) :
      law.expectation (fun word => (∑ index, term index word)^power) =
        ∑ pattern : Fin power → Index, law.expectation (productOf pattern) := by
    unfold expectation
    simp only [Fintype.sum_pow, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hexpand, hexpand, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun pattern _ => hterm pattern).trans_eq
  rw [← Finset.mul_sum, Fintype.sum_pow]

/-- In particular the even absolute moment needed by conditional positive
repair transfers with exactly the fixed-order polynomial envelope. -/
theorem chargeWordLaw_local_sum_even_moment_deviation (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required)
    (scope : Index → Finset Slot) (term : Index → (Slot → G) → ℝ)
    (hdepends : ∀ index, Hoeffding.DependsOn (scope index) (term index))
    (bound : Index → ℝ) (hbound : ∀ index, 0 ≤ bound index)
    (hsup : ∀ index word, |term index word| ≤ bound index)
    (degree moment : ℕ) (hdegree : ∀ index, (scope index).card ≤ degree)
    (error : ℝ) (herror : 0 ≤ error)
    (hratio : ∀ selected : Finset Slot, selected.card ≤ (2 * moment) * degree → ∀ partialCharge,
      |(center.sumLaw (Fintype.card Slot - selected.card)).weight (required - partialCharge) /
        (center.sumLaw (Fintype.card Slot)).weight required - 1| ≤ error) :
    |(chargeWordLaw center required hpos).expectation (fun word => |∑ index, term index word|^(2 * moment)) -
      (independent (fun _ : Slot => center)).expectation (fun word => |∑ index, term index word|^(2 * moment))| ≤
      error * (∑ index, bound index)^(2 * moment) := by
  simpa only [pow_mul, sq_abs] using chargeWordLaw_local_sum_power_deviation center required hpos
    scope term hdepends bound hbound hsup degree (2 * moment) hdegree error herror hratio

end
end AFT.FiniteDist

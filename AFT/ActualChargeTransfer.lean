import AFT.V7Charge
import AFT.ChargeMoment

/-! # The actual V7 charge proposal and local moment transfer -/

namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] actualModulusNeZero
local instance actualChargeTransferFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualChargeError (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) : ℝ :=
  4 * Parameters.modulus n * (actualBodyLaw C n beta).uniformDeviation ^ (Parameters.bodies n - cutoff)

theorem actualChargeError_nonneg (C : ℝ) (n : ℕ) (beta : ℝ) (cutoff : ℕ) :
    0 ≤ actualChargeError C n beta cutoff :=
  mul_nonneg (by positivity) (pow_nonneg (uniformDeviation_nonneg _) _)

theorem actual_charge_all_local_ratios_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) (cutoff : ℕ) :
    ∀ᶠ n in atTop, ∀ required : Fin (Parameters.modulus n),
      0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required ∧
      ∀ selected : Finset (Fin (Parameters.bodies n)), selected.card ≤ cutoff → ∀ partialCharge,
        |((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n - selected.card)).weight (required - partialCharge) /
          ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required - 1| ≤
            actualChargeError C n (beta n) cutoff := by
  have hall : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (cutoff + 1), ∀ required partialCharge : Fin (Parameters.modulus n),
      0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required ∧
      |((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n - k)).weight (required - partialCharge) /
        ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required - 1| ≤
        actualChargeError C n (beta n) k := by
    apply (Filter.eventually_all_finset (Finset.range (cutoff + 1))).mpr
    intro k _
    exact actual_charge_ratio_eventually C hC beta hbeta k
  filter_upwards [hall, actual_body_uniformDeviation_inv_parameter_eventually C hC beta hbeta,
    eventually_ge_atTop 2] with n hs hd hn required
  have hbase : (actualBodyLaw C n (beta n)).uniformDeviation ≤ 1 := by
    apply hd.trans
    exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).mpr (by exact_mod_cast (show 1 ≤ n by omega))
  refine ⟨(hs 0 (by simp) required 0).1, ?_⟩
  intro selected hk partialCharge
  apply (hs selected.card (Finset.mem_range.mpr (by omega)) required partialCharge).2.trans
  unfold actualChargeError
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_of_le_one (uniformDeviation_nonneg _) hbase (Nat.sub_le_sub_left hk _)

/-- All local terms use the same full safe-center charge proposal. The
input kernels may depend on arbitrary, overlapping sets of center labels. -/
theorem actual_charge_local_moment_transfer_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) (degree moment : ℕ) :
    ∀ᶠ n in atTop, ∀ required : Fin (Parameters.modulus n),
      ∃ hpos : 0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight required,
      ∀ (Index : Type) [Fintype Index],
      ∀ scope : Index → Finset (Fin (Parameters.bodies n)),
      ∀ term : Index → (Fin (Parameters.bodies n) → Fin (Parameters.modulus n)) → ℝ,
      (∀ index, Hoeffding.DependsOn (scope index) (term index)) →
      ∀ bound : Index → ℝ, (∀ index, 0 ≤ bound index) →
      (∀ index word, |term index word| ≤ bound index) →
      (∀ index, (scope index).card ≤ degree) →
      |(chargeWordLaw (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n (beta n)) required (by simpa using hpos)).expectation
          (fun word => |∑ index, term index word|^(2 * moment)) -
        (independent (fun _ : Fin (Parameters.bodies n) => actualBodyLaw C n (beta n))).expectation
          (fun word => |∑ index, term index word|^(2 * moment))| ≤
        actualChargeError C n (beta n) ((2 * moment) * degree) * (∑ index, bound index)^(2 * moment) := by
  filter_upwards [actual_charge_all_local_ratios_eventually C hC beta hbeta ((2 * moment) * degree)] with n hh required
  obtain ⟨hpos, hr⟩ := hh required
  refine ⟨hpos, ?_⟩
  intro Index _ scope term hdepends bound hb hsup hdegree
  apply chargeWordLaw_local_sum_even_moment_deviation (actualBodyLaw C n (beta n)) required _
    scope term hdepends bound hb hsup degree moment hdegree _ (actualChargeError_nonneg ..)
  simpa only [Fintype.card_fin] using hr

end
end AFT.V7Calibration

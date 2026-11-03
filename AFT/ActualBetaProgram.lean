import AFT.ActualFiniteBetaCharge
import AFT.BetaFiniteProgram

/-! # Exact fair-bit program identity for the actual beta reference -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualBetaProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The already proved actual finite reference law is literally the output
of the rational beta program fed by `n+n` independent fair bits. -/
theorem actualFiniteBetaHistogram_fair_bits (C : ℝ) (n : ℕ) :
    actualFiniteBetaHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualPositiveReferenceHistogram C n
          (safeFiniteDraw (Parameters.dimension n) (Parameters.legs n) n (n+n) word : ℝ)) := by
  unfold actualFiniteBetaHistogram actualFiniteBetaSource
  ext hist
  rw [finiteLaw_mix_weight]
  simp only [FiniteDist.mix_weight]
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- The zero-charge theorem uses exactly that same finite outer program. -/
theorem actualFiniteBetaZeroChargeHistogram_fair_bits (C : ℝ) (n : ℕ) :
    actualFiniteBetaZeroChargeHistogram C n=
      (FiniteDist.independent fun _ : Fin (n+n) => FiniteDist.uniform (Fin 2)).mix
        (fun word => actualReferenceZeroChargeHistogram C n
          (safeFiniteDraw (Parameters.dimension n) (Parameters.legs n) n (n+n) word : ℝ)) := by
  unfold actualFiniteBetaZeroChargeHistogram actualFiniteBetaSource
  ext hist
  rw [finiteLaw_mix_weight]
  simp only [FiniteDist.mix_weight]
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- All actual executions use exactly `n` CDF queries. The outer beta
program has no retry loop, even on non-typical tickets. -/
theorem actual_beta_program_queries (n : ℕ) (word : Fin (n+n) → Fin 2) :
    BinaryCDFSampler.locateQueries
      (finiteCut (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n (n+n))
      n 0 (FiniteTicketSampler.bitTicket (n+n) word).val=n :=
  finiteDraw_queries _ _ _ _ _

end
end AFT.V7Calibration

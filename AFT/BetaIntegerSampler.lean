import AFT.BetaIntegerArithmetic
import AFT.SafeBetaGridPoint

/-! # The actual beta sampler implemented with integer arithmetic only -/
namespace AFT.BinaryCDFSampler

theorem locate_congr_on (first second : ℕ → ℕ) (depth lower ticket : ℕ)
    (h : ∀ a,lower ≤ a → a ≤ lower+2^depth → first a=second a) :
    locate first depth lower ticket=locate second depth lower ticket := by
  induction depth generalizing lower with
  | zero => rfl
  | succ depth ih =>
    have hp : first (lower+2^depth)=second (lower+2^depth) := h _ (Nat.le_add_right lower _) (by rw [pow_succ]; omega)
    simp only [locate,hp]
    split_ifs
    · apply ih
      intro a hlo hhi
      exact h a hlo (by rw [pow_succ]; omega)
    · apply ih
      intro a hlo hhi
      exact h a (by omega) (by rw [pow_succ]; omega)

end AFT.BinaryCDFSampler

namespace AFT.BetaReference

/-- Only integer additions, products, powers, factorials, and divisions
are required by these cumulative queries. -/
def integerDraw (K n depth bits : ℕ) (word : Fin bits → Fin 2) : Fin (2^depth) :=
  BinaryCDFSampler.draw (integerCut K n depth bits) depth (2^bits) (FiniteTicketSampler.bitTicket bits word)

theorem integerDraw_eq_finiteDraw (K n depth bits : ℕ) (word : Fin bits → Fin 2) :
    integerDraw K n depth bits word=finiteDraw K n depth bits word := by
  apply Fin.ext
  apply BinaryCDFSampler.locate_congr_on
  intro a _ ha
  exact integerCut_eq_finiteCut K n depth bits a (by simpa only [zero_add] using ha)

def integerSafeDraw (N K depth bits : ℕ) (word : Fin bits → Fin 2) : ℚ :=
  safeGridValue N K (2^depth) (integerDraw K (N-K-1) depth bits word)

theorem integerSafeDraw_eq_safeFiniteDraw (N K depth bits : ℕ) (word : Fin bits → Fin 2) :
    integerSafeDraw N K depth bits word=safeFiniteDraw N K depth bits word := by
  unfold integerSafeDraw safeFiniteDraw
  rw [integerDraw_eq_finiteDraw]

/-- The replacement integer implementation has the same fixed query count. -/
theorem integerDraw_queries (K n depth bits : ℕ) (word : Fin bits → Fin 2) :
    BinaryCDFSampler.locateQueries (integerCut K n depth bits) depth 0
      (FiniteTicketSampler.bitTicket bits word).val=depth :=
  BinaryCDFSampler.locateQueries_eq _ _ _ _

end AFT.BetaReference

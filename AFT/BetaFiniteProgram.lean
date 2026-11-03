import AFT.SafeBetaGridPoint
import AFT.Histogram

namespace AFT.BetaReference
open scoped BigOperators Classical
noncomputable section

theorem finiteLaw_mix_weight {State : Type*} [Fintype State]
    (K n depth bits : ℕ) (kernel : Fin (2^depth) → FiniteDist State) (state : State) :
    ((finiteLaw K n depth bits).mix kernel).weight state=
      ∑ word : Fin bits → Fin 2,
        (FiniteDist.independent fun _ : Fin bits => FiniteDist.uniform (Fin 2)).weight word*
          (kernel (finiteDraw K n depth bits word)).weight state := by
  rw [finiteLaw,FiniteDist.mix_map]
  rfl

end
end AFT.BetaReference

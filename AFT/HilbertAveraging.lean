import AFT.MixedAveraging
import AFT.FiniteExpectationAlgebra

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source First Second : Type*} [Fintype Source] [Fintype First] [Fintype Second]

theorem l2Sq_prod_curried (first : FiniteDist First) (second : FiniteDist Second)
    (value : First → Second → ℝ) :
    (first.prod second).l2Sq (fun pair => value pair.1 pair.2) =
      first.expectation (fun left => second.l2Sq (value left)) := by
  exact expectation_prod first second (fun pair => value pair.1 pair.2^2)

theorem expectation_l2Sq_average_le_bound (source : FiniteDist Source)
    (first : FiniteDist First) (second : FiniteDist Second)
    (kernel : Source → First → Second → ℝ) (bound : ℝ)
    (hkernel : ∀ point,first.expectation (fun left => second.l2Sq (kernel point left)) ≤ bound) :
    first.expectation (fun left => second.l2Sq (fun right =>
      ∑ point,source.weight point*kernel point left right)) ≤ bound := by
  rw [← l2Sq_prod_curried]
  apply l2Sq_average_le_bound source (first.prod second) _ bound
  intro point
  rw [l2Sq_prod_curried]
  exact hkernel point

end
end AFT.FiniteDist

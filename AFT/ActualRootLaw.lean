import AFT.ActualNormalizedMean
import AFT.RootExchangeability

/-! # The actual normalized zero-sum root word law -/

namespace AFT.V7Calibration

open GaussianSource
open scoped Classical

noncomputable section

local instance actualRootLawFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Genuine conditioning of the independent protected Gaussian word on its
full integer sum being zero; positivity is proved by the zero word. -/
def actualRootConditionLaw (parameter : ℕ) : FiniteDist (actualRootWord parameter) :=
  RootSlice.law (fun _ : Fin (Parameters.bodies parameter) =>
    windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter)) (fun sample => (sample : ℤ)) 0
      (window_root_probability_positive (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter))

/-- Every real root coordinate has the declared calibrated root marginal. -/
theorem actualRootConditionLaw_coordinate (parameter : ℕ) (index : Fin (Parameters.bodies parameter)) :
    (actualRootConditionLaw parameter).map (fun word => word index) =
      rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter) :=
  root_joint_coordinate_map _ _ _ _ _

end

end AFT.V7Calibration

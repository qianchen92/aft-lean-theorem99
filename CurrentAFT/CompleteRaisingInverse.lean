import CurrentAFT.CompleteRaising

/-! # The explicit finite inverse of the genuine two-role raising operator -/
namespace CurrentAFT.CompleteRaisingInverse

open AFT DiffuseProfiles ProposalPrimary ActualControls GradedControlAlgebra GradedInverse
  LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem pow_vanishes (security order : ℕ) (horder : 1 ≤ order) (power : ℕ) (family : Family security order) :
    VanishesBelow (primaryLaw security) (bodyReference security) order power
      (((CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) ^ power) family) := by
  induction power with
  | zero => exact vanishesBelow_zero _ _ order _
  | succ power ih =>
    rw [pow_succ']
    change VanishesBelow _ _ order (power + 1)
      (CompleteRaising.raisingLinear security order horder
        (((CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) ^ power) family))
    exact CompleteRaising.raisingLinear_raises security order horder power _ ih

theorem nilpotent (security order : ℕ) (horder : 1 ≤ order) :
    (CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
  apply LinearMap.ext
  intro family
  funext arity
  exact pow_vanishes security order horder (order + 1) family arity (by have := arity.property; omega)

def response (security order : ℕ) (horder : 1 ≤ order) : Module.End ℝ (Family security order) :=
  1 + CompleteRaising.raisingLinear security order horder

def inverse (security order : ℕ) (horder : 1 ≤ order) : Module.End ℝ (Family security order) :=
  ∑ power ∈ Finset.range (order + 1), (-CompleteRaising.raisingLinear security order horder) ^ power

theorem inverse_mul (security order : ℕ) (horder : 1 ≤ order) :
    inverse security order horder * response security order horder = 1 := by
  have hnil : (-CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
    simpa only [nilpotent security order horder, mul_zero] using
      (neg_pow (CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) (order + 1))
  have h := geom_sum_mul_neg (-CompleteRaising.raisingLinear security order horder) (order + 1)
  simpa only [inverse, response, sub_neg_eq_add, hnil, sub_zero] using h

theorem mul_inverse (security order : ℕ) (horder : 1 ≤ order) :
    response security order horder * inverse security order horder = 1 := by
  have hnil : (-CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) ^ (order + 1) = 0 := by
    simpa only [nilpotent security order horder, mul_zero] using
      (neg_pow (CompleteRaising.raisingLinear security order horder : Module.End ℝ (Family security order)) (order + 1))
  have h := mul_neg_geom_sum (-CompleteRaising.raisingLinear security order horder) (order + 1)
  simpa only [inverse, response, sub_neg_eq_add, hnil, sub_zero] using h

theorem inverse_response (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    inverse security order horder (response security order horder family) = family :=
  congrArg (fun channel : Module.End ℝ (Family security order) => channel family) (inverse_mul security order horder)

theorem response_inverse (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    response security order horder (inverse security order horder family) = family :=
  congrArg (fun channel : Module.End ℝ (Family security order) => channel family) (mul_inverse security order horder)

end
end CurrentAFT.CompleteRaisingInverse

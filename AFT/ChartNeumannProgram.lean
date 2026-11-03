import AFT.ChartProjectionProgram

/-! # Error of the finite rational chart inverse against the actual Neumann solve -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Chart : Type*} [Fintype Chart]

/-- The cached finite iteration converges to the very inverse used by the
positive chart construction, with the concrete quarter-contraction rate. -/
theorem chart_neumann_iteration_error (D : (Chart → ℝ) →L[ℝ] (Chart → ℝ))
    (hD : ‖D‖<1) (hquarter : ‖D‖≤1/4) (rhs : Chart → ℝ) (steps : ℕ) :
    ‖realLinearIteration (-D.toLinearMap) rhs steps-neumannSolve D hD rhs‖≤
      (1/4 : ℝ)^steps*((4/3)*‖rhs‖) := by
  have hsolution := neumannSolve_equation D hD rhs
  induction steps with
  | zero =>
    simpa only [realLinearIteration,zero_sub,norm_neg,pow_zero,one_mul] using
      neumannSolve_norm D hD hquarter rhs
  | succ steps ih =>
    have hid : realLinearIteration (-D.toLinearMap) rhs (steps+1)-neumannSolve D hD rhs=
        D (realLinearIteration (-D.toLinearMap) rhs steps-neumannSolve D hD rhs) := by
      simp only [realLinearIteration,LinearMap.neg_apply,sub_neg_eq_add,map_sub]
      change rhs+D (realLinearIteration (-D.toLinearMap) rhs steps)-neumannSolve D hD rhs=_
      conv_lhs => lhs; lhs; rw [←hsolution]
      abel
    rw [hid]
    apply (D.le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_right hquarter (norm_nonneg _)).trans
    have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤1/4)
    exact hh.trans_eq (by rw [pow_succ];ring)

variable (charts colors features : ℕ) [NeZero charts]

theorem chartNeumannProgram_error
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts))
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖≤1/4)
    (rhs : Fin charts → ℚ) (steps : ℕ) (output : Fin charts) :
    |((chartNeumannProgram charts colors features feature allowed safe rhs steps).get output : ℝ)-
      neumannSolve (deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)) hD
        (fun x => (rhs x : ℝ)) output|≤(1/4 : ℝ)^steps*((4/3)*‖fun x => (rhs x : ℝ)‖) := by
  have hh := chart_neumann_iteration_error _ hD hquarter (fun x => (rhs x : ℝ)) steps
  rw [←chartNeumannProgram_cast charts colors features feature allowed safe rhs steps] at hh
  exact (norm_le_pi_norm ((fun x => ((chartNeumannProgram charts colors features feature allowed safe rhs steps).get x : ℝ))-
    neumannSolve _ hD (fun x => (rhs x : ℝ))) output).trans hh

end
end AFT.BoundaryCalibration

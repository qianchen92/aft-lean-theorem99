import AFT.ActualRootGaussianTickets
import AFT.ConditionRejection
import AFT.FiniteRefresh

/-! # Polynomially capped rejection for the actual computed zero-sum root source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteDist Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootTicketRejectionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actual_root_ticket_acceptance_eventually :
    ∀ᶠ n : ℕ in atTop,
      1/(n : ℝ)^32 ≤ RootSlice.sumProbability (actualRootTicketLaw n n)
        (fun point => (point : ℤ)) (Parameters.bodies n) 0 := by
  have hs := actualRootNumericalError_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlarge : ∀ᶠ n : ℕ in atTop,16*Real.exp 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (16*Real.exp 2))
  filter_upwards [v7_rootProbability_order,hs,hlarge,eventually_ge_atTop 2] with n hp hs hl hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : (Parameters.bodies n : ℝ) ≤ 2*(n : ℝ)^60 := by
    exact_mod_cast (show Parameters.bodies n ≤ 2*n^60 from
      (Nat.sub_le _ _).trans (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2))
  have herror := (RootSlice.sumProbability_l1_error (actualRootTicketLaw n n)
    (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun point => (point : ℤ))
    (Parameters.bodies n) 0).trans
    (mul_le_mul_of_nonneg_left (actualRootTicketLaw_l1 n n (by omega)) (Nat.cast_nonneg _))
  have hnum : (Parameters.bodies n : ℝ)*(1/(2 : ℝ)^n) ≤ 1/(16*Real.exp 2*(n : ℝ)^31) := by
    have hratio : (Parameters.bodies n : ℝ)*(1/(2 : ℝ)^n)*(16*Real.exp 2*(n : ℝ)^31) ≤
        actualRootNumericalError n := by
      calc
        _ ≤ (2*(n : ℝ)^60)*(1/(2 : ℝ)^n)*(16*Real.exp 2*(n : ℝ)^31) := by gcongr
        _ ≤ actualRootNumericalError n := by
          unfold actualRootNumericalError
          rw [show (n : ℝ)^91=(n : ℝ)^60*(n : ℝ)^31 by rw [← pow_add]]
          convert (mul_le_mul_of_nonneg_right (show (32 : ℝ) ≤ 64 by norm_num)
            (show 0 ≤ Real.exp 2*(n : ℝ)^60*(n : ℝ)^31/(2 : ℝ)^n by positivity)) using 1 <;> ring
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 16*Real.exp 2*(n : ℝ)^31)).mpr (hratio.trans hs.le)
  have happrox : 1/(16*Real.exp 2*(n : ℝ)^31) ≤ RootSlice.sumProbability (actualRootTicketLaw n n)
      (fun point => (point : ℤ)) (Parameters.bodies n) 0 := by
    have hh := (abs_le.mp (herror.trans hnum)).1
    have heq : 1/(8*Real.exp 2*(n : ℝ)^31)=2*(1/(16*Real.exp 2*(n : ℝ)^31)) := by ring
    rw [heq] at hp
    have htrue : 2*(1/(16*Real.exp 2*(n : ℝ)^31)) ≤
        RootSlice.sumProbability (windowGaussian (v7RootWidth n) (v7RootCutoff n))
          (fun point => (point : ℤ)) (Parameters.bodies n) 0 := hp.1
    linarith
  apply le_trans _ happrox
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16*Real.exp 2*(n : ℝ)^31)
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hl (pow_nonneg hn0.le 31)]

def actualCappedRootTicketLaw (n : ℕ) : FiniteDist (Fin (Parameters.bodies n) → Window (v7RootCutoff n)) :=
  cappedCondition (independent (fun _ : Fin (Parameters.bodies n) => actualRootTicketLaw n n))
    (fun word => RootSlice.integerSum (fun point : Window (v7RootCutoff n) => (point : ℤ)) word=0)
    (CanonicalMoments.pointLaw (fun _ => windowZero (v7RootCutoff n))) (n^33)

def actualRootProgramError (n : ℕ) : ℝ := Real.exp (-(n : ℝ))+actualRootNumericalError n

theorem actualRootProgramError_negligible : Negligible actualRootProgramError := by
  have he : Negligible (fun n : ℕ => Real.exp (-(n : ℝ))) := by
    simpa only [pow_zero,Real.rpow_one,one_mul,neg_mul] using
      negligible_polynomial_stretched_exponential 1 0 1 1 (by norm_num) (by norm_num) (by norm_num)
  exact he.add actualRootNumericalError_negligible

/-- The retry budget is the literal power `n^33`. Both numerical error and
exhaustion error are negligible against the actual complete root law. -/
theorem actual_capped_root_ticket_eventually :
    ∀ᶠ n : ℕ in atTop,
      TVBound (actualCappedRootTicketLaw n)
        (RootSlice.law (fun _ : Fin (Parameters.bodies n) => windowGaussian (v7RootWidth n) (v7RootCutoff n))
          (fun point => (point : ℤ)) 0 (window_root_probability_positive _ _ _))
        (actualRootProgramError n) := by
  filter_upwards [actual_root_ticket_acceptance_eventually,actual_root_ticket_conditioning_eventually,
    eventually_ge_atTop 1] with n ha hc hn
  obtain ⟨hpos,hclose⟩ := hc
  have hh := cappedCondition_tv (independent (fun _ : Fin (Parameters.bodies n) => actualRootTicketLaw n n))
    (fun word => RootSlice.integerSum (fun point : Window (v7RootCutoff n) => (point : ℤ)) word=0) hpos
    (CanonicalMoments.pointLaw (fun _ => windowZero (v7RootCutoff n))) (n^33)
  have hnorm : TVBound (actualCappedRootTicketLaw n)
      (RootSlice.law (fun _ : Fin (Parameters.bodies n) => actualRootTicketLaw n n)
        (fun point => (point : ℤ)) 0 hpos) (Real.exp (-(n : ℝ))) := by
    apply hh.mono
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ n^33 by positivity)
    have heq : (n : ℝ)^33*(1/(n : ℝ)^32)=(n : ℝ) := by rw [pow_succ]; field_simp
    rw [heq] at hm
    push_cast
    change -(n : ℝ)^33*RootSlice.sumProbability (actualRootTicketLaw n n)
      (fun point => (point : ℤ)) (Parameters.bodies n) 0 ≤ -(n : ℝ)
    linarith
  intro event
  exact (abs_sub_le _ _ _).trans (add_le_add (hnorm event) (hclose event))

end
end AFT.V7Calibration

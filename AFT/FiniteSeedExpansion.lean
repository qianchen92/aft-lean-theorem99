import AFT.PositiveSeedSum
import AFT.RepresentedCanonical

/-! # Finite expansion that acts only on the original input labels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {State Seed Branch : Type*}

/-- A step retains its original seed in the linear branch; only the list of
pending original coordinates changes there. Nonlinear branches carry their
own remaining original coordinates. -/
def seedExpansion (base : State → Seed) (linear : State → State)
    (branches : State → Finset Branch) (higher : State → Branch → State) :
    ℕ → State → Table Seed
  | 0, state => MvPolynomial.X (base state)
  | steps+1, state => seedExpansion base linear branches higher steps (linear state) +
      ∑ branch ∈ branches state, seedExpansion base linear branches higher steps (higher state branch)

theorem seedExpansion_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (base : State → Seed) (linear : State → State) (branches : State → Finset Branch)
    (higher : State → Branch → State) (good : State → Prop)
    (hlinear : ∀ state, good state → good (linear state) ∧ base (linear state)=base state)
    (hhigher : ∀ state, good state → ∀ branch ∈ branches state, good (higher state branch))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hstep : ∀ state, good state →
      (∑ branch ∈ branches state, weight (base (higher state branch))) ≤ delta*weight (base state))
    (steps : ℕ) (state : State) (hstate : good state) :
    activity weight (seedExpansion base linear branches higher steps state) ≤
      (1+delta)^steps*weight (base state) := by
  induction steps generalizing state with
  | zero => simp [seedExpansion]
  | succ steps ih =>
    rw [seedExpansion]
    apply (activity_add_le weight hweight _ _).trans
    have hsum : activity weight (∑ branch ∈ branches state,
        seedExpansion base linear branches higher steps (higher state branch)) ≤
        (1+delta)^steps*(delta*weight (base state)) := by
      apply (activity_sum_le weight hweight _ _).trans
      calc
        _ ≤ ∑ branch ∈ branches state, (1+delta)^steps*weight (base (higher state branch)) :=
          Finset.sum_le_sum fun branch hb => ih _ (hhigher state hstate branch hb)
        _ = (1+delta)^steps*(∑ branch ∈ branches state,weight (base (higher state branch))) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hstep state hstate) (pow_nonneg (by positivity) _)
    have hlin := ih (linear state) (hlinear state hstate).1
    rw [(hlinear state hstate).2] at hlin
    exact (add_le_add hlin hsum).trans_eq (by rw [pow_succ]; ring)

/-- The identity branch is literally the original variable, so the error
loses one factor of the true one-coordinate smallness. -/
theorem seedExpansion_error_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (base : State → Seed) (linear : State → State) (branches : State → Finset Branch)
    (higher : State → Branch → State) (good : State → Prop)
    (hlinear : ∀ state, good state → good (linear state) ∧ base (linear state)=base state)
    (hhigher : ∀ state, good state → ∀ branch ∈ branches state, good (higher state branch))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hstep : ∀ state, good state →
      (∑ branch ∈ branches state, weight (base (higher state branch))) ≤ delta*weight (base state))
    (steps : ℕ) (state : State) (hstate : good state) :
    activity weight (seedExpansion base linear branches higher steps state-MvPolynomial.X (base state)) ≤
      ((1+delta)^steps-1)*weight (base state) := by
  induction steps generalizing state with
  | zero => simp [seedExpansion]
  | succ steps ih =>
    rw [seedExpansion,add_sub_right_comm]
    apply (activity_add_le weight hweight _ _).trans
    have hsum : activity weight (∑ branch ∈ branches state,
        seedExpansion base linear branches higher steps (higher state branch)) ≤
        (1+delta)^steps*(delta*weight (base state)) := by
      apply (activity_sum_le weight hweight _ _).trans
      calc
        _ ≤ ∑ branch ∈ branches state, (1+delta)^steps*weight (base (higher state branch)) := by
          apply Finset.sum_le_sum
          intro branch hb
          exact seedExpansion_activity weight hweight base linear branches higher good hlinear hhigher
            delta hdelta hstep steps _ (hhigher state hstate branch hb)
        _ = (1+delta)^steps*(∑ branch ∈ branches state,weight (base (higher state branch))) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hstep state hstate) (pow_nonneg (by positivity) _)
    have hlin := ih (linear state) (hlinear state hstate).1
    rw [(hlinear state hstate).2] at hlin
    exact (add_le_add hlin hsum).trans_eq (by rw [pow_succ]; ring)

theorem seedExpansion_canonical {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (base : State → InputSeed Color)
    (linear : State → State) (branches : State → Finset Branch)
    (higher : State → Branch → State) (good : State → Prop)
    (hbase : ∀ state, good state → Hoeffding.Canonical (inputReference primary body (base state))
      Finset.univ (base state).kernel)
    (hlinear : ∀ state,good state → good (linear state))
    (hhigher : ∀ state,good state → ∀ branch ∈ branches state,good (higher state branch))
    (steps : ℕ) (state : State) (hstate : good state) :
    InputTableCanonical primary body (seedExpansion base linear branches higher steps state) := by
  induction steps generalizing state with
  | zero => exact InputTableCanonical.X _ (hbase state hstate)
  | succ steps ih =>
    apply InputTableCanonical.add (ih _ (hlinear state hstate))
    apply InputTableCanonical.sum
    intro branch hb
    exact ih _ (hhigher state hstate branch hb)

end
end AFT.RepresentedPolynomial

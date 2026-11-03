import AFT.IndependentGlobalBudget
import AFT.MixedMonomialSeed
import AFT.RepresentedLinearActivity

/-! # A literal finite independent-response operator on input tables -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentUpperOperatorFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Extending by zero off the canonical cutoff domain defines a bounded map
on the entire formal algebra. No actual canonical cutoff input is removed. -/
def independentUpperColumn (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (cutoff depth : ℕ) (powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  if weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff ∧
    (∀ seed ∈ powers.support,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed) Finset.univ seed.kernel) then
    truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
      (independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth-
        MvPolynomial.X (mixedMonomialSeed powers)) else 0

def independentUpperLinear (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (cutoff depth : ℕ) : Module.End ℝ (Table (InputSeed (Fin (Parameters.modulus n)))) :=
  Finsupp.linearCombination ℝ (independentUpperColumn C n beta operator charts cutoff depth)

/-- The original monomial remains in `Id`; only the actual joint quotient
minus its own leading seed is put into the upper operator. -/
theorem independentUpperLinear_monomial (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (cutoff depth : ℕ) (powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ) (scalar : ℝ)
    (horder : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff)
    (hcanonical : ∀ seed ∈ powers.support,Hoeffding.Canonical
      (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) seed) Finset.univ seed.kernel) :
    independentUpperLinear C n beta operator charts cutoff depth (MvPolynomial.monomial powers scalar)=
      scalar • truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
        (independentGlobalQuotient C n beta operator charts (mixedMonomialSeed powers) depth-
          MvPolynomial.X (mixedMonomialSeed powers)) := by
  change Finsupp.linearCombination ℝ (independentUpperColumn C n beta operator charts cutoff depth)
    (Finsupp.single powers scalar)=_
  rw [Finsupp.linearCombination_single]
  simp only [independentUpperColumn,if_pos (And.intro horder hcanonical)]

/-- The operator estimate holds on every formal table, so its finite Neumann
powers can be bounded without supplying a new analytic hypothesis. -/
theorem independentUpperLinear_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ) (cutoff : ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second=
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ bodyPool radius : ℝ,0 ≤ radius → ∀ depth : ℕ,
    ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
    let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
    activity weight (independentUpperLinear C n (beta n) operator charts cutoff depth table) ≤
      independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ)*activity weight table := by
  filter_upwards [independentGlobalUpper_activity_eventually C hC beta pool cutoff htypical]
    with n hi operator hop charts hcharts bodyPool radius hradius depth table
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have ha := activationConstant_pos C hC
  have hb : 0 ≤ independentGlobalUpperConstant C cutoff/(n : ℝ)^(5/2 : ℝ) := by
    unfold independentGlobalUpperConstant independentGlobalBudgetConstant independentJointHigherConstant
      independentReferenceHilbertConstant independentPositiveInputConstant independentBodyInputConstant
    positivity
  apply activity_linearCombination_le weight weight hw
  intro powers
  unfold independentUpperColumn
  split_ifs with hp
  · apply (activity_truncate_le weight hw _ _ _).trans
    apply (hi operator hop charts hcharts bodyPool radius hradius (mixedMonomialSeed powers)
      (mixedMonomialSeed_canonical _ _ powers hp.2) (by rw [mixedMonomialSeed_order]; exact hp.1) depth).trans
    exact mul_le_mul_of_nonneg_left (mixedMonomialSeed_weight_le _ _ _ _ _ hradius powers) hb
  · rw [activity_zero]
    exact mul_nonneg hb (monomialWeight_nonneg weight hw powers)

theorem independentUpperLinear_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ cutoff depth : ℕ,∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentUpperLinear C n (beta n) operator charts cutoff depth table) := by
  filter_upwards [independentGlobalQuotient_canonical_eventually C hC beta hbeta]
    with n hi operator hop charts cutoff depth table
  change InputTableCanonical _ _ (∑ powers ∈ table.support,
    MvPolynomial.coeff powers table • independentUpperColumn C n (beta n) operator charts cutoff depth powers)
  apply InputTableCanonical.sum
  intro powers _
  dsimp only
  rw [MvPolynomial.smul_eq_C_mul]
  apply InputTableCanonical.mul (InputTableCanonical.C _)
  unfold independentUpperColumn
  split_ifs with hp
  · have hc := mixedMonomialSeed_canonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) powers hp.2
    exact ((hi operator hop charts (mixedMonomialSeed powers) hc depth).sub
      (InputTableCanonical.X _ hc)).truncate _ _
  · exact InputTableCanonical.zero

end
end AFT.V7Calibration

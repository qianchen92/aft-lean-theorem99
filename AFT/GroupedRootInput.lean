import AFT.GroupedRootTensor
import AFT.RootBodyInput
import AFT.PairedRootCost

/-! # Actual calibrated inputs for grouped joint root channels -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance groupedRootInputFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance groupedRootInputSigmaDecEq {Index : Type*} (Slots : Index → Type*) :
    DecidableEq (Sigma Slots) := Classical.decEq _
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
variable (Slots : Index → Type*) [∀ index,Fintype (Slots index)]

/-- One literal calibrated seed for all emitted groups. The input root
coefficient remains joint across all active source coordinates. -/
def actualGroupedRootInput (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (matrix : (index : Index) → Window (v7RootCutoff n) → (Slots index → Fin (Parameters.modulus n)) → ℝ)
    (kernel : (Index → Window (v7RootCutoff n)) → ℝ) : InputSeed (Fin (Parameters.modulus n)) :=
  inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
    (primaryFiniteSeed (RootTensor.groupedDensity Slots (fun _ => bodyRootReference n) matrix kernel))

theorem actualGroupedRootInput_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0)
    (matrix : (index : Index) → Window (v7RootCutoff n) → (Slots index → Fin (Parameters.modulus n)) → ℝ)
    (kernel : (Index → Window (v7RootCutoff n)) → ℝ) :
    actualLeadingOutput C n beta (MvPolynomial.X (actualGroupedRootInput Slots C n beta operator matrix kernel)) =
      ∑ word : Sigma Slots → Fin (Parameters.modulus n),
        MvPolynomial.C (RootTensor.groupedDensity Slots (fun _ => bodyRootReference n) matrix kernel word*
          ∏ slot,(actualPrimaryLaw C n beta).weight (word slot))*∏ slot,MvPolynomial.X (word slot) := by
  exact (actualLeadingOutput_inverse_joint_primary C n beta operator hop hrho hp
    (primaryFiniteSeed (RootTensor.groupedDensity Slots (fun _ => bodyRootReference n) matrix kernel)) rfl).trans
      (primaryFiniteSeed_form _ _)

/-- The actual primary lower bound turns one joint Hilbert estimate into
all mixed fibers, followed by the same actual inverse at every new output. -/
theorem actual_grouped_root_input_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ (Index : Type) [Fintype Index] [DecidableEq Index],
    ∀ (Slots : Index → Type) [∀ index,Fintype (Slots index)],
    ∀ matrix : (index : Index) → Window (v7RootCutoff n) → (Slots index → Fin (Parameters.modulus n)) → ℝ,
    ∀ bound : Index → ℝ,(∀ index,0 ≤ bound index) →
    (∀ index,(FiniteDist.independent (fun _ : Slots index => actualPrimaryLaw C n (beta n))).expectation
      (fun word => (bodyRootReference n).l2Sq (fun root => matrix index root word)) ≤ bound index^2) →
    ∀ kernel : (Index → Window (v7RootCutoff n)) → ℝ,∀ bodyPool radius : ℝ,0 ≤ radius →
      inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
        (actualGroupedRootInput Slots C n (beta n) operator matrix kernel) ≤
      pairedOutputCoordinateCost C n (pool n)^Fintype.card (Sigma Slots)*
        (∏ index,bound index)*Real.sqrt ((FiniteDist.independent (fun _ : Index => bodyRootReference n)).l2Sq kernel) := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n hi hp hn operator hop Index _ _ Slots _ matrix bound hb hlocal kernel bodyPool radius hradius
  obtain ⟨inverse,hinverse,hi⟩ := hi
  have heq : operator=inverse := LinearEquiv.toLinearMap_injective (hop.trans hinverse.symm)
  subst inverse
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  have hlow : 0<(1 : ℝ)/(4*Parameters.modulus n) := by positivity
  have hlower (slot : Sigma Slots) (color) : 1/(4*(Parameters.modulus n : ℝ)) ≤
      (actualPrimaryLaw C n (beta n)).weight color := hp color
  have hh := RootTensor.groupedDensity_activity_le Slots (fun _ => bodyRootReference n)
    (fun _ : Sigma Slots => actualPrimaryLaw C n (beta n)) matrix bound hb hlocal
    (1/(4*(Parameters.modulus n : ℝ))) ((Real.sqrt (pool n : ℝ))⁻¹) hlow (by positivity) hlower kernel
  have hsqrt : Real.sqrt ((1 : ℝ)/(4*Parameters.modulus n)) = (2*Real.sqrt (Parameters.modulus n : ℝ))⁻¹ := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_mul (by norm_num),show Real.sqrt (4 : ℝ)=2 by norm_num]
    rw [one_div]
  have hseed := hi (actualBodyLaw C n (beta n)) bodyPool radius hradius
    (primaryFiniteSeed (RootTensor.groupedDensity Slots (fun _ => bodyRootReference n) matrix kernel))
  apply hseed.trans
  unfold responseInputWeight
  rw [primaryFiniteSeed_weight]
  change (4/v7Activation C n)^Fintype.card (Sigma Slots)*MixedKernel.activity _ _ _ ≤ _
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg (div_nonneg (by norm_num) hrho.le) _)).trans_eq
  rw [hsqrt,div_inv_eq_mul]
  simp only [pairedOutputCoordinateCost,one_div]
  rw [← mul_assoc,← mul_assoc,← mul_pow]
  congr 2
  ring

/-- Actual canonicality is preserved by the grouped channel and calibrated
inverse, independently of the size and dependence of its joint root input. -/
theorem actual_grouped_root_input_canonical_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ (Index : Type) [Fintype Index] [DecidableEq Index],
    ∀ (Slots : Index → Type) [∀ index,Fintype (Slots index)],
    ∀ matrix : (index : Index) → Window (v7RootCutoff n) → (Slots index → Fin (Parameters.modulus n)) → ℝ,
    (∀ index root,Hoeffding.Canonical (fun _ : Slots index => actualPrimaryLaw C n (beta n)) Finset.univ
      (matrix index root)) →
    ∀ kernel : (Index → Window (v7RootCutoff n)) → ℝ,
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualGroupedRootInput Slots C n (beta n) operator matrix kernel)) Finset.univ
        (actualGroupedRootInput Slots C n (beta n) operator matrix kernel).kernel := by
  filter_upwards [actual_primary_seed_canonical_eventually C hC beta hbeta]
    with n hc operator hop Index _ _ Slots _ matrix hcanonical kernel
  exact hc operator hop _ _ (primaryFiniteSeed_canonical _ _ _
    (RootTensor.groupedDensity_canonical Slots (fun _ => bodyRootReference n) _ matrix hcanonical kernel))

end
end AFT.V7Calibration

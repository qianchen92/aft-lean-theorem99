import AFT.RootBodyTensor
import AFT.RootSubsetNorm

/-! # Literal calibrated inputs for the actual joint body-root channels -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootBodyInputFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootBodyInputSubtypeDecEq {α : Type*} (selected : Finset α) : DecidableEq selected := Classical.decEq _
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

def actualRootBodyJointInput (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (offset : Slot → ℤ) (kernel : (Slot → Window (v7RootCutoff n)) → ℝ) :
    InputSeed (Fin (Parameters.modulus n)) :=
  inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
    (primaryFiniteSeed (actualRootBodyJointDensity C n beta offset kernel))

/-- Evaluation gives exactly the emitted joint density polynomial. -/
theorem actualRootBodyJointInput_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0)
    (offset : Slot → ℤ) (kernel : (Slot → Window (v7RootCutoff n)) → ℝ) :
    actualLeadingOutput C n beta (MvPolynomial.X (actualRootBodyJointInput C n beta operator offset kernel)) =
      ∑ word : Slot → Fin (Parameters.modulus n),
        MvPolynomial.C (actualRootBodyJointDensity C n beta offset kernel word*
          ∏ slot,(actualPrimaryLaw C n beta).weight (word slot))*∏ slot,MvPolynomial.X (word slot) := by
  have hh := actualLeadingOutput_inverse_joint_primary C n beta operator hop hrho hp
    (primaryFiniteSeed (actualRootBodyJointDensity C n beta offset kernel)) rfl
  exact hh.trans (primaryFiniteSeed_form _ _)

/-- This is an actual input seed, with the same calibrated inverse used
in every coordinate and the exact full mixed activity. -/
theorem actual_root_body_joint_input_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot], ∀ offset : Slot → ℤ,
    (∀ slot (root : Window (v7RootCutoff n)),|(root : ℤ)+offset slot| ≤ maxBodyShift C n) →
    ∀ kernel : (Slot → Window (v7RootCutoff n)) → ℝ, ∀ bodyPool radius : ℝ,0 ≤ radius →
      inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
        (actualRootBodyJointInput C n (beta n) operator offset kernel) ≤
        (∏ slot,(4/v7Activation C n)*(Real.sqrt (pool n : ℝ))⁻¹*
          (rootBodyFullCost n (offset slot)+(Real.sqrt (pool n : ℝ))⁻¹*rootBodyRowCost n (offset slot)))*
            Real.sqrt ((FiniteDist.independent (fun _ : Slot => bodyRootReference n)).l2Sq kernel) ∧
      Hoeffding.Canonical (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualRootBodyJointInput C n (beta n) operator offset kernel)) Finset.univ
        (actualRootBodyJointInput C n (beta n) operator offset kernel).kernel := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_root_body_joint_activity_eventually C hC beta hbeta,
    actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_primary_seed_canonical_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n h hi hc hn operator hop Slot _ _ offset hoff kernel bodyPool radius hradius
  obtain ⟨inverse,hinverse,hi⟩ := hi
  have heq : operator=inverse := LinearEquiv.toLinearMap_injective (hop.trans hinverse.symm)
  subst inverse
  have hh := h Slot offset hoff (fun _ => (Real.sqrt (pool n : ℝ))⁻¹) (fun _ => by positivity) kernel
  have hseed := hi (actualBodyLaw C n (beta n)) bodyPool radius hradius
    (primaryFiniteSeed (actualRootBodyJointDensity C n (beta n) offset kernel))
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  refine ⟨?_,hc operator hop _ _ (primaryFiniteSeed_canonical _ _ _ hh.2)⟩
  apply hseed.trans
  unfold responseInputWeight
  rw [primaryFiniteSeed_weight]
  change (4/v7Activation C n)^Fintype.card Slot*MixedKernel.activity _ _ _ ≤ _
  apply (mul_le_mul_of_nonneg_left hh.1 (pow_nonneg (div_nonneg (by norm_num) hrho.le) _)).trans_eq
  have hprod : (4/v7Activation C n)^Fintype.card Slot = ∏ _ : Slot,4/v7Activation C n := by rw [Finset.prod_const,Finset.card_univ]
  rw [← mul_assoc,hprod,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  ring

/-- The subset root coefficient is the literal canonical component of the
actual conditioned root law, retaining precisely its selected arguments. -/
def actualRootSubsetKernel (n : ℕ) (selected : Finset (Fin (Parameters.bodies n))) :
    (selected → Window (v7RootCutoff n)) → ℝ :=
  LocalTensors.restrictedComponent (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
    (actualRootConditionLaw n).weight selected

theorem actualRootSubsetKernel_l2Sq (n : ℕ) (selected : Finset (Fin (Parameters.bodies n))) :
    (FiniteDist.independent (fun _ : selected => bodyRootReference n)).l2Sq (actualRootSubsetKernel n selected) =
      v7RootKernelSq selected.card n := by
  have he := LocalTensors.localTensor_energy_eq (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
    (actualRootConditionLaw n).weight selected
  rw [LocalTensors.localTensor,LocalTensors.whitenedTensor_energy] at he
  apply Eq.trans ?_ (he.trans (actualRootResponseCoefficient_l2Sq n selected))
  unfold actualRootSubsetKernel FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro roots _
  rfl

/-- Each actual subset energy can now be used in the concrete mixed-input
bound, rather than replacing the joint coefficient by a rank-one expansion. -/
theorem actual_root_body_subset_input_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n)
    (order : ℕ) (horder : 0<order) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ selected : Finset (Fin (Parameters.bodies n)),selected.card=order →
    ∀ offset : selected → ℤ,
    (∀ slot (root : Window (v7RootCutoff n)),|(root : ℤ)+offset slot| ≤ maxBodyShift C n) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
      inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
        (actualRootBodyJointInput C n (beta n) operator offset (actualRootSubsetKernel n selected)) ≤
        (∏ slot : selected,(4/v7Activation C n)*(Real.sqrt (pool n : ℝ))⁻¹*
          (rootBodyFullCost n (offset slot)+(Real.sqrt (pool n : ℝ))⁻¹*rootBodyRowCost n (offset slot)))*
            Real.sqrt (rootANOVAConstant order/(Parameters.bodies n : ℝ)^(2*((order+1)/2))) := by
  filter_upwards [actual_root_body_joint_input_eventually C hC beta pool htypical,
    v7RootKernelSq_decay order horder,eventually_ge_atTop 1]
    with n h hb hn operator hop selected hselected offset hoff bodyPool radius hradius
  have hh := (h operator hop selected offset hoff (actualRootSubsetKernel n selected) bodyPool radius hradius).1
  rw [actualRootSubsetKernel_l2Sq,hselected] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb)
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)
  exact Finset.prod_nonneg fun slot _ => mul_nonneg
    (mul_nonneg (div_nonneg (by norm_num) hrho.le) (by positivity))
    (add_nonneg (rootBodyFullCost_nonneg n _) (mul_nonneg (by positivity) (rootBodyRowCost_nonneg n _)))

end
end AFT.V7Calibration

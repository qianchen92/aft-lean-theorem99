import AFT.RootTensorActivity
import AFT.OrdinaryBodyVarianceParameters
import AFT.PrimaryFiniteSeed
import AFT.JointSeedOutput

/-! # Actual ordinary and translated body/root tensor inputs -/
namespace AFT.RootTensor
open scoped BigOperators Classical
noncomputable section
variable {Source Color : Type*} [Fintype Source] [Fintype Color]

theorem profile_density_full_energy (source : FiniteDist Source) (reference : FiniteDist Color)
    (hp : ∀ color,reference.weight color ≠ 0) (family : Source → Color → ℝ) :
    reference.expectation (fun color => source.l2Sq (fun root => family root color/reference.weight color)) =
      source.expectation (fun root => profileSquareNorm reference.weight (family root)) := by
  unfold FiniteDist.l2Sq FiniteDist.expectation profileSquareNorm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro color _
  field_simp [hp color]

end
end AFT.RootTensor

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootBodyTensorFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def rootBodyFullCost (n : ℕ) (offset : ℤ) : ℝ :=
  if offset=0 then Real.sqrt (ordinaryRootEnergyConstant/(n : ℝ)^(289/4 : ℝ))
    else Real.sqrt (175104/(n : ℝ)^38)

def rootBodyRowCost (n : ℕ) (offset : ℤ) : ℝ :=
  if offset=0 then Real.sqrt (ordinaryRootRowConstant/(n : ℝ)^(137/4 : ℝ)) else 16

def rootBodyDensityMatrix (C : ℝ) (n : ℕ) (beta : ℝ) (offset : ℤ)
    (root : Window (v7RootCutoff n)) (color : Fin (Parameters.modulus n)) : ℝ :=
  centeredRootBodyProfile C n beta offset root color/(actualPrimaryLaw C n beta).weight color

theorem rootBodyFullCost_nonneg (n : ℕ) (offset : ℤ) : 0 ≤ rootBodyFullCost n offset := by
  unfold rootBodyFullCost
  split_ifs <;> exact Real.sqrt_nonneg _

theorem rootBodyRowCost_nonneg (n : ℕ) (offset : ℤ) : 0 ≤ rootBodyRowCost n offset := by
  unfold rootBodyRowCost
  split_ifs
  · exact Real.sqrt_nonneg _
  · norm_num

/-- The genuine centered translated-body density has the sharp ordinary
variance at offset zero, and the uniform strip variance otherwise. -/
theorem actual_root_body_density_variance_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ offset : ℤ,
    (∀ root : Window (v7RootCutoff n),|(root : ℤ)+offset| ≤ maxBodyShift C n) →
      (actualPrimaryLaw C n (beta n)).expectation (fun color =>
        (bodyRootReference n).l2Sq (fun root => rootBodyDensityMatrix C n (beta n) offset root color)) ≤
          rootBodyFullCost n offset ^ 2 ∧
      (∀ color,(bodyRootReference n).l2Sq (fun root => rootBodyDensityMatrix C n (beta n) offset root color) ≤
          rootBodyRowCost n offset ^ 2) ∧
      (∀ root,(actualPrimaryLaw C n (beta n)).expectation
        (rootBodyDensityMatrix C n (beta n) offset root)=0) := by
  filter_upwards [actual_root_body_variance_power_eventually C hC beta hbeta,
    actual_ordinary_root_profile_eventually C hC beta hbeta,
    actual_centered_root_body_strip_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta]
    with n hv he hs hp offset hoff
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hp0 (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity) (hp color))
  have hfull := RootTensor.profile_density_full_energy (bodyRootReference n)
    (actualPrimaryLaw C n (beta n)) hp0 (centeredRootBodyProfile C n (beta n) offset)
  have hmass (root) : (actualPrimaryLaw C n (beta n)).expectation
      (rootBodyDensityMatrix C n (beta n) offset root)=0 := by
    unfold FiniteDist.expectation rootBodyDensityMatrix
    simp_rw [mul_div_cancel₀ _ (hp0 _)]
    exact centeredRootBodyProfile_mass C n (beta n) offset root
  refine ⟨?_,?_,hmass⟩
  · change (actualPrimaryLaw C n (beta n)).expectation (fun color =>
      (bodyRootReference n).l2Sq (fun root => centeredRootBodyProfile C n (beta n) offset root color /
        (actualPrimaryLaw C n (beta n)).weight color)) ≤ _
    rw [hfull]
    by_cases hz : offset=0
    · subst offset
      rw [rootBodyFullCost,if_pos rfl,Real.sq_sqrt (show 0 ≤ ordinaryRootEnergyConstant/(n : ℝ)^(289/4 : ℝ) by
        unfold ordinaryRootEnergyConstant ordinaryRootDeltaConstant; positivity)]
      simp_rw [he]
      unfold FiniteDist.expectation
      rw [← rootBodyVariance_profile_energy]
      exact hv.2
    · rw [rootBodyFullCost,if_neg hz,Real.sq_sqrt (by positivity)]
      calc
        _ ≤ (bodyRootReference n).expectation (fun _ => 175104/(n : ℝ)^38) :=
          Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left (hs offset hoff root).1 (FiniteDist.nonneg _ _)
        _ = _ := FiniteDist.expectation_const _ _
  · intro color
    by_cases hz : offset=0
    · subst offset
      rw [rootBodyRowCost,if_pos rfl,Real.sq_sqrt (by
        unfold ordinaryRootRowConstant ordinaryRootDeltaConstant; positivity)]
      change (∑ root,(bodyRootReference n).weight root*
        (centeredRootBodyProfile C n (beta n) 0 root color/(actualPrimaryLaw C n (beta n)).weight color)^2) ≤ _
      simp_rw [he]
      have heq : (∑ root,(bodyRootReference n).weight root*
        (rootCenteredShift n root (actualBodyCenter C n (beta n)) color/(actualPrimaryLaw C n (beta n)).weight color)^2) =
          rootBodyVariance n (actualBodyCenter C n (beta n)) color/(actualPrimaryLaw C n (beta n)).weight color^2 := by
        simp only [rootBodyVariance,Finset.sum_div,div_pow,mul_div_assoc]
      rw [heq]
      exact hv.1 color
    · rw [rootBodyRowCost,if_neg hz]
      calc
        _ ≤ (bodyRootReference n).expectation (fun _ => (16 : ℝ)^2) := by
          unfold FiniteDist.l2Sq FiniteDist.expectation rootBodyDensityMatrix
          apply Finset.sum_le_sum
          intro root _
          apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr ((hs offset hoff root).2 color)
        _ = _ := FiniteDist.expectation_const _ _

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

def actualRootBodyJointDensity (C : ℝ) (n : ℕ) (beta : ℝ) (offset : Slot → ℤ)
    (kernel : (Slot → Window (v7RootCutoff n)) → ℝ) : (Slot → Fin (Parameters.modulus n)) → ℝ :=
  RootTensor.density (fun _ : Slot => bodyRootReference n) (fun slot => rootBodyDensityMatrix C n beta (offset slot)) kernel

/-- Arbitrary joint root inputs now satisfy the full mixed activity bound,
with the correct distinct local costs for every ordinary or shifted body. -/
theorem actual_root_body_joint_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ offset : Slot → ℤ,
    (∀ slot (root : Window (v7RootCutoff n)),|(root : ℤ)+offset slot| ≤ maxBodyShift C n) →
    ∀ rate : Slot → ℝ,(∀ slot,0 ≤ rate slot) →
    ∀ kernel : (Slot → Window (v7RootCutoff n)) → ℝ,
      MixedKernel.activity rate (fun _ : Slot => actualPrimaryLaw C n (beta n))
        (actualRootBodyJointDensity C n (beta n) offset kernel) ≤
        (∏ slot,rate slot*(rootBodyFullCost n (offset slot)+rate slot*rootBodyRowCost n (offset slot)))*
          Real.sqrt ((FiniteDist.independent (fun _ : Slot => bodyRootReference n)).l2Sq kernel) ∧
      Hoeffding.Canonical (fun _ : Slot => actualPrimaryLaw C n (beta n)) Finset.univ
        (actualRootBodyJointDensity C n (beta n) offset kernel) := by
  filter_upwards [actual_root_body_density_variance_eventually C hC beta hbeta]
    with n h Slot _ _ offset hoff rate hrate kernel
  exact ⟨RootTensor.density_activity_le _ _ _ rate _ _ hrate
      (fun slot => rootBodyFullCost_nonneg n (offset slot)) (fun slot => rootBodyRowCost_nonneg n (offset slot))
      (fun slot => (h (offset slot) (hoff slot)).1) (fun slot => (h (offset slot) (hoff slot)).2.1) kernel,
    RootTensor.density_canonical _ _ _ (fun slot => (h (offset slot) (hoff slot)).2.2) kernel⟩

end
end AFT.V7Calibration

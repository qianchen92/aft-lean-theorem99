import AFT.BodyShiftComposition

/-! # The literal mean input for the true shared-source attached body -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed Target Sample : Type*} [Fintype Sample]

theorem map_queueAverage (hom : Table Seed →ₐ[ℝ] Table Target) (law : FiniteDist Sample)
    (tables : Sample → Table Seed) :
    hom (queueAverage law tables) = queueAverage law (fun sample => hom (tables sample)) := by
  unfold queueAverage
  simp only [map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro sample _
  congr 1
  exact hom.commutes (law.weight sample)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

def attachedMeanTable (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  queueAverage (windowGaussian (10*n) (legCutoff C n-1))
    (fun sample => bodyMeanTable C n beta ((sample : ℤ)+queue))

theorem attachedMeanTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (attachedMeanTable C n beta queue) :=
  queueAverage_hasOrder _ _ _ _ (fun _ => bodyMeanTable_hasOrder C n beta _)

theorem attached_mean_shift_bound (C : ℝ) (n : ℕ) (queue : ℤ) (hq : |queue| ≤ queueCutoff n)
    (sample : Window (legCutoff C n-1)) : |(sample : ℤ)+queue| ≤ maxBodyShift C n := by
  have hs := abs_le.mpr (Finset.mem_Icc.mp sample.property)
  have hh := abs_add_le (sample : ℤ) queue
  unfold maxBodyShift
  omega

theorem localBodyMixture_source_average (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (output : Fin (Parameters.modulus n)) :
    localBodyMixture C n beta queue output =
      ∑ sample, (windowGaussian (10*n) (legCutoff C n-1)).weight sample*
        attachedBodyAtSource C n beta queue sample output := by
  simp_rw [← inactiveLegSource_mixture C n]
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [localBodyMixture,averagedInactiveBody,Finset.mul_sum,windowZero]
  simp only [mul_assoc]

theorem actual_attached_mean_table_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (attachedMeanTable C n (beta n) queue)) =
      profileForm (localBodyMixture C n (beta n) queue-actualReferenceMean C n (beta n)) := by
  filter_upwards [actual_body_mean_table_output_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta,
    legCutoff_le_square_eventually C hC,eventually_ge_atTop 2] with n ho hb hc hn operator hop queue hq
  unfold attachedMeanTable
  rw [map_queueAverage,map_queueAverage]
  have hlocal (sample : Window (legCutoff C n-1)) :
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (bodyMeanTable C n (beta n) ((sample : ℤ)+queue))) =
      profileForm (attachedBodyAtSource C n (beta n) queue sample-actualReferenceMean C n (beta n)) := by
    rw [ho operator hop _ (attached_mean_shift_bound C n queue hq sample),attachedBodyAtSource_root_image C n (beta n) queue sample hb.2.2
      (body_shift_fraction C n hn hc _ (attached_mean_shift_bound C n queue hq sample)).2]
  simp_rw [hlocal]
  have hid : (∑ sample : Window (legCutoff C n-1),
      (windowGaussian (10*n) (legCutoff C n-1)).weight sample •
        (attachedBodyAtSource C n (beta n) queue sample-actualReferenceMean C n (beta n))) =
      localBodyMixture C n (beta n) queue-actualReferenceMean C n (beta n) := by
    funext color
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub,
      Finset.sum_sub_distrib,← Finset.sum_mul,FiniteDist.sum_one,one_mul,localBodyMixture_source_average]
  rw [← hid,map_sum]
  simp only [queueAverage,map_smul,MvPolynomial.smul_eq_C_mul]

theorem actual_attached_mean_table_raw_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      activity (responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n))
        (attachedMeanTable C n (beta n) queue) ≤ bodyMeanInputConstant/(n : ℝ)^46 := by
  filter_upwards [actual_body_mean_table_raw_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hb hn primary body hp hbody ppool bpool hpp hbp queue hq
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  apply activity_queueAverage_le_bound _
    (responseInputWeight_nonneg _ _ _ _ _ _ (sq_nonneg _) (by positivity))
  intro sample
  exact hb _ (attached_mean_shift_bound C n queue hq sample) primary body hp hbody ppool bpool hpp hbp

end
end AFT.V7Calibration

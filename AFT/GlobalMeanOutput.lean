import AFT.GlobalBackgroundMean

/-! # Exact global first-degree cancellation in the actual output algebra -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial FiniteDist
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance globalMeanOutputFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance globalMeanOutputSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def blockBodyMeanProfile (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n) (queue : ℤ) :
    Fin (Parameters.modulus n) → ℝ :=
  match index with
  | .inl _ => localBodyMixture C n beta queue
  | .inr _ => attachedBodyAtSource C n beta queue 0

def endpointMeanProfile (C : ℝ) (n : ℕ) (beta : ℝ) (color : Fin (Parameters.modulus n)) : ℝ :=
  (∑ second,localPairMixture C n beta color second)+(∑ first,localPairMixture C n beta first color)-
    2*actualReferenceMean C n beta color

def globalLinearTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  (∑ index,blockBodyMeanTable C n beta index (actualQueueShifts n sample index))+
    MvPolynomial.C (Parameters.legs n : ℝ)*pairMeanTable C n beta

def globalLinearProfile (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) : Fin (Parameters.modulus n) → ℝ :=
  (∑ index, (blockBodyMeanProfile C n beta index (actualQueueShifts n sample index)-actualReferenceMean C n beta))+
    (Parameters.legs n : ℝ) • endpointMeanProfile C n beta

/-- The concrete root marginal at each body coordinate gives the same
population blur as the original zero-sum conditioned root word. -/
theorem blockBodyMeanProfile_population (C : ℝ) (n : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus n)) :
    (∑ index : blockIndex n, (FiniteDist.retype (actualQueuePlacementLaw n)).expectation (fun sample =>
      blockBodyMeanProfile C n beta index (actualQueueShifts n sample index) color)) =
      (Parameters.bodies n : ℝ)*actualFullBodyProfile C n beta color := by
  have hroot (index : blockIndex n) (f : ℤ → ℝ) :
      (actualRootConditionLaw n).expectation (fun word => f (actualRootField n word index)) =
      (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n) (Parameters.bodies_positive n)).expectation
        (fun root => f root) := by
    rw [← actualRootConditionLaw_coordinate n (actualRootIndex n index),expectation_map]
    rfl
  have hpoint (index : blockIndex n) (queue : ℤ) :
      (actualRootConditionLaw n).expectation (fun word => match index with
        | .inl _ => (windowGaussian (10*n) (legCutoff C n-1)).expectation (fun source =>
            integerShiftProfile n (actualBodyCenter C n beta) (actualRootField n word index+source+queue) color)
        | .inr _ => integerShiftProfile n (actualBodyCenter C n beta) (actualRootField n word index+queue) color) =
      blockBodyMeanProfile C n beta index queue color := by
    cases index with
    | inl leg =>
      dsimp only
      rw [hroot (.inl leg) (fun root => (windowGaussian (10*n) (legCutoff C n-1)).expectation
        (fun source => integerShiftProfile n (actualBodyCenter C n beta) (root+source+queue) color))]
      rw [blockBodyMeanProfile,localBodyMixture_source_average]
      simp only [FiniteDist.expectation,attachedBodyAtSource,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro root _
      ring
    | inr body =>
      dsimp only
      rw [hroot (.inr body) (fun root => integerShiftProfile n (actualBodyCenter C n beta) (root+queue) color)]
      simp only [FiniteDist.expectation,blockBodyMeanProfile,attachedBodyAtSource,add_zero]
  have hp := actual_body_population_expectation C n
    (fun shift => integerShiftProfile n (actualBodyCenter C n beta) shift color)
  refine Eq.trans ?_ hp
  apply Finset.sum_congr rfl
  intro index _
  apply congrArg (FiniteDist.expectation (FiniteDist.retype (actualQueuePlacementLaw n)))
  funext sample
  exact (hpoint index (actualQueueShifts n sample index)).symm

/-- Calibration cancels the real population mean after the single common
queue is marginalized. No independence between queue-selected sites is used. -/
theorem globalLinearProfile_average_zero_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ beta : ℝ,
      (∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample • globalLinearProfile C n beta sample) = 0 := by
  filter_upwards [actual_total_mean_eventually C hC] with n hm beta
  funext color
  have hpopulation := blockBodyMeanProfile_population C n beta color
  have hmean := hm beta color
  have hpop : (Parameters.dimension n : ℝ) = Parameters.bodies n+2*Parameters.legs n := by
    exact_mod_cast (Parameters.population_identity n).symm
  have hmass := (FiniteDist.retype (actualQueuePlacementLaw n)).sum_one
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
  have heq : (∑ sample, (FiniteDist.retype (actualQueuePlacementLaw n)).weight sample*globalLinearProfile C n beta sample color) =
      (Parameters.bodies n : ℝ)*actualFullBodyProfile C n beta color-
      (Parameters.bodies n : ℝ)*actualReferenceMean C n beta color+
      (Parameters.legs n : ℝ)*endpointMeanProfile C n beta color := by
    simp only [globalLinearProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Pi.sub_apply,
      mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hmass,one_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hmass,one_mul,Finset.sum_const,
      Finset.card_univ,blockIndex_card,nsmul_eq_mul]
    exact congrArg (fun value => value-(Parameters.bodies n : ℝ)*actualReferenceMean C n beta color+
      (Parameters.legs n : ℝ)*endpointMeanProfile C n beta color) hpopulation
  rw [heq]
  unfold endpointMeanProfile
  rw [hpop] at hmean
  nlinarith


theorem actual_block_body_mean_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ index : blockIndex n, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (blockBodyMeanTable C n (beta n) index queue)) =
      profileForm (blockBodyMeanProfile C n (beta n) index queue-actualReferenceMean C n (beta n)) := by
  filter_upwards [actual_body_mean_table_output_eventually C hC beta hbeta,
    actual_attached_mean_table_output_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta,
    legCutoff_le_square_eventually C hC,eventually_ge_atTop 2]
    with n hb ha hc hcut hn operator hop index queue hq
  cases index with
  | inl _ => exact ha operator hop queue hq
  | inr _ =>
    have hs : |queue| ≤ maxBodyShift C n := by unfold maxBodyShift; omega
    have hi := attachedBodyAtSource_root_image C n (beta n) queue 0 hc.2.2
      (by simpa only [zero_add] using (body_shift_fraction C n hn hcut queue hs).2)
    simp only [zero_add] at hi
    change _ = profileForm (attachedBodyAtSource C n (beta n) queue 0-actualReferenceMean C n (beta n))
    rw [← hi]
    exact hb operator hop queue hs

theorem actual_global_linear_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ sample,
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (globalLinearTable C n (beta n) sample)) =
      profileForm (globalLinearProfile C n (beta n) sample) := by
  filter_upwards [actual_block_body_mean_output_eventually C hC beta hbeta,
    actual_pair_mean_table_output_eventually C hC beta hbeta] with n hb hp operator hop sample
  let T := inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
  let L := actualLeadingOutput C n (beta n)
  have hconst (scalar : ℝ) : L (T (MvPolynomial.C scalar)) = MvPolynomial.C scalar := by
    change L (T (algebraMap ℝ _ scalar)) = algebraMap ℝ _ scalar
    rw [T.commutes,L.commutes]
  have hblock (index) := hb operator hop index (actualQueueShifts n sample index) (actualQueueShifts_bound n sample index)
  change L (T (globalLinearTable C n (beta n) sample)) = _
  simp only [globalLinearTable,map_add,map_sum,map_mul,hconst]
  dsimp only [T,L]
  simp_rw [hblock,hp operator hop]
  change (∑ index,profileForm (blockBodyMeanProfile C n (beta n) index (actualQueueShifts n sample index)-actualReferenceMean C n (beta n)))+
    MvPolynomial.C (Parameters.legs n : ℝ)*profileForm (endpointMeanProfile C n (beta n)) = _
  simp only [globalLinearProfile,map_add,map_sum,map_smul,MvPolynomial.smul_eq_C_mul]

/-- The literal replacement subtracts the actual average of all first
input tables. Its small norm follows from queue support, while its output
is unchanged because the calibrated population average is exactly zero. -/
theorem globalMeanTable_eq_centered_linear (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    globalMeanTable C n beta sample = globalLinearTable C n beta sample-
      queueAverage (FiniteDist.retype (actualQueuePlacementLaw n)) (globalLinearTable C n beta) := by
  let baseline := (∑ index,blockBodyMeanTable C n beta index 0)+
    MvPolynomial.C (Parameters.legs n : ℝ)*pairMeanTable C n beta
  have hchange (q) : globalMeanChangeTable C n beta q = globalLinearTable C n beta q-baseline := by
    simp only [globalMeanChangeTable,globalLinearTable,baseline,Finset.sum_sub_distrib]
    ring
  have hfunction : globalMeanChangeTable C n beta = (fun q => globalLinearTable C n beta q-baseline) := funext hchange
  rw [globalMeanTable,hfunction,queueAverage_sub,queueAverage_const]
  ring

/-- This is the global first-degree output identity used by the actual
background certificate; formal input labels have not been identified. -/
theorem actual_global_mean_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ sample,
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (globalMeanTable C n (beta n) sample)) =
      actualLeadingOutput C n (beta n)
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (globalLinearTable C n (beta n) sample)) := by
  filter_upwards [actual_global_linear_output_eventually C hC beta hbeta,
    globalLinearProfile_average_zero_eventually C hC] with n ho hz operator hop sample
  rw [globalMeanTable_eq_centered_linear,map_sub,map_sub,map_queueAverage,map_queueAverage]
  simp_rw [ho operator hop]
  have havg : queueAverage (FiniteDist.retype (actualQueuePlacementLaw n))
      (fun q => profileForm (globalLinearProfile C n (beta n) q)) = 0 := by
    have heq : queueAverage (FiniteDist.retype (actualQueuePlacementLaw n))
        (fun q => profileForm (globalLinearProfile C n (beta n) q)) =
      profileForm (∑ q, (FiniteDist.retype (actualQueuePlacementLaw n)).weight q • globalLinearProfile C n (beta n) q) := by
      simp only [queueAverage,map_sum,map_smul,MvPolynomial.smul_eq_C_mul]
    rw [heq,hz (beta n),map_zero]
  rw [havg,sub_zero]

end
end AFT.V7Calibration

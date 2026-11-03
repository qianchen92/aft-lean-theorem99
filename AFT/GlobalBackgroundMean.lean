import AFT.LocalBackgroundInput
import AFT.ActualPhysicalMean

/-! # A literal global mean certificate supported on the true common queue -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed : Type*}

theorem activity_sub_le (w : Seed → ℝ) (hw : ∀ seed, 0 ≤ w seed) (first second : Table Seed) :
    activity w (first-second) ≤ activity w first+activity w second := by
  simpa only [sub_eq_add_neg,activity_neg] using activity_add_le w hw first (-second)

theorem hasOrder_sub (order : Seed → ℕ) (minimum : ℕ) (first second : Table Seed)
    (hf : HasOrder order minimum first) (hs : HasOrder order minimum second) :
    HasOrder order minimum (first-second) := by
  simpa only [sub_eq_add_neg] using hasOrder_add order minimum first (-second) hf (hasOrder_neg order minimum second hs)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance globalBackgroundMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance globalBackgroundMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def blockBodyMeanTable (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n) (queue : ℤ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  match index with
  | .inl _ => attachedMeanTable C n beta queue
  | .inr _ => bodyMeanTable C n beta queue

def globalMeanChangeTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  ∑ index, (blockBodyMeanTable C n beta index (actualQueueShifts n sample index)-blockBodyMeanTable C n beta index 0)

def globalMeanTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  globalMeanChangeTable C n beta sample-
    queueAverage (FiniteDist.retype (actualQueuePlacementLaw n)) (globalMeanChangeTable C n beta)

theorem blockBodyMeanTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n) (queue : ℤ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (blockBodyMeanTable C n beta index queue) := by
  cases index with
  | inl _ => exact attachedMeanTable_hasOrder C n beta queue
  | inr _ => exact bodyMeanTable_hasOrder C n beta queue

theorem globalMeanTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (globalMeanTable C n beta sample) := by
  have hc (q) : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1 (globalMeanChangeTable C n beta q) := by
    apply hasOrder_sum
    intro index _
    exact hasOrder_sub _ _ _ _ (blockBodyMeanTable_hasOrder C n beta index _) (blockBodyMeanTable_hasOrder C n beta index _)
  exact hasOrder_sub _ _ _ _ (hc sample) (queueAverage_hasOrder _ _ _ _ hc)

/-- Only the q positions selected by the actual permutation can change.
The bound does not multiply a one-body error by all N_B bodies. -/
theorem globalMeanChangeTable_activity_le (C : ℝ) (n : ℕ) (beta : ℝ)
    (w : InputSeed (Fin (Parameters.modulus n)) → ℝ) (hw : ∀ seed, 0 ≤ w seed)
    (bound : ℝ) (h : ∀ (index : blockIndex n) (queue : ℤ), |queue| ≤ queueCutoff n →
      activity w (blockBodyMeanTable C n beta index queue) ≤ bound)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    activity w (globalMeanChangeTable C n beta sample) ≤ (Parameters.modulus n : ℝ)*(2*bound) := by
  have hpoint (index : blockIndex n) : activity w
      (blockBodyMeanTable C n beta index (actualQueueShifts n sample index)-blockBodyMeanTable C n beta index 0) ≤
      if sample.2 index ∈ actualQueueSelection n then 2*bound else 0 := by
    by_cases hi : sample.2 index ∈ actualQueueSelection n
    · rw [if_pos hi]
      exact (activity_sub_le w hw _ _).trans ((add_le_add (h index _ (actualQueueShifts_bound n sample index))
        (h index 0 (by simp))).trans_eq (by ring))
    · have hz : actualQueueShifts n sample index = 0 := by
        simp only [actualQueueShifts,FiniteDist.sharedQueueShift,if_neg hi]
      simp only [if_neg hi,hz,sub_self,activity_zero,le_refl]
  apply (activity_sum_le w hw _ _).trans
  apply (Finset.sum_le_sum fun index _ => hpoint index).trans_eq
  rw [Equiv.sum_comp sample.2 (fun index => if index ∈ actualQueueSelection n then 2*bound else 0)]
  simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,actualQueueSelection_card]

theorem globalMeanTable_activity_le (C : ℝ) (n : ℕ) (beta : ℝ)
    (w : InputSeed (Fin (Parameters.modulus n)) → ℝ) (hw : ∀ seed, 0 ≤ w seed)
    (bound : ℝ) (h : ∀ (index : blockIndex n) (queue : ℤ), |queue| ≤ queueCutoff n →
      activity w (blockBodyMeanTable C n beta index queue) ≤ bound)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    activity w (globalMeanTable C n beta sample) ≤ (Parameters.modulus n : ℝ)*(4*bound) := by
  have hc := globalMeanChangeTable_activity_le C n beta w hw bound h
  apply (activity_sub_le w hw _ _).trans
  exact (add_le_add (hc sample) (activity_queueAverage_le_bound w hw _ _ _ hc)).trans_eq (by ring)

theorem actual_global_mean_raw_activity_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primary body : FiniteDist (Fin (Parameters.modulus n)),
      primary.weight = actualPrimary C n (beta n) → body.weight = actualBodyCenter C n (beta n) →
      ∀ primaryPool bodyPool : ℕ, Parameters.legs n ≤ 2*primaryPool → Parameters.bodies n ≤ 2*bodyPool →
      ∀ sample, activity (responseInputWeight primary body primaryPool bodyPool ((n : ℝ)^2) (4/v7Activation C n))
        (globalMeanTable C n (beta n) sample) ≤ 8*bodyMeanInputConstant/(n : ℝ)^6 := by
  filter_upwards [actual_body_mean_table_raw_eventually C hC beta hbeta,
    actual_attached_mean_table_raw_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hb ha hn primary body hp hbody ppool bpool hpp hbp sample
  let w := responseInputWeight primary body ppool bpool ((n : ℝ)^2) (4/v7Activation C n)
  have hrho : 0 < v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hw : ∀ seed, 0 ≤ w seed := responseInputWeight_nonneg _ _ _ _ _ _ (sq_nonneg _) (by positivity)
  have hblock (index : blockIndex n) (queue : ℤ) (hq : |queue| ≤ queueCutoff n) :
      activity w (blockBodyMeanTable C n (beta n) index queue) ≤ bodyMeanInputConstant/(n : ℝ)^46 := by
    cases index with
    | inl _ => exact ha primary body hp hbody ppool bpool hpp hbp queue hq
    | inr _ =>
      apply hb queue _ primary body hp hbody ppool bpool hpp hbp
      unfold maxBodyShift
      omega
  have hg := globalMeanTable_activity_le C n (beta n) w hw (bodyMeanInputConstant/(n : ℝ)^46) hblock sample
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    exact_mod_cast (show Parameters.modulus n ≤ 2*n^40 by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2)
  have hB := (local_background_constants_nonneg C).1
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply hg.trans
  calc
    _ ≤ (2*(n : ℝ)^40)*(4*(bodyMeanInputConstant/(n : ℝ)^46)) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by field_simp; ring

/-- The literal global first-degree input is small after the real common
queue is averaged, with the same actual inverse used for every local seed. -/
theorem actual_global_mean_input_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ sample, activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool ((n : ℝ)^2))
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator
          (globalMeanTable C n (beta n) sample)) ≤ 8*bodyMeanInputConstant/(n : ℝ)^6 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually C hC beta pool htypical,
    actual_global_mean_raw_activity_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,htypical] with n hi hg hl ht
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro bpool hbp sample
  exact (inversePrimaryTable_activity_le _ _ _ _ _ _ (sq_nonneg _) operator
    (hi (actualBodyLaw C n (beta n)) bpool ((n : ℝ)^2) (sq_nonneg _)) _).trans
      (hg _ _ hl.1 hl.2.1 (pool n) bpool ht.2.2 hbp sample)

end
end AFT.V7Calibration

import AFT.BackgroundQueueAlgebra
import AFT.PhysicalBackgroundPolynomial

/-! # The actual shared-queue background reciprocal and initial certificate

The queue is sampled once for all physical blocks. Its average is taken before
finite inversion. The resulting literal correction has positive input order,
canonical joint seeds, and the actual uniform `O(λ⁻²)` activity bound.
-/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance backgroundQueueCertificateFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance backgroundQueueCertificateSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualBackgroundReciprocal (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  queueReciprocal (FiniteDist.retype (actualQueuePlacementLaw n))
    (fun sample => actualBackgroundLog C n beta operator sample cutoff) cutoff

def actualInitialBackgroundCorrection (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
    (actualBackgroundReciprocal C n beta operator cutoff-1)

def actualBackgroundPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) : Table (Fin (Parameters.modulus n)) :=
  queueAverage (FiniteDist.retype (actualQueuePlacementLaw n))
    (fun sample => ∏ index,blockPhysicalPolynomial C n beta index (actualQueueShifts n sample index))

theorem actualInitialBackgroundCorrection_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 1
      (actualInitialBackgroundCorrection C n beta operator cutoff) := by
  apply hasOrder_truncate
  apply hasOrder_finiteCorrection_sub_one
  apply queueError_hasOrder
  exact fun sample => actualBackgroundLog_hasOrder C n beta operator sample cutoff

theorem actualInitialBackgroundCorrection_truncated (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) :
    truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
      (actualInitialBackgroundCorrection C n beta operator cutoff) =
      actualInitialBackgroundCorrection C n beta operator cutoff := truncate_idempotent ..

theorem actualInitialBackgroundCorrection_add_one (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) :
    1+actualInitialBackgroundCorrection C n beta operator cutoff =
      truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
        (actualBackgroundReciprocal C n beta operator cutoff) := by
  rw [actualInitialBackgroundCorrection,truncate_sub,truncate_one]
  ring

theorem actualBackgroundReciprocal_identity (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (cutoff : ℕ) :
    truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff
      (actualBackgroundReciprocal C n beta operator cutoff *
        queueAverage (FiniteDist.retype (actualQueuePlacementLaw n))
          (fun sample => exponential (actualBackgroundLog C n beta operator sample cutoff) cutoff)) = 1 :=
  queueReciprocal_identity _ _ _ _ (fun sample => actualBackgroundLog_hasOrder C n beta operator sample cutoff)

theorem actual_background_reciprocal_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ cutoff,
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualBackgroundReciprocal C n (beta n) operator cutoff) ∧
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualInitialBackgroundCorrection C n (beta n) operator cutoff) := by
  filter_upwards [actual_background_log_canonical_eventually C hC beta hbeta]
    with n hc operator hop cutoff
  have he : InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (queueError (FiniteDist.retype (actualQueuePlacementLaw n))
        (fun sample => actualBackgroundLog C n (beta n) operator sample cutoff) cutoff) :=
    (InputTableCanonical.queueAverage _ _ (fun sample => (hc operator hop sample cutoff).exponential cutoff)).sub
      InputTableCanonical.one
  have hi := he.finiteCorrection cutoff
  exact ⟨hi,(hi.sub InputTableCanonical.one).truncate _ cutoff⟩

theorem backgroundLogConstant_nonneg (C : ℝ) : 0 ≤ backgroundLogConstant C := by
  have hB := (local_background_constants_nonneg C).1
  have hH := (local_background_constants_nonneg C).2.2.2.2.1
  unfold backgroundLogConstant
  positivity

theorem actual_background_reciprocal_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧ Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∃ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n ∧ ∀ bodyPool : ℕ, Parameters.bodies n ≤ 2*bodyPool →
      ∀ cutoff, 1 ≤ cutoff →
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (pool n) bodyPool ((n : ℝ)^2)) (actualBackgroundReciprocal C n (beta n) operator cutoff) ≤ 2 ∧
      activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (pool n) bodyPool ((n : ℝ)^2)) (actualInitialBackgroundCorrection C n (beta n) operator cutoff) ≤
        4*backgroundLogConstant C/(n : ℝ)^2 := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 4*backgroundLogConstant C ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (4*backgroundLogConstant C))
  filter_upwards [actual_background_log_activity_eventually C hC beta pool htypical,
    hlarge,eventually_ge_atTop 1] with n hl hlarge hn
  obtain ⟨operator,hop,hl⟩ := hl
  refine ⟨operator,hop,?_⟩
  intro bodyPool hpool cutoff hcut
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (pool n) bodyPool ((n : ℝ)^2)
  have hw : ∀ seed, 0 ≤ weight seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hx
  have hb : 0 ≤ backgroundLogConstant C/(n : ℝ)^2 := div_nonneg (backgroundLogConstant_nonneg C) (sq_nonneg _)
  have hs : backgroundLogConstant C/(n : ℝ)^2 ≤ 1/4 :=
    (div_le_iff₀ (sq_pos_of_pos hx0)).mpr (by nlinarith)
  have hi := queueReciprocal_small_activity weight hw (FiniteDist.retype (actualQueuePlacementLaw n))
    (fun sample => actualBackgroundLog C n (beta n) operator sample cutoff) cutoff
    (backgroundLogConstant C/(n : ℝ)^2) hb hs (fun sample => hl bodyPool hpool sample cutoff hcut)
  exact ⟨hi.1,(activity_truncate_le weight hw _ _ _).trans (hi.2.trans_eq (by ring))⟩

/-- The denominator is the average of the complete actual block generating
law, with one common queue value and placement inside every product. -/
theorem actual_background_reciprocal_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ cutoff,
      truncate (fun _ => 1) cutoff
        (actualLeadingOutput C n (beta n) (actualBackgroundReciprocal C n (beta n) operator cutoff) *
          actualBackgroundPolynomial C n (beta n)) = 1 := by
  filter_upwards [actual_background_exponential_polynomial_eventually C hC beta hbeta]
    with n he operator hop cutoff
  let queue := FiniteDist.retype (actualQueuePlacementLaw n)
  let log := fun sample => actualBackgroundLog C n (beta n) operator sample cutoff
  let inv := actualBackgroundReciprocal C n (beta n) operator cutoff
  let output := actualLeadingOutput C n (beta n)
  have hi := outputHom_truncation_respects (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualPrimaryChannel C n) (actualBodyChannel n) cutoff
    (inv*queueAverage queue (fun sample => exponential (log sample) cutoff)) 1
    (by simpa only [truncate_one] using actualBackgroundReciprocal_identity C n (beta n) operator cutoff)
  change truncate (fun _ => 1) cutoff (output (inv*queueAverage queue (fun sample => exponential (log sample) cutoff))) =
    truncate (fun _ => 1) cutoff (output 1) at hi
  rw [map_mul,map_one,truncate_one,map_queueAverage] at hi
  have hq := truncate_queueAverage_congr queue (fun _ => 1) cutoff
    (fun sample => output (exponential (log sample) cutoff))
    (fun sample => ∏ index,blockPhysicalPolynomial C n (beta n) index (actualQueueShifts n sample index))
    (fun sample => he operator hop sample cutoff)
  change truncate (fun _ => 1) cutoff (queueAverage queue (fun sample => output (exponential (log sample) cutoff))) =
    truncate (fun _ => 1) cutoff (actualBackgroundPolynomial C n (beta n)) at hq
  change truncate (fun _ => 1) cutoff (output inv*actualBackgroundPolynomial C n (beta n)) = 1
  rw [truncate_mul,← hq,← truncate_mul]
  exact hi

/-- The actual finite, positive-order initial input correction cancels the
whole shared-queue background through the same input/output degree cutoff. -/
theorem actual_initial_background_correction_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ cutoff,
      truncate (fun _ => 1) cutoff
        (actualLeadingOutput C n (beta n) (1+actualInitialBackgroundCorrection C n (beta n) operator cutoff) *
          actualBackgroundPolynomial C n (beta n)) = 1 := by
  filter_upwards [actual_background_reciprocal_polynomial_eventually C hC beta hbeta]
    with n hi operator hop cutoff
  have ht := outputHom_truncation_respects (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualPrimaryChannel C n) (actualBodyChannel n) cutoff
    (1+actualInitialBackgroundCorrection C n (beta n) operator cutoff)
    (actualBackgroundReciprocal C n (beta n) operator cutoff)
    (by rw [actualInitialBackgroundCorrection_add_one,truncate_idempotent])
  change truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n) _) =
    truncate (fun _ => 1) cutoff (actualLeadingOutput C n (beta n) _) at ht
  rw [truncate_mul,ht,← truncate_mul]
  exact hi operator hop cutoff

end
end AFT.V7Calibration

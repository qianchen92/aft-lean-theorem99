import AFT.BackgroundCanonical
import AFT.MarkedSeedOutput
import AFT.PairCompletionCanonical

/-! # Complete canonicality of the literal global background certificate -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance globalBackgroundCanonicalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance globalBackgroundCanonicalSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

theorem actual_endpoint_table_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualEndpointHigherTable C n (beta n) operator) := by
  filter_upwards [actual_inactive_body_pair_canonical_eventually C hC beta hbeta,
    actual_pair_completion_canonical_eventually C hC beta hbeta,
    actual_marked_input_canonical_eventually C hC beta hbeta,
    actual_marked_fringe_canonical_eventually C hC beta hbeta,
    actual_primary_seed_canonical_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n hb hc hm hf hi hl operator hop
  apply InputTableCanonical.sum
  intro index _
  apply (InputTableCanonical.C _).mul
  apply InputTableCanonical.X
  fin_cases index
  · have href : inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualInactiveBodyPairInput C n (beta n)) = fun _ => actualBodyLaw C n (beta n) := by
      funext slot
      fin_cases slot <;> rfl
    simpa [actualEndpointSeed,href] using hb
  · have href : inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualPairCompletionInput C n (beta n) operator) = fun _ => actualPrimaryLaw C n (beta n) :=
      funext (all_primary_reference _ _ _ rfl)
    simpa [actualEndpointSeed,href] using hc operator hop
  · exact hi operator hop _ _ hm
  · apply hi operator hop
    have href : inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualMarkedFringeInput C n (beta n)) = fun _ => actualPrimaryLaw C n (beta n) :=
      funext (all_primary_reference _ _ _ rfl)
    rw [href]
    exact hf _ hl.1

/-- Every variable occurring in the actual global log is a genuine joint
canonical input kernel under its actual calibrated primary/body references. -/
theorem actual_background_log_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ sample cutoff,
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualBackgroundLog C n (beta n) operator sample cutoff) := by
  filter_upwards [actual_mean_tables_canonical_eventually C hC beta hbeta,
    actual_covariance_table_canonical_eventually C hC beta hbeta,
    actual_endpoint_table_canonical_eventually C hC beta hbeta,
    actual_primary_seed_canonical_eventually C hC beta hbeta] with n hm hc he hi operator hop sample cutoff
  dsimp only at hm
  have hT (table : Table (InputSeed (Fin (Parameters.modulus n))))
      (ht : InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) table) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (inversePrimaryTable (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (v7Activation C n) operator table) :=
    inversePrimaryTable_canonical _ _ _ operator table ht (hi operator hop _)
  have hp := hT _ hm.1
  have he := he operator hop
  have hlinear (index : blockIndex n) (queue : ℤ) (hq : |queue| ≤ queueCutoff n) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (blockBackgroundLinear C n (beta n) operator index queue) := by
    cases index with
    | inl _ => exact hp.add (hT _ (hm.2.2.1 queue hq))
    | inr _ => exact hT _ (hm.2.1 queue (by unfold maxBodyShift; omega))
  have herror (index : blockIndex n) (queue : ℤ) (hq : |queue| ≤ queueCutoff n) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (blockBackgroundError C n (beta n) operator index queue) := by
    cases index with
    | inl _ =>
      have hb := hT _ (hm.2.2.1 queue hq)
      exact (hp.add hb).add (((he.add (hp.mul hb)).add (he.mul hb)).add (hT _ (hc queue hq)))
    | inr _ => exact hlinear _ queue hq
  apply (hT _ (hm.2.2.2 sample)).add
  apply InputTableCanonical.sum
  intro index _
  exact ((herror index _ (actualQueueShifts_bound n sample index)).logarithm cutoff).sub
    (hlinear index _ (actualQueueShifts_bound n sample index))

end
end AFT.V7Calibration

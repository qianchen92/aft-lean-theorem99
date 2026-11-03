import AFT.PairCompletionOutput
import AFT.MarkedSeedOutput
import AFT.EndpointTable

/-! # The complete endpoint certificate has the exact physical canonical mass -/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actual_inverse_primary_seedOutputMass (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap = actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0)
    (seed : InputSeed (Fin (Parameters.modulus n))) (hbody : seed.bodyOrder = 0)
    (output : Fin (seed.primaryOrder+seed.bodyOrder) → Fin (Parameters.modulus n)) :
    seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (actualPrimaryChannel C n) (actualBodyChannel n)
      (inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator seed) output =
    seed.kernel output*∏ slot,(actualPrimaryLaw C n beta).weight (output slot) := by
  have hh := inverse_primary_seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (v7Activation C n) hrho operator (actualBodyChannel n) seed hbody hp output
  have hdecision : (fun a b : Fin (Parameters.modulus n) => Classical.propDecidable (a = b)) =
      instDecidableEqFin (Parameters.modulus n) := Subsingleton.elim _ _
  rw [hdecision] at hh
  unfold actualPrimaryChannel
  rw [← hop]
  exact hh

theorem actual_marked_fringe_outputMass (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap = actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hl : (actualPrimaryLaw C n beta).weight = actualPrimary C n beta)
    (hp : ∀ color,actualPrimary C n beta color ≠ 0)
    (output : Fin 2 → Fin (Parameters.modulus n)) :
    seedOutputMass (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (actualPrimaryChannel C n) (actualBodyChannel n)
      (inversePrimarySeed (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) (v7Activation C n) operator
        (actualMarkedFringeInput C n beta)) output =
      (actualPrimary C n beta (output 0)-actualReferenceMean C n beta (output 0))*
      (actualRootBodyMean n (output 1)-actualReferenceMean C n beta (output 1)) := by
  rw [actual_inverse_primary_seedOutputMass C n beta operator hop hrho (by rw [hl]; exact hp) (actualMarkedFringeInput C n beta) rfl output]
  change (primaryReferenceDifferenceDensity C n beta (output 0)*rootMeanDifferenceDensity C n beta (output 1))*
    (∏ slot : Fin 2,(actualPrimaryLaw C n beta).weight (output slot)) = _
  rw [Fin.prod_univ_two,hl]
  unfold primaryReferenceDifferenceDensity rootMeanDifferenceDensity
  field_simp [hp]

theorem actual_endpoint_completed_mass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n → ∀ output : Fin 2 → Fin (Parameters.modulus n),
      let out := fun seed : InputSeed (Fin (Parameters.modulus n)) =>
        seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (actualPrimaryChannel C n) (actualBodyChannel n) seed
      (1-v7Activation C n)*(out (actualInactiveBodyPairInput C n (beta n)) output+
        out (actualPairCompletionInput C n (beta n) operator) output)+
      v7Activation C n*(out (inversePrimarySeed (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (actualMarkedInput C n (beta n))) output+
        out (inversePrimarySeed (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (v7Activation C n) operator (actualMarkedFringeInput C n (beta n))) output) =
      SafePair.canonicalPair (actualReferenceMean C n (beta n)) (localPairMixture C n (beta n)) (output 0) (output 1) := by
  filter_upwards [actual_inactive_pair_completed_output_eventually C hC beta hbeta,
    actual_marked_inverse_outputMass_eventually C hC beta hbeta,
    actual_marked_canonical_root_decomposition C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n hi hm hd hl hp hn operator hop output
  dsimp only
  have hp0 (color) : actualPrimary C n (beta n) color ≠ 0 := (hp.1 _).ne'
  have hpLaw (color) : (actualPrimaryLaw C n (beta n)).weight color ≠ 0 := by rw [hl.1]; exact hp0 color
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  rw [hi operator hop hrho hpLaw output,hm operator hop output,
    actual_marked_fringe_outputMass C n (beta n) operator hop hrho hl.1 hp0 output,← hd (output 0) (output 1),hl.2.2]
  simp only [SafePair.canonicalPair,localPairMixture,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

end
end AFT.V7Calibration

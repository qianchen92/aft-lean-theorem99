import AFT.EndpointOutputMass
import AFT.PhysicalCovarianceForms
import AFT.PhysicalBlockMass

/-! # The actual endpoint pair's complete centered generating polynomial -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def pairWordForm : ((Fin 2 → Color) → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun mass := ∑ word,MvPolynomial.C (mass word)*∏ slot,MvPolynomial.X (word slot)
  map_add' first second := by simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar mass := by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,mul_assoc,
      RingHom.id_apply,MvPolynomial.smul_eq_C_mul]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem actual_endpoint_higher_output_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      actualLeadingOutput C n (beta n) (actualEndpointHigherTable C n (beta n) operator) =
      pairForm (SafePair.canonicalPair (actualReferenceMean C n (beta n)) (localPairMixture C n (beta n))) := by
  filter_upwards [actual_endpoint_completed_mass_eventually C hC beta hbeta] with n hm operator hop
  let L := actualLeadingOutput C n (beta n)
  let out := fun seed : InputSeed (Fin (Parameters.modulus n)) =>
    seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (actualPrimaryChannel C n) (actualBodyChannel n) seed
  let seed0 := actualInactiveBodyPairInput C n (beta n)
  let seed1 := actualPairCompletionInput C n (beta n) operator
  let seed2 := inversePrimarySeed (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (v7Activation C n) operator (actualMarkedInput C n (beta n))
  let seed3 := inversePrimarySeed (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (v7Activation C n) operator (actualMarkedFringeInput C n (beta n))
  let out0 : (Fin 2 → Fin (Parameters.modulus n)) → ℝ := out seed0
  let out1 : (Fin 2 → Fin (Parameters.modulus n)) → ℝ := out seed1
  let out2 : (Fin 2 → Fin (Parameters.modulus n)) → ℝ := out seed2
  let out3 : (Fin 2 → Fin (Parameters.modulus n)) → ℝ := out seed3
  have hc (x : ℝ) : L (MvPolynomial.C x) = MvPolynomial.C x := L.commutes x
  have hx0 : L (MvPolynomial.X seed0) = pairWordForm out0 := by
    dsimp only [L]
    rw [actualLeadingOutput,outputHom_X,seedOutput_eq_mass]
    rfl
  have hx1 : L (MvPolynomial.X seed1) = pairWordForm out1 := by
    dsimp only [L]
    rw [actualLeadingOutput,outputHom_X,seedOutput_eq_mass]
    rfl
  have hx2 : L (MvPolynomial.X seed2) = pairWordForm out2 := by
    dsimp only [L]
    rw [actualLeadingOutput,outputHom_X,seedOutput_eq_mass]
    rfl
  have hx3 : L (MvPolynomial.X seed3) = pairWordForm out3 := by
    dsimp only [L]
    rw [actualLeadingOutput,outputHom_X,seedOutput_eq_mass]
    rfl
  have heq : actualEndpointHigherTable C n (beta n) operator =
      MvPolynomial.C (1-v7Activation C n)*MvPolynomial.X seed0+
      MvPolynomial.C (1-v7Activation C n)*MvPolynomial.X seed1+
      MvPolynomial.C (v7Activation C n)*MvPolynomial.X seed2+
      MvPolynomial.C (v7Activation C n)*MvPolynomial.X seed3 := by
    simp [actualEndpointHigherTable,endpointCoefficient,actualEndpointSeed,Fin.sum_univ_succ,seed0,seed1,seed2,seed3]
    ring
  change L _ = _
  rw [heq]
  simp only [map_add,map_mul,hc,hx0,hx1,hx2,hx3]
  have hmass : (1-v7Activation C n) • (out0+out1)+v7Activation C n • (out2+out3) =
      fun word : Fin 2 → Fin (Parameters.modulus n) =>
        SafePair.canonicalPair (actualReferenceMean C n (beta n)) (localPairMixture C n (beta n)) (word 0) (word 1) :=
    funext (hm operator hop)
  calc
    _ = pairWordForm ((1-v7Activation C n) • (out0+out1)+v7Activation C n • (out2+out3)) := by
      simp only [map_add,map_smul,MvPolynomial.smul_eq_C_mul]
      ring
    _ = _ := by
      rw [hmass]
      exact pairForm_word _

/-- Combining the genuine endpoint means with all four higher seeds gives
the entire centered physical pair law, including its constant and linear terms. -/
theorem actual_endpoint_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
      operator.toLinearMap = actualResponse C n →
      actualLeadingOutput C n (beta n)
        (1+localPrimaryMeanInputTable C n (beta n) operator+actualEndpointHigherTable C n (beta n) operator) =
      pairGenerating (actualReferenceMean C n (beta n)) (localPairMixture C n (beta n)) := by
  filter_upwards [actual_endpoint_higher_output_eventually C hC beta hbeta,
    actual_pair_mean_table_output_eventually C hC beta hbeta,
    actual_local_pair_mass_eventually C hC beta hbeta] with n hh hl hm operator hop
  rw [map_add,map_add,map_one,hh operator hop]
  dsimp only [localPrimaryMeanInputTable]
  rw [hl operator hop,pairGenerating_canonical,hm]
  simp only [mul_one,map_one]
  ring

end
end AFT.V7Calibration

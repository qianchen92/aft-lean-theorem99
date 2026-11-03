import AFT.PrimarySeedInverse
import AFT.MarkedFringe
import AFT.V7PairCompletion

/-! # The literal higher-order certificate for the actual endpoint pair -/

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

/-- These are already input kernels: two safe-completion seeds, followed
by the actual inverses of the two marked-law seeds. -/
def actualEndpointSeed (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ)) :
    Fin 4 → InputSeed (Fin (Parameters.modulus parameter)) :=
  ![actualInactiveBodyPairInput cutoffScale parameter beta,
    actualPairCompletionInput cutoffScale parameter beta operator,
    inversePrimarySeed (actualPrimaryLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta)
      (v7Activation cutoffScale parameter) operator (actualMarkedInput cutoffScale parameter beta),
    inversePrimarySeed (actualPrimaryLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta)
      (v7Activation cutoffScale parameter) operator (actualMarkedFringeInput cutoffScale parameter beta)]

def endpointCoefficient (rho : ℝ) : Fin 4 → ℝ := ![1-rho,1-rho,rho,rho]

def actualEndpointHigherTable (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ)) :
    Table (InputSeed (Fin (Parameters.modulus parameter))) :=
  ∑ index : Fin 4, MvPolynomial.C (endpointCoefficient (v7Activation cutoffScale parameter) index) *
    MvPolynomial.X (actualEndpointSeed cutoffScale parameter beta operator index)

def endpointAggregateConstant (cutoffScale : ℝ) : ℝ :=
  512*pairNeumannConstant+64*(pairResidualMixedConstant cutoffScale+pairReferenceMixedConstant cutoffScale)+
    markedAggregateConstant cutoffScale+markedFringeAggregateConstant

theorem actualEndpointHigherTable_hasOrder (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ)) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) 2 (actualEndpointHigherTable cutoffScale parameter beta operator) := by
  apply hasOrder_sum
  intro index _
  apply hasOrder_C_mul_X
  fin_cases index <;> norm_num [actualEndpointSeed,actualInactiveBodyPairInput,actualPairCompletionInput,
    primaryPairSeed,inversePrimarySeed,actualMarkedInput,actualMarkedFringeInput,primaryPairInput]

theorem actualEndpointHigherTable_activity_le (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))
    (weight : InputSeed (Fin (Parameters.modulus parameter)) → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (hrho0 : 0 ≤ v7Activation cutoffScale parameter) (hrho1 : v7Activation cutoffScale parameter ≤ 1) :
    activity weight (actualEndpointHigherTable cutoffScale parameter beta operator) ≤
      (1-v7Activation cutoffScale parameter)*(weight (actualEndpointSeed cutoffScale parameter beta operator 0)+
        weight (actualEndpointSeed cutoffScale parameter beta operator 1))+
      v7Activation cutoffScale parameter*(weight (actualEndpointSeed cutoffScale parameter beta operator 2)+
        weight (actualEndpointSeed cutoffScale parameter beta operator 3)) := by
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index : Fin 4, |endpointCoefficient (v7Activation cutoffScale parameter) index| *
        weight (actualEndpointSeed cutoffScale parameter beta operator index) := by
      apply Finset.sum_le_sum
      intro index _
      simpa only [activity_C,activity_X] using activity_mul_le weight hweight
        (MvPolynomial.C (endpointCoefficient (v7Activation cutoffScale parameter) index))
        (MvPolynomial.X (actualEndpointSeed cutoffScale parameter beta operator index))
    _ = _ := by
      have hnonneg : 0 ≤ 1-v7Activation cutoffScale parameter := sub_nonneg.mpr hrho1
      simp [Fin.sum_univ_succ,endpointCoefficient,abs_of_nonneg hnonneg,abs_of_nonneg hrho0]
      ring

theorem actualResponse_equiv_unique (cutoffScale : ℝ) (parameter : ℕ)
    (first second : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))
    (hfirst : first.toLinearMap = actualResponse cutoffScale parameter)
    (hsecond : second.toLinearMap = actualResponse cutoffScale parameter) : first = second := by
  ext profile color
  exact congrFun (congrArg (fun op : Module.End ℝ (Fin (Parameters.modulus parameter) → ℝ) => op profile)
    (hfirst.trans hsecond.symm)) color

/-- Every endpoint term is a concrete inverse input. The bound includes
all actual legs and keeps the physical activation weights. -/
theorem actual_endpoint_higher_table_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2*pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        ∀ bodyPool : ℕ, Parameters.bodies parameter ≤ 2*bodyPool →
        (Parameters.legs parameter : ℝ)*activity
          (inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) (actualBodyLaw cutoffScale parameter (beta parameter))
            (pool parameter) bodyPool ((parameter : ℝ)^2))
          (actualEndpointHigherTable cutoffScale parameter (beta parameter) operator) ≤ endpointAggregateConstant cutoffScale/(parameter : ℝ)^2 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually cutoffScale hscale beta pool htypical,
    actual_pair_completion_eventually cutoffScale hscale beta pool htypical,
    actual_inactive_body_pair_total_activity_eventually cutoffScale hscale beta hbeta,
    actual_marked_total_activity_eventually cutoffScale hscale beta hbeta,
    actual_marked_fringe_total_activity_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,htypical,eventually_ge_atTop 2]
    with parameter hi hc hb hm hf hl ht hp
  obtain ⟨operator,hop,hi⟩ := hi
  obtain ⟨other,ho,hpositive,hrhone,hcompletion⟩ := hc
  have heq : other = operator := actualResponse_equiv_unique cutoffScale parameter other operator ho hop
  subst other
  refine ⟨operator,hop,?_⟩
  intro bpool hbpool
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let w := inputWeight primary body (pool parameter) bpool ((parameter : ℝ)^2)
  let rho := v7Activation cutoffScale parameter
  have hw : ∀ seed, 0 ≤ w seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hrho : 0 < rho := activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hrho1 : rho ≤ 1 := activation_le_one _ _ _ _
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hbody := hb primary (pool parameter) bpool hbpool
  have hmarkedRaw := hm primary body hl.1 hl.2.1 (pool parameter) bpool ht.2.2 hbpool
  have hfringeRaw := hf primary body hl.1 (pool parameter) ht.2.2 bpool ((parameter : ℝ)^2)
  have hmarked := (mul_le_mul_of_nonneg_left (hi body bpool ((parameter : ℝ)^2) (sq_nonneg _) (actualMarkedInput cutoffScale parameter (beta parameter)))
    (mul_nonneg (Nat.cast_nonneg _) hrho.le)).trans hmarkedRaw
  have hfringe := (mul_le_mul_of_nonneg_left (hi body bpool ((parameter : ℝ)^2) (sq_nonneg _) (actualMarkedFringeInput cutoffScale parameter (beta parameter)))
    (mul_nonneg (Nat.cast_nonneg _) hrho.le)).trans hfringeRaw
  have hcomp := hcompletion body bpool ((parameter : ℝ)^2)
  have hrates := covariance_pool_rate parameter (pool parameter) hp ht.2.2
  have hrateSq : (Real.sqrt (pool parameter : ℝ))⁻¹ ^2 ≤ 4/(parameter : ℝ)^30 := by
    exact (pow_le_pow_left₀ hrates.1 hrates.2.2 2).trans_eq (by ring)
  have hc0 : 0 ≤ pairResidualMixedConstant cutoffScale+pairReferenceMixedConstant cutoffScale := by
    unfold pairResidualMixedConstant pairReferenceMixedConstant pairNeumannConstant
    positivity
  have hmexact : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs,Parameters.security_eq parameter hp,Nat.cast_pow]
  have hcompletionTotal : (Parameters.legs parameter : ℝ)*w (actualPairCompletionInput cutoffScale parameter (beta parameter) operator) ≤
      64*(pairResidualMixedConstant cutoffScale+pairReferenceMixedConstant cutoffScale)/(parameter : ℝ)^2 := by
    apply (mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg _)).trans
    rw [hmexact]
    calc
      _ ≤ (parameter : ℝ)^30*((4/(parameter : ℝ)^30)*(16*(pairResidualMixedConstant cutoffScale+pairReferenceMixedConstant cutoffScale))/(parameter : ℝ)^2) := by gcongr
      _ = _ := by field_simp; ring
  have htable := actualEndpointHigherTable_activity_le cutoffScale parameter (beta parameter) operator w hw hrho.le hrho1
  have hcost : (Parameters.legs parameter : ℝ)*activity w (actualEndpointHigherTable cutoffScale parameter (beta parameter) operator) ≤
      512*pairNeumannConstant/(parameter : ℝ)^18+
      64*(pairResidualMixedConstant cutoffScale+pairReferenceMixedConstant cutoffScale)/(parameter : ℝ)^2+
      markedAggregateConstant cutoffScale/(parameter : ℝ)^9+markedFringeAggregateConstant/(parameter : ℝ)^31 := by
    have hsmall : 1-rho ≤ 1 := by linarith
    have hdrop := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 0)+w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 1) by exact add_nonneg (hw _) (hw _))
    have htable' : activity w (actualEndpointHigherTable cutoffScale parameter (beta parameter) operator) ≤
        w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 0)+w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 1)+
        rho*(w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 2)+w (actualEndpointSeed cutoffScale parameter (beta parameter) operator 3)) := by
      change _ ≤ _+rho*(_+_) at htable
      linarith
    have hmul := mul_le_mul_of_nonneg_left htable' (Nat.cast_nonneg (Parameters.legs parameter))
    change (Parameters.legs parameter : ℝ)*_ ≤ _ at hmul
    change (Parameters.legs parameter : ℝ)*activity w _ ≤ (Parameters.legs parameter : ℝ)*(
      w (actualInactiveBodyPairInput cutoffScale parameter (beta parameter))+
      w (actualPairCompletionInput cutoffScale parameter (beta parameter) operator)+
      rho*(w (inversePrimarySeed primary body rho operator (actualMarkedInput cutoffScale parameter (beta parameter)))+
        w (inversePrimarySeed primary body rho operator (actualMarkedFringeInput cutoffScale parameter (beta parameter))))) at hmul
    dsimp only [w,primary,body,rho] at hmul
    dsimp only [w,primary,body,rho] at hbody hcompletionTotal hmarked hfringe ⊢
    linear_combination hmul+hbody+hcompletionTotal+hmarked+hfringe
  apply hcost.trans
  have h18 := mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 2 ≤ 18 by decide))
    (show 0 ≤ 512*pairNeumannConstant by norm_num [pairNeumannConstant])
  have h9 := mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 2 ≤ 9 by decide))
    (show 0 ≤ markedAggregateConstant cutoffScale by unfold markedAggregateConstant; positivity)
  have h31 := mul_le_mul_of_nonneg_left (inverse_power_antitone hx (show 2 ≤ 31 by decide))
    (show 0 ≤ markedFringeAggregateConstant by unfold markedFringeAggregateConstant bodyMeanRelativeConstant; positivity)
  unfold endpointAggregateConstant
  simp only [div_eq_mul_inv,one_mul] at h18 h9 h31 ⊢
  linarith

end
end AFT.V7Calibration

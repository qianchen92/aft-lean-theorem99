import CurrentAFT.CurrentPublicCompletion
import CurrentAFT.NumericalAffineTransport
import AFT.FiniteChannelIdentities

/-! # Composing the current finite-bit core and completion errors

The same fixed placement is used for the full public experiment. A failed
core remains failed, and completion uses the inputs stored by the proposal.
-/
namespace CurrentAFT.NumericalPublicCompletion
open AFT ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

theorem completion_joint {Core Charts Edge : Type*} [Fintype Core] [Fintype Charts] [Fintype Edge]
    (coreLaw : FiniteDist Core) (charts : Core → FiniteDist Charts) (edge : FiniteDist Edge) :
    coreLaw.mix (fun core => ((charts core).prod edge).map
      (fun pair => ((core, pair.1), pair.2))) = (FiniteDist.joint coreLaw charts).prod edge := by
  ext output
  rcases output with ⟨⟨core, chart⟩, closing⟩
  simp only [FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.prod_weight,
    Fintype.sum_prod_type, Prod.mk.injEq, FiniteDist.joint_weight]
  simp only [ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, mul_ite, mul_zero]
  exact (mul_assoc _ _ _).symm

def targetCore (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist (Option (CachedCore security)) :=
  ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map
    (coreEquiv security).symm).map some

theorem lift_core_error (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (Option (CachedCore security))) (error : ℝ)
    (hcore : FiniteDist.TVBound (implementation.map (Option.map (coreEquiv security)))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map some) error) :
    FiniteDist.TVBound implementation (targetCore security weight hpositive) error := by
  have h := hcore.map (Option.map (coreEquiv security).symm)
  rw [FiniteDist.map_map] at h
  have hid : (fun result : Option (CachedCore security) =>
      Option.map (coreEquiv security).symm (Option.map (coreEquiv security) result)) = id := by
    funext result
    cases result <;> simp
  have hmap : implementation.map id = implementation := by
    ext point
    exact FiniteDist.map_equiv_weight implementation (Equiv.refl _) point
  rw [hid, hmap] at h
  simpa only [targetCore, FiniteDist.map_map, Option.map_some] using h

theorem target_completed (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    (targetCore security weight hpositive).mix (targetKernel security) =
      (CurrentPublicAffineSample.law security weight hpositive).map some := by
  rw [targetCore, FiniteDist.mix_map, FiniteDist.mix_map]
  change (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).mix
    (fun core => ((CurrentPublicAffineSample.chartsLaw security core).prod (DiffuseProfiles.edgeLaw security)).map
      (fun pair => some ((core, pair.1), pair.2))) = _
  have h := completion_joint (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
    (CurrentPublicAffineSample.chartsLaw security) (DiffuseProfiles.edgeLaw security)
  have hm := congrArg (fun law => law.map some) h
  dsimp only at hm
  rw [FiniteDist.map_mix] at hm
  simp only [FiniteDist.map_map] at hm
  exact hm

theorem completion_tv (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (input : Option (CachedCore security)) :
    FiniteDist.TVBound (kernel security precisionBits drawBits edgeBits input) (targetKernel security input)
      (errorBound security precisionBits drawBits edgeBits/2) := by
  rw [FiniteDist.tvBound_iff_totalVariation_le, FiniteDist.totalVariation_eq_half_l1]
  exact div_le_div_of_nonneg_right (completion_l1 security precisionBits drawBits edgeBits hprecision input) (by norm_num)

theorem implementation_error (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (Option (CachedCore security))) (coreError : ℝ)
    (hcore : FiniteDist.TVBound implementation (targetCore security weight hpositive) coreError) :
    FiniteDist.TVBound (implementation.mix (kernel security precisionBits drawBits edgeBits))
      ((CurrentPublicAffineSample.law security weight hpositive).map some)
      (coreError+errorBound security precisionBits drawBits edgeBits/2) := by
  have hc := hcore.mix (kernel security precisionBits drawBits edgeBits)
  have hh := FiniteDist.TVBound.mix_right (targetCore security weight hpositive)
    (completion_tv security precisionBits drawBits edgeBits hprecision)
  rw [target_completed] at hh
  exact hc.triangle hh

theorem gaussian_error (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (Option (CachedCore security))) (coreError analytic : ℝ)
    (hcore : FiniteDist.TVBound implementation (targetCore security weight hpositive) coreError)
    (hanalytic : (CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic) :
    (NumericalAffineTransport.gaussianOutput security layout
      (implementation.mix (kernel security precisionBits drawBits edgeBits))).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic+coreError+errorBound security precisionBits drawBits edgeBits/2 := by
  have h := NumericalAffineTransport.transport_error security layout weight hpositive
    (implementation.mix (kernel security precisionBits drawBits edgeBits))
    (coreError+errorBound security precisionBits drawBits edgeBits/2) analytic
    (implementation_error security precisionBits drawBits edgeBits hprecision weight hpositive implementation coreError hcore) hanalytic
  exact h.trans_eq (by ring)

end
end CurrentAFT.NumericalPublicCompletion

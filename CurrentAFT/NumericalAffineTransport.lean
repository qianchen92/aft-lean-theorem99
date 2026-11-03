import CurrentAFT.ActualGaussianAccuracy

/-! # Passing a finite public implementation error to the real Gaussian output

The extra `none` branch realizes the integral identity fallback. A numerical
sampler supplies a distribution on these finite public results, independently
of the hidden source. Its total-variation error is paid once, after all public
sampling steps have been composed. This is an implementation bridge, not a
claim that the required finite-bit sampler has already been constructed.
-/
namespace CurrentAFT.NumericalAffineTransport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport CurrentZeroFiber
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

abbrev PublicResult (security : ℕ) := Option (Sample security)

def realizeResult (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) : PublicResult security → Data security
  | none => fallback security
  | some sample => realize security layout sample

def gaussianChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (result : PublicResult security) : FiniteDist (Word security) :=
  hiddenGaussianOutput security (fun input => (FiniteDist.uniform Unit).map
    (fun _ index => ((realizeResult security layout result).eval input index : ZMod (Parameters.modulus security))))

def gaussianOutput (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (distribution : FiniteDist (PublicResult security)) : FiniteDist (Word security) :=
  distribution.mix (gaussianChannel security layout)

theorem ideal_output (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    gaussianOutput security layout ((law security weight hpositive).map some) =
      CurrentAffineTransport.gaussianLaw security layout weight hpositive := by
  rw [gaussianOutput, FiniteDist.mix_map]
  rfl

/-- Every public outcome, including failed rejection and numerical fallback,
has integral data and an exactly invertible residue matrix. -/
theorem every_result_invertible (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (result : PublicResult security) :
    IsUnit ((realizeResult security layout result).matrix.map
      (Int.castRingHom (ZMod (Parameters.modulus security)))) :=
  (realizeResult security layout result).invertible

theorem implementation_error (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (PublicResult security)) (numerical : ℝ)
    (himplementation : FiniteDist.TVBound implementation ((law security weight hpositive).map some) numerical) :
    FiniteDist.TVBound (gaussianOutput security layout implementation)
      (CurrentAffineTransport.gaussianLaw security layout weight hpositive) numerical := by
  have h := himplementation.mix (gaussianChannel security layout)
  change FiniteDist.TVBound (gaussianOutput security layout implementation)
    (gaussianOutput security layout ((law security weight hpositive).map some)) numerical at h
  rw [ideal_output] at h
  exact h

theorem transport_error (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (PublicResult security)) (numerical analytic : ℝ)
    (himplementation : FiniteDist.TVBound implementation ((law security weight hpositive).map some) numerical)
    (hanalytic : (CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation
      (uniformFiber security) ≤ analytic) :
    (gaussianOutput security layout implementation).totalVariation (uniformFiber security) ≤ analytic + numerical := by
  have h := (implementation_error security layout weight hpositive implementation numerical himplementation).triangle
    ((FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr hanalytic)
  exact ((FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp h).trans_eq (add_comm numerical analytic)

end
end CurrentAFT.NumericalAffineTransport

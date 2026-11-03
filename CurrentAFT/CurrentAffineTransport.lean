import CurrentAFT.CurrentPublicAffineSample
import CurrentAFT.CurrentAffineProtectedCarry
import CurrentAFT.CurrentHiddenSourceTransport
import CurrentAFT.CurrentZeroFiber

/-! # Actual Gaussian and protected affine output laws

The complete finite public law is independent of the dimension-many hidden
Gaussian inputs. The protected experiment uses the identical affine data.
-/
namespace CurrentAFT.CurrentAffineTransport
open AFT CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport
  CurrentSourceProtection CurrentSourceLayout CurrentAffineProtectedCarry CurrentZeroFiber
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

def output (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : Fin (Parameters.dimension security) → ℤ) : Word security :=
  fun index => ((realize security layout sample).eval input index : ZMod (Parameters.modulus security))

def endpoint (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (sample : Sample security) (input : Fin (Parameters.dimension security) → ℤ) : Word security :=
  fun vertex => (CurrentAffineLoad.rounding security ((realize security layout sample).eval input) vertex :
    ZMod (Parameters.modulus security))

def gaussianLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => hiddenGaussianOutput security
    (fun input => (FiniteDist.uniform Unit).map (fun _ => output security layout sample input)))

def protectedLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => (hiddenLaw security).map
    (fun input => output security layout sample (sourceEmbedding (hiddenCutoff security) input)))

def protectedEndpointLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) : FiniteDist (Word security) :=
  (law security weight hpositive).mix (fun sample => (hiddenLaw security).map
    (fun input => endpoint security layout sample (sourceEmbedding (hiddenCutoff security) input)))

theorem mix_constant_map {Source Output : Type*} [Fintype Source] [Fintype Output]
    (distribution : FiniteDist Source) (value : Source → Output) :
    distribution.mix (fun source => (FiniteDist.uniform Unit).map (fun _ => value source)) =
      distribution.map value := by
  ext output
  simp [FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.uniform_weight]

theorem gaussian_protected_tv (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound (gaussianLaw security layout weight hpositive)
      (protectedLaw security layout weight hpositive) (budget security) := by
  have h := public_hidden_channel_tv security
    (FiniteDist.joint (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
      (chartsLaw security)) (fun publicDraw closure input => (FiniteDist.uniform Unit).map
        (fun _ => output security layout (publicDraw, closure) input))
  simp_rw [mix_constant_map] at h
  exact h

theorem supported_protected_carry (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (sample : Sample security) (hsample : (law security weight hpositive).weight sample ≠ 0)
    (input : HiddenWord security) :
    (∑ vertex, CurrentAffineLoad.rounding security
      ((realize security layout sample).eval (sourceEmbedding (hiddenCutoff security) input)) vertex /
        Parameters.modulus security : ℤ) = 0 := by
  have hs := support security weight hpositive sample hsample
  rw [realize_on_support security layout weight hpositive sample hsample]
  let word := joinProtected security (input, sample.2)
  have hsplit := (splitWord security).apply_symm_apply
    (sourceEmbedding (hiddenCutoff security) input, sample.2.val)
  have hh : hiddenWord security (sourceEmbedding (cutoff security) word) =
      sourceEmbedding (hiddenCutoff security) input := congrArg Prod.fst hsplit
  have hc : closureScalar security (sourceEmbedding (cutoff security) word) = sample.2.val := congrArg Prod.snd hsplit
  have h := affine_total_carry_zero security layout sample.1.1 hs.1.1 hs.2.1 sample.1.2 hs.2.2 word
  rw [hh, hc] at h
  exact h

theorem protected_pullback (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    (protectedEndpointLaw security layout weight hpositive).map (pullback security) =
      protectedLaw security layout weight hpositive := by
  rw [protectedEndpointLaw, FiniteDist.map_mix]
  apply FiniteDist.mix_congr_support
  intro sample hsample
  rw [FiniteDist.map_map]
  congr 1
  funext input
  exact pullback_rounding security _
    (supported_protected_carry security layout weight hpositive sample hsample input)

theorem protected_fiber_bound (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (error : ℝ)
    (hendpoint : (protectedEndpointLaw security layout weight hpositive).totalVariation
      (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)) ≤ error) :
    (protectedLaw security layout weight hpositive).totalVariation (uniformFiber security) ≤ error := by
  have h := ((FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr hendpoint).map (pullback security)
  rw [protected_pullback, uniform_pullback] at h
  exact (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp h

/-- The full hidden Gaussian source costs one protection budget, after
the genuine carry and uniform-zero-fiber identifications. -/
theorem gaussian_fiber_bound (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (error : ℝ)
    (hendpoint : (protectedEndpointLaw security layout weight hpositive).totalVariation
      (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)) ≤ error) :
    (gaussianLaw security layout weight hpositive).totalVariation (uniformFiber security) ≤ error + budget security := by
  have hp := protected_fiber_bound security layout weight hpositive error hendpoint
  have h := (gaussian_protected_tv security layout weight hpositive).triangle
    ((FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr hp)
  rw [add_comm] at h
  exact (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp h

end
end CurrentAFT.CurrentAffineTransport

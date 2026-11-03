import CurrentAFT.CurrentAffineData
import CurrentAFT.CurrentPublicSupport
import AFT.ConditionalRepair

/-! # A complete positive source-independent public affine experiment

The core, all complete charts, and the finite closing Gaussian edge are
sampled before any hidden source coordinate.  The constructor always
returns integral invertible affine data, including on zero-probability
invalid records through its identity fallback.
-/
namespace CurrentAFT.CurrentPublicAffineSample
open AFT CurrentAffineData CurrentAffineLegCarry AffineFlagCalibration ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean CurrentPublicSupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

def chartsLaw (security : ℕ) (core : Core security) : FiniteDist (Charts security) :=
  FiniteDist.independent (fun leg => completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)

abbrev Sample (security : ℕ) := (Core security × Charts security) × Edge security

def law (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist (Sample security) :=
  (FiniteDist.joint (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
    (chartsLaw security)).prod (DiffuseProfiles.edgeLaw security)

def realize (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (sample : Sample security) :
    Data security := assemble security layout sample.1.1 sample.1.2 sample.2.val

theorem charts_support (security : ℕ) (core : Core security) (charts : Charts security)
    (hweight : (chartsLaw security core).weight charts ≠ 0) (leg : Fin (Parameters.legCount security)) :
    (completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1).weight (charts leg) ≠ 0 := by
  intro hzero
  apply hweight
  exact Finset.prod_eq_zero (Finset.mem_univ leg) hzero

theorem support (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (sample : Sample security) (hweight : (law security weight hpositive).weight sample ≠ 0) :
    Valid security sample.1.1 sample.1.2 ∧ SafeCore security sample.1.1 ∧
      ∀ leg, (completionLaw security (sample.1.1.controls (.inl leg)).1
        (sample.1.1.legs leg).1).weight (sample.1.2 leg) ≠ 0 := by
  change ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).weight sample.1.1 *
    (chartsLaw security sample.1.1).weight sample.1.2) * (DiffuseProfiles.edgeLaw security).weight sample.2 ≠ 0 at hweight
  have hcore := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hweight).1).1
  have hcharts := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hweight).1).2
  have hs := positive_safe security weight hpositive sample.1.1 hcore
  have hc := charts_support security sample.1.1 sample.1.2 hcharts
  refine ⟨⟨hs.1, ?_⟩, hs.2, hc⟩
  intro leg
  exact supported_chart_scale security _ _ _ (hc leg)

theorem realize_on_support (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (sample : Sample security) (hweight : (law security weight hpositive).weight sample ≠ 0) :
    realize security layout sample = assembled security layout sample.1.1 sample.1.2 sample.2.val
      (support security weight hpositive sample hweight).1 :=
  assemble_valid security layout sample.1.1 sample.1.2 sample.2.val _

/-- Exact uniformity and independence of the transformed public matrix
for this actual completed public sampler, for any modular source law. -/
theorem public_matrix_independent (security : ℕ) {Column : Type*} [Fintype Column]
    (layout : RoleIndex security ≃ BodyIndex security) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (source : FiniteDist (ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))) :
    ((law security weight hpositive).prod source).mix (fun draw =>
      (FiniteDist.uniform (Column → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).map
        (fun matrix => (((realize security layout draw.1).reduced).columnsEquiv Column matrix,
          ((realize security layout draw.1).reduced).eval draw.2))) =
      (FiniteDist.uniform (Column → ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))).prod
        (transportedLaw (law security weight hpositive) (fun sample => (realize security layout sample).reduced) source) :=
  AFT.public_matrix_error_independent (R := ZMod (Parameters.modulus security))
    (V := ModularCoordinates (Parameters.dimension security) (Parameters.modulus security))
    (Column := Column) (law security weight hpositive)
    (fun sample => (realize security layout sample).reduced) source

end
end CurrentAFT.CurrentPublicAffineSample

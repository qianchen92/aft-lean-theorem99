import CurrentAFT.CurrentAffineGeometry
import CurrentAFT.CurrentAffineLegCarry
import CurrentAFT.AffinePublicLaw

/-! # Actual integral public affine data, including an always-legal fallback -/
namespace CurrentAFT.CurrentAffineData
open AFT CurrentAffineGeometry CurrentAffineLegCarry ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean AffineFlagCalibration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

structure Data (security : ℕ) where
  matrix : Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ
  offset : Fin (Parameters.dimension security) → ℤ
  invertible : IsUnit (matrix.map (Int.castRingHom (ZMod (Parameters.modulus security))))

def Data.eval {security : ℕ} (data : Data security) (input : Fin (Parameters.dimension security) → ℤ) :=
  data.matrix.mulVec input + data.offset

def Data.reduced {security : ℕ} (data : Data security) :
    ModularAffinePair (Parameters.dimension security) (Parameters.modulus security) where
  linear := (data.matrix.map (Int.castRingHom (ZMod (Parameters.modulus security)))).toLinearEquiv
    (Pi.basisFun _ _) ((Matrix.isUnit_iff_isUnit_det _).mp data.invertible)
  offset := fun index => (data.offset index : ZMod (Parameters.modulus security))

theorem Data.reduced_eval {security : ℕ} (data : Data security)
    (input : Fin (Parameters.dimension security) → ℤ) :
    data.reduced.eval (fun index => (input index : ZMod (Parameters.modulus security))) =
      fun index => (data.eval input index : ZMod (Parameters.modulus security)) := by
  unfold Data.reduced AffinePair.eval
  simp only [Matrix.toLinearEquiv_apply]
  change (data.matrix.map (Int.castRingHom (ZMod (Parameters.modulus security)))).mulVec
    (fun index => (input index : ZMod (Parameters.modulus security))) +
      (fun index => (data.offset index : ZMod (Parameters.modulus security))) = _
  funext index
  have hm := RingHom.map_mulVec (Int.castRingHom (ZMod (Parameters.modulus security))) data.matrix input index
  change _ + _ = ((data.matrix.mulVec input index + data.offset index : ℤ) : ZMod (Parameters.modulus security))
  rw [Int.cast_add]
  exact congrArg (fun value => value + (data.offset index : ZMod (Parameters.modulus security))) hm.symm

def fallback (security : ℕ) : Data security where
  matrix := 1
  offset := 0
  invertible := by simp

abbrev Charts (security : ℕ) := Fin (Parameters.legCount security) → PublicChart security

def scales (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.2.1.val

def shears (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.2.2.val

def intercepts (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.1.val

def Valid (security : ℕ) (core : Core security) (charts : Charts security) : Prop :=
  publicCharge security core ∧ ∀ leg, (charts leg).2.2.1 ≠ 0

def assembled (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (charts : Charts security) (closure : ℤ) (hvalid : Valid security core charts) : Data security where
  matrix := CurrentAffineGeometry.matrix security layout core (scales security charts) (shears security charts)
  offset := CurrentAffineGeometry.offset security layout core (intercepts security charts) closure hvalid.1
  invertible := CurrentAffineGeometry.matrix_invertible security layout core _ _ (by
    intro leg
    simpa [scales] using hvalid.2 leg)

/-- This constructor takes only public data. Every branch returns integral
affine data whose reduction is invertible. -/
def assemble (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (charts : Charts security) (closure : ℤ) : Data security :=
  if hvalid : Valid security core charts then assembled security layout core charts closure hvalid
  else fallback security

theorem assemble_valid (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (charts : Charts security) (closure : ℤ) (hvalid : Valid security core charts) :
    assemble security layout core charts closure = assembled security layout core charts closure hvalid := by
  simp only [assemble, dif_pos hvalid]

theorem fallback_eval (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    (fallback security).eval input = input := by
  simp [Data.eval, fallback]

theorem supported_chart_scale (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (chart : PublicChart security)
    (hchart : (completionLaw security primary seed).weight chart ≠ 0) : chart.2.2.1 ≠ 0 :=
  currentLaw_nonzero_scale security (ActualPublicLegCharge.publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using ActualPublicLegCharge.publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num) chart hchart

end
end CurrentAFT.CurrentAffineData

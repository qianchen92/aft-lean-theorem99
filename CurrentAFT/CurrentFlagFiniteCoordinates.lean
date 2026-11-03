import CurrentAFT.CurrentFlagFiniteResponse
import AFT.FiniteChartSemantics

/-! The finite-coordinate repair uses the actual executable feature and palette arrays. -/

namespace CurrentAFT.CurrentFlagFiniteCoordinates

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagFiniteResponse CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

variable (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]

omit [Fact modulus.Prime] in
theorem palettes_eq (baseline : ℤ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    finiteProtectedPalettes cutoff modulus 1 baseline index =
      (protectedPalettes cutoff modulus 1 baseline (finiteInputEquiv cutoff index)).map
        (ZMod.finEquiv modulus).toEquiv.symm.toEmbedding := by
  ext color
  rw [Finset.mem_map_equiv]
  exact finiteProtectedPalettes_field cutoff modulus 1 baseline index color

theorem safe_equiv (baseline : ℤ) (point : Fin (modulus * (modulus * modulus))) :
    point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline) ↔
    affineSafe (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline)
      (finiteChartEquiv modulus point) := by
  have hscale : finiteAffineScale modulus point ≠ 0 ↔ (finiteChartEquiv modulus point).2.1 ≠ 0 := by
    simp only [finiteAffineScale, ne_eq, RingEquiv.symm_apply_eq]
    rw [map_zero]
  simp only [finiteMarkedSafe, Finset.mem_filter, Finset.mem_univ, true_and, affineSafe, legalChart,
    Finset.mem_erase, and_true]
  rw [hscale]
  apply and_congr_right
  intro _
  constructor
  · intro h input
    let index := (finiteInputEquiv cutoff).symm input
    have hh := (finiteProtectedPalettes_field cutoff modulus 1 baseline index _).mp (h index)
    rw [finiteProtectedFeatures_field] at hh
    simpa only [index, Equiv.apply_symm_apply, affineFeatures, protectedInputs] using hh
  · intro h index
    apply (finiteProtectedPalettes_field cutoff modulus 1 baseline index _).mpr
    rw [finiteProtectedFeatures_field]
    exact h (finiteInputEquiv cutoff index)

omit [NeZero modulus] in
theorem first_zero (hsize : 2 * cutoff < modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0 ↔
      ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  let value := (finiteInputEquiv cutoff index).1
  let zero := GaussianSource.windowZero cutoff
  constructor
  · intro hc
    have hz : value = zero := window_cast_injective cutoff modulus hsize
      (by simpa only [zero, GaussianSource.windowZero, Int.cast_zero] using hc)
    exact congrArg Subtype.val hz
  · intro hc
    rw [hc, Int.cast_zero]

def nativeRegular (baseline : ℤ) (mark : ZMod modulus) (atom : ℚ) (steps : ℕ) :
    Fin (modulus * (modulus * modulus)) → ℚ :=
  regularIterate (finiteProtectedFeatures cutoff modulus) (finiteProtectedPalettes cutoff modulus 1 baseline)
    (fun index => (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0)
    (fun point => point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline)) atom
    (chartSpikeProgram (modulus * (modulus * modulus))
      (fiber (finiteChartEquiv modulus) (protectedInputs cutoff modulus)
        (protectedPalettes cutoff modulus 1 baseline) mark)) steps

theorem nativeRegular_eq (baseline : ℤ) (mark : ZMod modulus) (atom : ℚ) (steps : ℕ) :
    nativeRegular cutoff modulus baseline mark atom steps =
      finiteRegular (finiteChartEquiv modulus) (ZMod.finEquiv modulus).toEquiv (finiteInputEquiv cutoff)
        (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline) mark atom steps := by
  have ha : finiteProtectedPalettes cutoff modulus 1 baseline =
      fun index => (protectedPalettes cutoff modulus 1 baseline (finiteInputEquiv cutoff index)).map
        (ZMod.finEquiv modulus).toEquiv.symm.toEmbedding := funext (palettes_eq cutoff modulus baseline)
  have hs : (fun point => point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline)) =
      (fun point => affineSafe (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline)
        (finiteChartEquiv modulus point)) := funext (fun point => propext (safe_equiv cutoff modulus baseline point))
  unfold nativeRegular finiteRegular
  rw [hs, ha]
  rfl

end
end CurrentAFT.CurrentFlagFiniteCoordinates

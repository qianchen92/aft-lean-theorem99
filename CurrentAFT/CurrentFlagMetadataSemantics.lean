import CurrentAFT.CurrentFlagBinaryMetadata
import CurrentAFT.CurrentFlagFiniteCoordinates

/-! The generated marked mask is exactly the canonical scale-only chart fiber. -/

namespace CurrentAFT.CurrentFlagMetadataSemantics

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagMarkedArray CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000

theorem boundary_one : signedValue false [true] = 1 := by decide

theorem fiber_exact (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (hsize : 2 * cutoff < modulus) (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) :
    maskSet (build cutoff modulus false baselineSign [true] baseline mark).value.fiber =
      fiber (finiteChartEquiv modulus) (protectedInputs cutoff modulus)
        (protectedPalettes cutoff modulus 1 (signedValue baselineSign baseline)) ((ZMod.finEquiv modulus) mark) := by
  ext point
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [build_fiber, mem_fiber]
  have hc := coordinates_field modulus point
  have hb : (coordinates modulus point).value.1 = mark ↔
      (finiteChartEquiv modulus point).1 = (ZMod.finEquiv modulus) mark := by
    have hfirst := congrArg Prod.fst hc
    rw [← hfirst]
    exact (ZMod.finEquiv modulus).injective.eq_iff.symm
  have ht : (coordinates modulus point).value.2.2 = 0 ↔ (finiteChartEquiv modulus point).2.2 = 0 := by
    have hlast := congrArg (fun word => word.2.2) hc
    change (ZMod.finEquiv modulus) (coordinates modulus point).value.2.2 =
      (finiteChartEquiv modulus point).2.2 at hlast
    rw [← hlast]
    exact (map_eq_zero_iff (ZMod.finEquiv modulus) (ZMod.finEquiv modulus).injective).symm
  have hs : finiteAffineScale modulus point ≠ 0 ↔ (finiteChartEquiv modulus point).2.1 ≠ 0 := by
    simp only [finiteAffineScale, ne_eq, RingEquiv.symm_apply_eq]
    rw [map_zero]
  rw [hb, ht, hs, boundary_one]
  constructor
  · rintro ⟨hb, hs, ht, hall⟩
    refine ⟨hb, ht, hs, ?_⟩
    intro input hfirst
    let index := (finiteInputEquiv cutoff).symm input
    have hi : ((finiteInputEquiv cutoff index).1 : ℤ) ≠ 0 := by
      intro hz
      apply hfirst
      change (((input.1 : ℤ) : ZMod modulus)) = 0
      have hz' : (input.1 : ℤ) = 0 := by simpa only [index, Equiv.apply_symm_apply] using hz
      rw [hz', Int.cast_zero]
    have hallowed := (finiteProtectedPalettes_field cutoff modulus 1
      (signedValue baselineSign baseline) index _).mp (hall index hi)
    rw [finiteProtectedFeatures_field] at hallowed
    simpa only [index, Equiv.apply_symm_apply, feature, hb, ht, zero_mul, add_zero, protectedInputs] using hallowed
  · rintro ⟨hb, ht, hs, hall⟩
    refine ⟨hb, hs, ht, ?_⟩
    intro index hi
    apply (finiteProtectedPalettes_field cutoff modulus 1 (signedValue baselineSign baseline) index _).mpr
    rw [finiteProtectedFeatures_field]
    have hfirst : (protectedInputs cutoff modulus (finiteInputEquiv cutoff index)).1 ≠ 0 := by
      exact (not_congr (first_zero cutoff modulus hsize index)).mpr hi
    have hallowed := hall (finiteInputEquiv cutoff index) hfirst
    simpa only [feature, hb, ht, zero_mul, add_zero, protectedInputs] using hallowed

end
end CurrentAFT.CurrentFlagMetadataSemantics

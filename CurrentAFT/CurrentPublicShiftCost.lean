import CurrentAFT.CurrentPublicShiftProgram

/-! Uniform current-parameter work and length bounds for public shifts. -/

namespace CurrentAFT.CurrentPublicShiftProgram

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 500000

theorem programWork_mono {q q' a a' c c' i i' x x' y y' : ℕ}
    (hq : q ≤ q') (ha : a ≤ a') (hc : c ≤ c') (hi : i ≤ i') (hx : x ≤ x') (hy : y ≤ y') :
    programWork q a c i x y ≤ programWork q' a' c' i' x' y' := by
  unfold programWork
  gcongr

theorem program_length (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (program modulus width primary index coin blurFirst blurSecond).value.digits.length ≤
      width + index + blurFirst.natAbs + blurSecond.natAbs + 2 := by
  have hfirst := encode_length blurFirst
  have hsecond := encode_length blurSecond
  have hsub := IntegerBits.subtract_length (encode blurFirst).value (encode blurSecond).value
  have hbits : (canonicalCounter (width + index)).digits.length ≤ width + index := by
    rw [canonicalCounter_length]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))
  have hl := IntegerBits.add_length
    (⟨!(direction modulus primary coin).value, (canonicalCounter (width + index)).digits⟩ : IntegerBits)
    (IntegerBits.subtract (encode blurFirst).value (encode blurSecond).value).value
  change _ ≤ max (canonicalCounter (width + index)).digits.length
    (IntegerBits.subtract (encode blurFirst).value (encode blurSecond).value).value.digits.length + 1 at hl
  simp only [program, addCounter_value]
  omega

theorem edge_size (security : ℕ) (value : GaussianSource.Window (DiffuseProfiles.edgeCutoff security)) :
    value.val.natAbs ≤ (security + 2) ^ 2 := by
  have hedge : DiffuseProfiles.edgeCutoff security ≤ (security + 2) ^ 2 := by
    exact (Nat.div_le_self (Parameters.sourceCutoff security - 1) 2).trans
      (by simpa only [Parameters.sourceCutoff, Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have hv := Finset.mem_Icc.mp value.property
  have he : (DiffuseProfiles.edgeCutoff security : ℤ) ≤ (((security + 2) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hedge
  have ha : (value.val.natAbs : ℤ) ≤ (((security + 2) ^ 2 : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨by omega, by omega⟩
  exact_mod_cast ha

def workBound (security : ℕ) : ℕ :=
  let base := security + 2
  let q := 131072 * base ^ 64
  let width := base ^ 48
  let cutoff := base ^ 2
  PublicParameterProgram.workBound security + (2 * security + 1) + powerCounterWork base 48 +
    programWork q width q width cutoff cutoff + 3

theorem current_work (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) :
    (current security primary seed).work ≤ workBound security := by
  let q := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 48
  let result := program q.count width.count primary.val seed.anchorIndex.val seed.coin seed.blur.1.val seed.blur.2.val
  have hq : q.count ≤ 131072 * (security + 2) ^ 64 := by
    rw [show q.count = Parameters.modulus security from PublicParameterProgram.modulus_value security]
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hw : width.count = (security + 2) ^ 48 := by
    simp only [width, base, powerCounter_value, addCounter_value]
  have hc : primary.val ≤ 131072 * (security + 2) ^ 64 := by
    apply primary.isLt.le.trans
    simpa only [q, PublicParameterProgram.modulus_value] using hq
  have hi : seed.anchorIndex.val ≤ (security + 2) ^ 48 := by
    have h := seed.anchorIndex.isLt.le
    simpa only [Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul] using h
  have hedge : DiffuseProfiles.edgeCutoff security ≤ (security + 2) ^ 2 := by
    exact (Nat.div_le_self (Parameters.sourceCutoff security - 1) 2).trans
      (by simpa only [Parameters.sourceCutoff, Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have hblur (value : GaussianSource.Window (DiffuseProfiles.edgeCutoff security)) : value.val.natAbs ≤ (security + 2) ^ 2 := by
    have hv := Finset.mem_Icc.mp value.property
    have he : (DiffuseProfiles.edgeCutoff security : ℤ) ≤ (((security + 2) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hedge
    have ha : (value.val.natAbs : ℤ) ≤ (((security + 2) ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr ⟨by omega, by omega⟩
    exact_mod_cast ha
  have hp := (program_work q.count width.count primary.val seed.anchorIndex.val seed.coin seed.blur.1.val seed.blur.2.val).trans
    (programWork_mono hq hw.le hc hi (hblur seed.blur.1) (hblur seed.blur.2))
  have hqw := PublicParameterProgram.modulus_work security
  have hbw := addCounter_work security 2
  have hww : width.work ≤ powerCounterWork (security + 2) 48 := by
    have h := powerCounter_work base.count 48
    change width.work ≤ powerCounterWork base.count 48 at h
    rw [show base.count = security + 2 from addCounter_value security 2] at h
    exact h
  change result.work ≤ _ at hp
  change q.work ≤ _ at hqw
  change base.work = _ at hbw
  change q.work + base.work + width.work + result.work + 3 ≤ _
  change _ ≤ PublicParameterProgram.workBound security + (2 * security + 1) + powerCounterWork (security + 2) 48 +
    programWork (131072 * (security + 2) ^ 64) ((security + 2) ^ 48)
      (131072 * (security + 2) ^ 64) ((security + 2) ^ 48) ((security + 2) ^ 2) ((security + 2) ^ 2) + 3
  omega

theorem current_length (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) :
    (current security primary seed).value.digits.length ≤ 2 * (security + 2) ^ 48 + 2 * (security + 2) ^ 2 + 2 := by
  have h := program_length (PublicParameterProgram.modulus security).count
    (powerCounter (addCounter security 2).count 48).count primary.val seed.anchorIndex.val seed.coin seed.blur.1.val seed.blur.2.val
  change (current security primary seed).value.digits.length ≤
    (powerCounter (addCounter security 2).count 48).count + seed.anchorIndex.val + seed.blur.1.val.natAbs + seed.blur.2.val.natAbs + 2 at h
  rw [powerCounter_value, addCounter_value] at h
  have hi : seed.anchorIndex.val ≤ (security + 2) ^ 48 := by
    simpa only [Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul] using seed.anchorIndex.isLt.le
  have hfirst := edge_size security seed.blur.1
  have hsecond := edge_size security seed.blur.2
  omega

end CurrentAFT.CurrentPublicShiftProgram

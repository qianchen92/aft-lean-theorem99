import AFT.TrimmedPairInput
import AFT.V7PairCertificateParameters

/-! # All fixed fibers of the actual fifteen-term safe pair certificate -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open SafeConvolution

attribute [local instance] actualModulusNeZero

def pairNeumannConstant : ℝ := 32767

theorem pairNeumannConstant_sum : (∑ i ∈ Finset.range 15, (2 : ℝ) ^ i) = pairNeumannConstant := by
  norm_num [Finset.sum_range_succ, pairNeumannConstant]

theorem pair_row_denominator (parameter q denominator : ℝ) (hp : 0 < parameter) (hq : 0 < q)
    (hd : q / 2 ≤ denominator) :
    Real.sqrt (1 / (parameter ^ 32 * denominator ^ 2)) ≤ 2 / (q * parameter ^ 16) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  calc
    _ ≤ 1 / (parameter ^ 32 * (q / 2) ^ 2) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd 2) (by positivity))
    _ = _ := by field_simp

/-- The complete finite body input and its residual have both fixed-endpoint
bounds and a pointwise bound, at the true public V7 parameters. -/
theorem actual_pair_input_fibers_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter : ℕ in atTop,
      let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
      let seed := actualPairCoreSeed parameter 14 mass
      let input := actualCompactRootInput parameter 14 seed
      let image := convolution (actualRootPair parameter).weight input
      let target := uniformCanonical (fun color => mass color.1 color.2)
      let row := 4 * pairNeumannConstant / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 16)
      let height := 8 * pairNeumannConstant / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 32)
      let errorRow := 4 * (pairNeumannConstant + 1) / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 16)
      let errorHeight := 8 * (pairNeumannConstant + 1) / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 32)
      RowBound row input ∧ RowBound row (fun point => input point.swap) ∧ SupBound height input ∧
      RowBound errorRow (image - target) ∧ RowBound errorRow (fun point => (image - target) point.swap) ∧
      SupBound errorHeight (image - target) := by
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary
    (hphysical.mono fun _ h => h.1)
  filter_upwards [hphysical, hclear, pairCore_nonempty_eventually 14, eventually_ge_atTop 2]
    with parameter hs hc hne hp
  have hparameter : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp]
    positivity
  have hden : (Parameters.modulus parameter : ℝ) / 2 ≤ Parameters.modulus parameter -
      2 * boundary parameter - 3 * Parameters.anchorWidth parameter - legCutoff cutoffScale parameter := by
    have hh : (2 : ℝ) * (3 * Parameters.anchorWidth parameter + 2 * boundary parameter +
      legCutoff cutoffScale parameter) ≤ Parameters.modulus parameter := by exact_mod_cast hc.2
    linarith
  have hstrict : 2 * boundary parameter + 3 * (Parameters.anchorWidth parameter : ℤ) +
      legCutoff cutoffScale parameter < Parameters.modulus parameter := by
    have hq' : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    have hh := hc.2
    omega
  have hraw := TrimmedSlice.mixedPair_input_bounds (Parameters.modulus parameter) (boundary parameter)
    (3 * Parameters.anchorWidth parameter) (legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter)
    hw (starts parameter) (sources parameter) (sourceLaw parameter) hs.1.1 hs.2.1 hs.2.2 hstrict
  dsimp only at hraw
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hraw
  have hrow := pair_row_denominator (parameter : ℝ) (Parameters.modulus parameter)
    (Parameters.modulus parameter - 2 * boundary parameter - 3 * Parameters.anchorWidth parameter - legCutoff cutoffScale parameter)
    hparameter hq hden
  have hheight : 1 / ((Parameters.anchorWidth parameter : ℝ) *
      (Parameters.modulus parameter - 2 * boundary parameter - 3 * Parameters.anchorWidth parameter - legCutoff cutoffScale parameter)) ≤
      2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 32) := by
    calc
      _ ≤ 1 / ((Parameters.anchorWidth parameter : ℝ) * ((Parameters.modulus parameter : ℝ) / 2)) :=
        one_div_le_one_div_of_le (by exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hw) (by positivity))
          (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _))
      _ = _ := by simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]; ring
  have hrow' : RowBound (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 16))
      (fun point => TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter) point.1 point.2) := by
    intro first
    exact (hraw.1 first).trans (by simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow] using hrow)
  have hsup' : SupBound (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 32))
      (fun point : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
        TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
          (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter) point.1 point.2) :=
    fun point => (hraw.2 point).trans hheight
  have hcol' : RowBound (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 16))
      (fun point => TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter) point.2 point.1) := by
    simpa only [TrimmedSlice.mixedPair_symmetric] using hrow'
  have hh := compact_pair_fiber_bounds (pairCore parameter 14) hne _ _ _ hrow' hsup'
    (actualRootPair parameter) (actualCompactBox parameter) 14
  have hk := compact_pair_column_bounds (pairCore parameter 14) hne _ _ _ hcol' hsup'
    (actualRootPair parameter) (actualCompactBox parameter) 14
  dsimp only at hh hk ⊢
  rw [pairNeumannConstant_sum] at hh hk
  have hroweq : 2 * pairNeumannConstant * (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16)) =
      4 * pairNeumannConstant / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16) := by ring
  have hsupeq : 4 * pairNeumannConstant * (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32)) =
      8 * pairNeumannConstant / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32) := by ring
  have heroweq : 2 * (pairNeumannConstant+1) * (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16)) =
      4 * (pairNeumannConstant+1) / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^16) := by ring
  have hesupeq : 4 * (pairNeumannConstant+1) * (2 / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32)) =
      8 * (pairNeumannConstant+1) / ((Parameters.modulus parameter : ℝ) * (parameter : ℝ)^32) := by ring
  rw [hroweq, hsupeq, heroweq, hesupeq] at hh
  rw [hroweq, heroweq] at hk
  exact ⟨hh.1, hk.1, hh.2.1, hh.2.2.1, hk.2, hh.2.2.2⟩

end AFT.GaussianSource

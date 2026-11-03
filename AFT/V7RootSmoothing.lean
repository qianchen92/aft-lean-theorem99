import AFT.CanonicalConvolution
import AFT.BodyBlurParameters

/-! # Finite Neumann smoothing instantiated at the actual V7 root parameters -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open AFT.SafeConvolution

noncomputable section

local instance actualModulusNeZero (parameter : ℕ) : NeZero (Parameters.modulus parameter) :=
  ⟨(Parameters.modulus_prime parameter).ne_zero⟩

def paletteEmbedding (parameter : ℕ) : ℤ →+ Fin (Parameters.modulus parameter) :=
  (ZMod.finEquiv (Parameters.modulus parameter)).symm.toAddEquiv.toAddMonoidHom.comp (Int.castAddHom _) 

def independentRootPair (parameter : ℕ) :
    FiniteDist (Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)).prod
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter))

def actualRootPair (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
  (independentRootPair parameter).map (fun sample => (paletteEmbedding parameter (sample.1 : ℤ), paletteEmbedding parameter (sample.2 : ℤ)))

def actualCompactBox (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
  boxDistribution (paletteEmbedding parameter) (-(parameter ^ 3 : ℕ)) (2 * parameter ^ 3 + 1) (by omega)

def actualCompactRootInput (parameter depth : ℕ)
    (seed : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ) :=
  compactRootInput (actualRootPair parameter) (actualCompactBox parameter) depth seed

/-- The source displacement budget is proved on the actual clipped
conditional-root sample space. -/
theorem independentRootPair_shift_bound (parameter : ℕ)
    (sample : Window (v7RootCutoff parameter) × Window (v7RootCutoff parameter)) :
    ((sample.1 : ℤ).natAbs : ℝ) + ((sample.2 : ℤ).natAbs : ℝ) ≤ 6 * (parameter : ℝ) ^ 2 := by
  have hfirst := Finset.mem_Icc.mp sample.1.property
  have hsecond := Finset.mem_Icc.mp sample.2.property
  have h1 : (sample.1 : ℤ).natAbs ≤ v7RootCutoff parameter := by
    exact_mod_cast (show ((sample.1 : ℤ).natAbs : ℤ) ≤ (v7RootCutoff parameter : ℤ) by
      rw [Int.natCast_natAbs]; exact abs_le.mpr hfirst)
  have h2 : (sample.2 : ℤ).natAbs ≤ v7RootCutoff parameter := by
    exact_mod_cast (show ((sample.2 : ℤ).natAbs : ℤ) ≤ (v7RootCutoff parameter : ℤ) by
      rw [Int.natCast_natAbs]; exact abs_le.mpr hsecond)
  have hh : (sample.1 : ℤ).natAbs + (sample.2 : ℤ).natAbs ≤ 6 * parameter ^ 2 := by
    unfold v7RootCutoff at h1 h2
    omega
  exact_mod_cast hh

/-- Each actual Neumann step gains a factor at most 12/lambda. This is
already specialized to the real root law, q(lambda), and the centered
compact box of radius lambda^3. -/
theorem actualCompactRootInput_residual_L2_le (parameter depth : ℕ) (hp : 0 < parameter)
    (seed : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ) :
    countingL2 (convolution (actualRootPair parameter).weight (actualCompactRootInput parameter depth seed) -
      (convolution (actualCompactBox parameter).weight ^ (depth + 1)) seed) ≤
      (12 / (parameter : ℝ)) ^ (depth + 1) * countingL2 seed := by
  have hh := box_compactRootInput_residual_L2_le (paletteEmbedding parameter)
    (-(parameter ^ 3 : ℕ)) (2 * parameter ^ 3 + 1) (by omega) (independentRootPair parameter)
    (fun sample => (sample.1 : ℤ)) (fun sample => (sample.2 : ℤ)) (6 * (parameter : ℝ) ^ 2)
    (by positivity) (independentRootPair_shift_bound parameter) depth seed
  dsimp only at hh
  have hc : 2 * (6 * (parameter : ℝ) ^ 2) / (2 * parameter ^ 3 + 1 : ℕ) ≤ 12 / (parameter : ℝ) := by
    have hp' : 0 < (parameter : ℝ) := by exact_mod_cast hp
    apply (div_le_div_iff₀ (by positivity) hp').mpr
    push_cast
    nlinarith [pow_nonneg hp'.le 3]
  exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc _) (countingL2_nonneg seed))

theorem actualCompactRootInput_canonical (parameter depth : ℕ)
    (seed : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ)
    (hseed : PairCanonical seed) : PairCanonical (actualCompactRootInput parameter depth seed) :=
  compactRootInput_pairCanonical _ _ _ _ hseed

end
end AFT.GaussianSource

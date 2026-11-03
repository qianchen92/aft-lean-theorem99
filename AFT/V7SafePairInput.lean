import AFT.ConvolutionSupport
import AFT.V7RootSmoothing
import AFT.CoreProjectionEnergy

/-! # Actual canonical, safely supported finite root inputs for pair kernels -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open AFT.SafeConvolution

noncomputable section

attribute [local instance] actualModulusNeZero

theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus] (color : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The palette embedding agrees with the original integer color whenever
the reserved margin places that integer inside the palette. -/
theorem paletteEmbedding_val (parameter : ℕ) (color : ℤ) (h0 : 0 ≤ color)
    (hq : color < Parameters.modulus parameter) :
    ((paletteEmbedding parameter color).val : ℤ) = color := by
  change (((ZMod.finEquiv (Parameters.modulus parameter)).symm (color : ZMod (Parameters.modulus parameter))).val : ℤ) = color
  rw [finEquiv_symm_val, ZMod.val_intCast, Int.emod_eq_of_lt h0 hq]

theorem paletteEmbedding_color (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    paletteEmbedding parameter color.val = color := by
  apply Fin.ext
  exact_mod_cast paletteEmbedding_val parameter color.val (by positivity) (by exact_mod_cast color.isLt)

def pairCoreDepth (parameter depth : ℕ) : ℕ :=
  Parameters.safeMargin parameter + (depth + 1) * parameter ^ 3 + depth * v7RootCutoff parameter

def pairCore (parameter depth : ℕ) : Finset (Fin (Parameters.modulus parameter)) :=
  TrimmedSlice.paletteSlice (Parameters.modulus parameter) (pairCoreDepth parameter depth) 0

def actualPairCoreSeed (parameter depth : ℕ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ) :
    Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
  fun color => SafePair.coreSeed (pairCore parameter depth) mass color.1 color.2

theorem actualRootPair_supported (parameter : ℕ) :
    SupportedInBox (paletteEmbedding parameter) (-(v7RootCutoff parameter : ℤ)) (v7RootCutoff parameter)
      (actualRootPair parameter).weight := by
  apply source_supportBox
  intro sample
  exact ⟨abs_le.mpr (Finset.mem_Icc.mp sample.1.property), abs_le.mpr (Finset.mem_Icc.mp sample.2.property)⟩

theorem actualPairCoreSeed_supported (parameter depth : ℕ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ) :
    SupportedInBox (paletteEmbedding parameter) (pairCoreDepth parameter depth)
      ((Parameters.modulus parameter : ℤ) - pairCoreDepth parameter depth - 1) (actualPairCoreSeed parameter depth mass) := by
  intro color hc
  have hfirst : color.1 ∈ pairCore parameter depth := by
    by_contra hh
    exact hc (SafePair.coreSeed_supported _ _ _ _ (Or.inl hh))
  have hsecond : color.2 ∈ pairCore parameter depth := by
    by_contra hh
    exact hc (SafePair.coreSeed_supported _ _ _ _ (Or.inr hh))
  simp only [pairCore, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, TrimmedSlice.slice, max_self, min_self,
    add_zero, Finset.mem_Ico] at hfirst hsecond
  refine ⟨color.1.val, color.2.val, by omega, by omega, by omega, by omega, ?_⟩
  simp only [paletteEmbedding_color]

theorem actualPairCoreSeed_canonical (parameter depth : ℕ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ)
    (hne : (pairCore parameter depth).Nonempty) : PairCanonical (actualPairCoreSeed parameter depth mass) :=
  SafePair.coreSeed_canonical _ _ hne

/-- Every retained input term has its original integer colors in the safe
center interval. This proves that the auxiliary group convolution has not
introduced any wrap-around input. -/
theorem actualPairInput_safe (parameter depth : ℕ)
    (mass : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ)
    (color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter))
    (hn : actualCompactRootInput parameter depth (actualPairCoreSeed parameter depth mass) color ≠ 0) :
    (Parameters.safeMargin parameter ≤ color.1.val ∧ color.1.val < Parameters.modulus parameter - Parameters.safeMargin parameter) ∧
    (Parameters.safeMargin parameter ≤ color.2.val ∧ color.2.val < Parameters.modulus parameter - Parameters.safeMargin parameter) := by
  have hh := compactRootInput_supportBox (paletteEmbedding parameter)
    (actualRootPair parameter) (actualCompactBox parameter) (v7RootCutoff parameter) (parameter ^ 3 : ℕ)
    (pairCoreDepth parameter depth) ((Parameters.modulus parameter : ℤ) - pairCoreDepth parameter depth - 1)
    (by positivity) (actualRootPair_supported parameter) (box_supportBox _ (parameter ^ 3))
    (actualPairCoreSeed parameter depth mass) (actualPairCoreSeed_supported parameter depth mass) depth
  obtain ⟨first, second, hf, hf', hs, hs', heq⟩ := hh color hn
  have hdepth : (pairCoreDepth parameter depth : ℤ) =
      Parameters.safeMargin parameter + ((depth : ℤ) + 1) * (parameter ^ 3 : ℕ) + depth * (v7RootCutoff parameter : ℤ) := by
    simp only [pairCoreDepth, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [hdepth] at hf hf' hs hs'
  have hf0 : 0 ≤ first := by omega
  have hs0 : 0 ≤ second := by omega
  have hfq : first < Parameters.modulus parameter := by omega
  have hsq : second < Parameters.modulus parameter := by omega
  have hv1 := paletteEmbedding_val parameter first hf0 hfq
  have hv2 := paletteEmbedding_val parameter second hs0 hsq
  rw [heq]
  dsimp only
  omega

/-- For every fixed correction order the actual protected core is nonempty;
its margin uses only O(lambda^3) colors of the lambda^40 palette. -/
theorem pairCore_nonempty_eventually (depth : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, (pairCore parameter depth).Nonempty := by
  filter_upwards [eventually_ge_atTop (max 2 (2 * (21 + 4 * depth)))] with parameter hp
  have hp2 : 2 ≤ parameter := (le_max_left _ _).trans hp
  have hlarge : 2 * (21 + 4 * depth) ≤ parameter := (le_max_right _ _).trans hp
  have hp1 : 1 ≤ parameter := by omega
  have h23 : parameter ^ 2 ≤ parameter ^ 3 := Nat.pow_le_pow_right hp1 (by decide)
  have hbound : pairCoreDepth parameter depth ≤ (21 + 4 * depth) * parameter ^ 3 := by
    unfold pairCoreDepth Parameters.safeMargin v7RootCutoff
    rw [Parameters.security_eq parameter hp2]
    have hcutoff : 3 * parameter ^ 2 - 1 ≤ 3 * parameter ^ 2 := Nat.sub_le _ _
    nlinarith
  have h40 : 2 * pairCoreDepth parameter depth ≤ parameter ^ 40 := by
    calc
      _ ≤ 2 * ((21 + 4 * depth) * parameter ^ 3) := Nat.mul_le_mul_left 2 hbound
      _ ≤ parameter * parameter ^ 3 := by nlinarith
      _ = parameter ^ 4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp1 (by decide)
  have hq := (Parameters.modulus_spec parameter).2.1
  rw [Parameters.security_eq parameter hp2] at hq
  apply TrimmedSlice.paletteSlice_nonempty
  · positivity
  · simp only [abs_zero]
    omega

end
end AFT.GaussianSource

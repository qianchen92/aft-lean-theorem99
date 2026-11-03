import AFT.V7SafePairInput
import AFT.MaskedWindowTranslation

/-! # No-wrap comparison between finite-palette and integer translations -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open AFT.SafeConvolution

noncomputable section

attribute [local instance] actualModulusNeZero

/-- Every palette subtraction is the embedding of the corresponding
integer difference, before choosing any representative. -/
theorem palette_sub_embedding (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) (shift : ℤ) :
    color - paletteEmbedding parameter shift = paletteEmbedding parameter ((color.val : ℤ) - shift) := by
  rw [map_sub, paletteEmbedding_color]

/-- If the translated palette color lies in the reserved core, its original
integer representative underwent exactly the intended shift. -/
theorem palette_sub_val_on_core (parameter : ℕ) (core : ℤ) (shift : ℤ)
    (color : Fin (Parameters.modulus parameter)) (hshift : |shift| ≤ core)
    (hl : core ≤ ((color - paletteEmbedding parameter shift).val : ℤ))
    (hu : ((color - paletteEmbedding parameter shift).val : ℤ) < (Parameters.modulus parameter : ℤ) - core) :
    ((color - paletteEmbedding parameter shift).val : ℤ) = (color.val : ℤ) - shift := by
  let input := color - paletteEmbedding parameter shift
  have hlo : 0 ≤ (input.val : ℤ) + shift := by dsimp [input]; have hh := abs_le.mp hshift; omega
  have hhi : (input.val : ℤ) + shift < Parameters.modulus parameter := by dsimp [input]; have hh := abs_le.mp hshift; omega
  have heq : paletteEmbedding parameter ((input.val : ℤ) + shift) = color := by
    rw [map_add, paletteEmbedding_color]
    dsimp [input]
    abel
  have hh := paletteEmbedding_val parameter ((input.val : ℤ) + shift) hlo hhi
  rw [heq] at hh
  dsimp [input] at hh
  omega

/-- A core-supported integer pair agrees with its finite-palette translated
profile at every output, including outputs whose subtraction wraps. Those
wrapping cases have zero mass on both sides. -/
theorem core_profile_translation_eq (parameter : ℕ) (core : ℤ) (hcore : 0 ≤ core)
    (profile : ℤ → ℤ → ℝ)
    (hsupport : ∀ first second, profile first second ≠ 0 →
      (core ≤ first ∧ first < (Parameters.modulus parameter : ℤ) - core) ∧
      (core ≤ second ∧ second < (Parameters.modulus parameter : ℤ) - core))
    (firstShift secondShift : ℤ) (hfirst : |firstShift| ≤ core) (hsecond : |secondShift| ≤ core)
    (first second : Fin (Parameters.modulus parameter)) :
    profile ((first - paletteEmbedding parameter firstShift).val : ℤ)
      ((second - paletteEmbedding parameter secondShift).val : ℤ) =
        profile ((first.val : ℤ) - firstShift) ((second.val : ℤ) - secondShift) := by
  by_cases hn : profile ((first - paletteEmbedding parameter firstShift).val : ℤ)
      ((second - paletteEmbedding parameter secondShift).val : ℤ) = 0
  · rw [hn]
    symm
    by_contra hneq
    have hh := hsupport _ _ hneq
    have hl1 : 0 ≤ (first.val : ℤ) - firstShift := hcore.trans hh.1.1
    have hu1 : (first.val : ℤ) - firstShift < Parameters.modulus parameter := by linarith [hh.1.2]
    have hl2 : 0 ≤ (second.val : ℤ) - secondShift := hcore.trans hh.2.1
    have hu2 : (second.val : ℤ) - secondShift < Parameters.modulus parameter := by linarith [hh.2.2]
    have hv1 := paletteEmbedding_val parameter ((first.val : ℤ) - firstShift) hl1 hu1
    have hv2 := paletteEmbedding_val parameter ((second.val : ℤ) - secondShift) hl2 hu2
    rw [← palette_sub_embedding] at hv1 hv2
    rw [hv1, hv2] at hn
    exact hneq hn
  · have hh := hsupport _ _ hn
    rw [palette_sub_val_on_core parameter core firstShift first hfirst hh.1.1 hh.1.2,
      palette_sub_val_on_core parameter core secondShift second hsecond hh.2.1 hh.2.2]

end
end AFT.GaussianSource

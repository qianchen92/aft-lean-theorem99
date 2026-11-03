import CurrentAFT.CurrentGaussianBits
import AFT.BinaryFiniteDraw

/-! Current finite Gaussian-window sampling by literal binary table and ticket programs. -/

namespace CurrentAFT.CurrentWindowDraw

open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.RationalRejectionProgram AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

private theorem table_nonneg (security cutoff bits : ℕ) (index : Fin (2 * cutoff + 1)) :
    0 ≤ ((CurrentGaussianBits.table security cutoff bits).data.get index).decode := by
  rw [CurrentGaussianBits.table_value]
  exact windowGaussianWeights_nonneg _ _ _ _

private theorem table_sum (security cutoff bits : ℕ) :
    ∑ index, ((CurrentGaussianBits.table security cutoff bits).data.get index).decode = 1 := by
  simp only [CurrentGaussianBits.table_value]
  exact windowGaussianWeights_sum _ _ _

private theorem draw_congr {count : ℕ} (first second : Fin (count + 1) → ℚ) (heq : first = second)
    (hn : ∀ index, 0 ≤ first index) (hs : ∑ index, first index = 1)
    (hn' : ∀ index, 0 ≤ second index) (hs' : ∑ index, second index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    RationalFiniteQuantization.draw first hn hs bits word = RationalFiniteQuantization.draw second hn' hs' bits word := by
  subst second
  rfl

def draw (security cutoff bits : ℕ) (word : Fin (windowTicketBits cutoff bits) → Fin 2) : CountedValue (Window cutoff) :=
  let weights := CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := binaryRationalDraw weights.data (windowTicketBits cutoff bits) word
  have hi : selected.value < 2 * cutoff + 1 := by
    rw [binaryRationalDraw_value weights.data (table_nonneg security cutoff (bits + 1))
      (table_sum security cutoff (bits + 1))]
    exact Fin.isLt _
  let point := integerDifference selected.value cutoff
  have hp : point.value ∈ Finset.Icc (-(cutoff : ℤ)) cutoff := by
    have hw := (windowIndexEquiv cutoff (⟨selected.value, hi⟩ : Fin (2 * cutoff + 1))).property
    change ((selected.value : ℤ) - cutoff) ∈ Finset.Icc (-(cutoff : ℤ)) cutoff at hw
    simpa only [point, integerDifference_value] using hw
  ⟨⟨point.value, hp⟩, weights.work + selected.work + point.work + 3⟩

theorem draw_value (security cutoff bits : ℕ) (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (draw security cutoff bits word).value = WindowGaussianSampler.draw security cutoff bits word := by
  let weights := CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := binaryRationalDraw weights.data (windowTicketBits cutoff bits) word
  have hw : (fun index => (weights.data.get index).decode) =
      windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff (bits + 1) :=
    funext (CurrentGaussianBits.table_value security cutoff (bits + 1))
  have hs := binaryRationalDraw_value weights.data (table_nonneg security cutoff (bits + 1))
    (table_sum security cutoff (bits + 1)) (windowTicketBits cutoff bits) word
  rw [draw_congr _ _ hw (table_nonneg security cutoff (bits + 1)) (table_sum security cutoff (bits + 1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _) _ _] at hs
  have hi : selected.value = ((windowIndexEquiv cutoff).symm (WindowGaussianSampler.draw security cutoff bits word)).val := by
    simpa only [WindowGaussianSampler.draw, windowGaussianDraw, Equiv.symm_apply_apply] using hs
  apply Subtype.ext
  change (integerDifference selected.value cutoff).value = (WindowGaussianSampler.draw security cutoff bits word).val
  rw [integerDifference_value, hi]
  exact congrArg Subtype.val ((windowIndexEquiv cutoff).apply_symm_apply (WindowGaussianSampler.draw security cutoff bits word))

def workBound (security cutoff bits : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security (bits + 1) +
    binaryRationalDrawWork (2 * cutoff + 1) (500000000 * (CurrentGaussianBits.budget security (bits + 1)) ^ 6)
      (windowTicketBits cutoff bits) + 6 * cutoff + 7

theorem draw_work (security cutoff bits : ℕ) (hcutoff : cutoff ≤ (security + 2) ^ 2)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (draw security cutoff bits word).work ≤ workBound security cutoff bits := by
  let weights := CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := binaryRationalDraw weights.data (windowTicketBits cutoff bits) word
  have hw := CurrentGaussianBits.table_work security cutoff (bits + 1) hcutoff
  have hs := binaryRationalDraw_work weights.data (500000000 * (CurrentGaussianBits.budget security (bits + 1)) ^ 6)
    (windowTicketBits cutoff bits) (CurrentGaussianBits.table_height security cutoff (bits + 1) hcutoff) word
  have hi : selected.value < 2 * cutoff + 1 := by
    rw [binaryRationalDraw_value weights.data (table_nonneg security cutoff (bits + 1))
      (table_sum security cutoff (bits + 1))]
    exact Fin.isLt _
  have hp := integerDifference_work selected.value cutoff
  change weights.work ≤ _ at hw
  change selected.work ≤ _ at hs
  change weights.work + selected.work + (integerDifference selected.value cutoff).work + 3 ≤ _
  unfold workBound
  omega

noncomputable section
open scoped Classical

theorem draw_l1 (security cutoff bits : ℕ) :
    (∑ point, |((FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))).map
      (fun word => (draw security cutoff bits word).value)).weight point -
        (windowGaussian (Parameters.sourceWidth security) cutoff).weight point|) ≤ 1 / (2 : ℝ) ^ bits := by
  simpa only [draw_value] using WindowGaussianSampler.draw_l1 security cutoff bits

end
end CurrentAFT.CurrentWindowDraw

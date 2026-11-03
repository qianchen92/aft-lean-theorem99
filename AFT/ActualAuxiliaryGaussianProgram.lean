import AFT.ActualLegCutoffProgram
import AFT.RationalWindowTickets
import AFT.BodyBlur

/-! # Executable actual leg and queue Gaussian sources

The cutoff constant is a natural number. Both leg cutoffs and Gaussian
weights are computed from integers and rationals; the sampler never asks
for a real exponential, real power, or real ceiling.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics
open scoped BigOperators

/-- The source code uses this integer width and its rational square. -/
def actualAuxiliarySquaredWidth (scale n : ℕ) : ℚ := (scale*n : ℚ)^2

def actualLegTicketBits (constant n bits : ℕ) : ℕ :=
  windowTicketBits (actualLegCutoffProgram constant n-1) bits

def actualLegGaussianDraw (constant scale n bits : ℕ)
    (word : Fin (actualLegTicketBits constant n bits) → Fin 2) :
    Window (legCutoff (constant : ℝ) n-1) :=
  let point := windowGaussianDraw (actualAuxiliarySquaredWidth scale n)
    (actualLegCutoffProgram constant n-1) bits word
  ⟨point.val,by rw [← actualLegCutoffProgram_eq]; exact point.property⟩

def actualQueueTicketBits (n bits : ℕ) : ℕ := windowTicketBits (n^2-1) bits

def actualQueueGaussianDraw (n bits : ℕ)
    (word : Fin (actualQueueTicketBits n bits) → Fin 2) : Window (queueCutoff n) :=
  windowGaussianDraw (actualAuxiliarySquaredWidth 1 n) (n^2-1) bits word

noncomputable section
set_option backward.isDefEq.respectTransparency false

def actualLegWindowEquiv (constant n : ℕ) :
    Window (actualLegCutoffProgram constant n-1)≃Window (legCutoff (constant : ℝ) n-1) where
  toFun point := ⟨point.val,by rw [← actualLegCutoffProgram_eq]; exact point.property⟩
  invFun point := ⟨point.val,by rw [actualLegCutoffProgram_eq]; exact point.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def actualLegTicketLaw (constant scale n bits : ℕ) : FiniteDist (Window (legCutoff (constant : ℝ) n-1)) :=
  (windowTicketLaw (actualAuxiliarySquaredWidth scale n) (actualLegCutoffProgram constant n-1) bits).map
    (actualLegWindowEquiv constant n)

def actualQueueTicketLaw (n bits : ℕ) : FiniteDist (Window (queueCutoff n)) :=
  windowTicketLaw (actualAuxiliarySquaredWidth 1 n) (n^2-1) bits

theorem actualLegGaussianDraw_law (constant scale n bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (actualLegTicketBits constant n bits) => FiniteDist.uniform (Fin 2))).map
      (actualLegGaussianDraw constant scale n bits)=actualLegTicketLaw constant scale n bits := by
  have hh := congrArg (fun law : FiniteDist (Window (actualLegCutoffProgram constant n-1)) =>
    law.map (actualLegWindowEquiv constant n))
      (windowGaussianDraw_law (actualAuxiliarySquaredWidth scale n) (actualLegCutoffProgram constant n-1) bits)
  dsimp only at hh
  rw [FiniteDist.map_map] at hh
  exact hh

theorem actualQueueGaussianDraw_law (n bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (actualQueueTicketBits n bits) => FiniteDist.uniform (Fin 2))).map
      (actualQueueGaussianDraw n bits)=actualQueueTicketLaw n bits := windowGaussianDraw_law _ _ _

private theorem actualAuxiliarySquaredWidth_positive (scale n : ℕ) (hs : 0<scale) (hn : 0<n) :
    0<actualAuxiliarySquaredWidth scale n := by unfold actualAuxiliarySquaredWidth; positivity

private theorem actualAuxiliarySquaredWidth_cast (scale n : ℕ) :
    (actualAuxiliarySquaredWidth scale n : ℝ)=((scale : ℝ)*n)^2 := by
  unfold actualAuxiliarySquaredWidth
  push_cast
  rfl

/-- The two physical leg noises use `scale=1` and `scale=10`. This statement
compares the executable sampler with those exact actual finite laws. -/
theorem actualLegTicketLaw_l1 (constant scale n bits : ℕ) (hs : 0<scale) (hn : 0<n) :
    (∑ point,|(actualLegTicketLaw constant scale n bits).weight point-
      (windowGaussian ((scale : ℝ)*n) (legCutoff (constant : ℝ) n-1)).weight point|)≤1/(2 : ℝ)^bits := by
  have hh := windowTicketLaw_l1 (actualAuxiliarySquaredWidth scale n) ((scale : ℝ)*n)
    (actualLegCutoffProgram constant n-1) bits (actualAuxiliarySquaredWidth_positive scale n hs hn)
    (actualAuxiliarySquaredWidth_cast scale n)
  rw [← (actualLegWindowEquiv constant n).sum_comp]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro point _
  unfold actualLegTicketLaw
  rw [FiniteDist.map_equiv_weight]
  simp only [Equiv.symm_apply_apply]
  congr 2
  change GaussianSource.weight ((scale : ℝ)*n) point.val/windowNormalizer ((scale : ℝ)*n) (legCutoff (constant : ℝ) n-1)=
    GaussianSource.weight ((scale : ℝ)*n) point.val/windowNormalizer ((scale : ℝ)*n) (actualLegCutoffProgram constant n-1)
  exact congrArg (fun cutoff => GaussianSource.weight ((scale : ℝ)*n) point.val/
    windowNormalizer ((scale : ℝ)*n) (cutoff-1)) (actualLegCutoffProgram_eq constant n).symm

theorem actualQueueTicketLaw_l1 (n bits : ℕ) (hn : 0<n) :
    (∑ point,|(actualQueueTicketLaw n bits).weight point-
      (windowGaussian n (queueCutoff n)).weight point|)≤1/(2 : ℝ)^bits := by
  have hh := windowTicketLaw_l1 (actualAuxiliarySquaredWidth 1 n) (1*(n : ℝ))
    (n^2-1) bits (actualAuxiliarySquaredWidth_positive 1 n (by decide) hn)
    (by simpa only [Nat.cast_one] using actualAuxiliarySquaredWidth_cast 1 n)
  simpa only [Nat.cast_one,one_mul] using hh

theorem actualLegTicketBits_bound (constant n : ℕ) (hn : 2≤n) :
    actualLegTicketBits constant n n≤(2*constant+2)*n^2 := by
  have hc := actualLegCutoffProgram_le constant n
  have hn2 : n≤n^2 := by nlinarith
  have hn4 : 4≤n^2 := by nlinarith
  unfold actualLegTicketBits windowTicketBits
  have hs := Nat.sub_le (actualLegCutoffProgram constant n) 1
  nlinarith

theorem actualQueueTicketBits_bound (n : ℕ) (hn : 2≤n) : actualQueueTicketBits n n≤4*n^2 := by
  unfold actualQueueTicketBits windowTicketBits
  have hn2 : n≤n^2 := by nlinarith
  have hn4 : 4≤n^2 := by nlinarith
  omega

end
end AFT.V7Calibration

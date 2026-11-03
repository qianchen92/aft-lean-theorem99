import AFT.ProfileHilbert
import CurrentAFT.Parameters

/-! # Literal normalized finite sums and their centered decomposition -/

namespace CurrentAFT.NormalizedMeanAlgebra

open scoped BigOperators Classical

noncomputable section

def normalizationScale (security : ℕ) : ℝ :=
  (Real.sqrt (Parameters.dimension security : ℝ))⁻¹

variable {Index Hilbert : Type*} [Fintype Index] [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def normalizedSum (scale : ℝ) (value : Index → Hilbert) (offset : Hilbert) : Hilbert :=
  scale • ((∑ index, value index) + offset)

def centeredSum (scale : ℝ) (value mean : Index → Hilbert) : Hilbert :=
  scale • ∑ index, (value index - mean index)

theorem decomposition_unconditional (scale : ℝ) (value mean : Index → Hilbert) (offset : Hilbert) :
    normalizedSum scale value offset = centeredSum scale value mean + normalizedSum scale mean offset := by
  unfold normalizedSum centeredSum
  rw [Finset.sum_sub_distrib, ← smul_add]
  congr 1
  abel

theorem decomposition (scale : ℝ) (value mean : Index → Hilbert)
    (offset targetMean : Hilbert) (hmean : (∑ index, mean index) + offset = targetMean) :
    normalizedSum scale value offset = centeredSum scale value mean + scale • targetMean := by
  unfold normalizedSum centeredSum
  rw [← hmean, Finset.sum_sub_distrib, ← smul_add]
  congr 1
  abel

section Euclidean

variable {Color : Type*} [Fintype Color]

def euclideanSum (scale : ℝ) (value : Index → EuclideanSpace ℝ Color)
    (offset : EuclideanSpace ℝ Color) : EuclideanSpace ℝ Color :=
  scale • ((∑ index, value index) + offset)

def euclideanCenteredSum (scale : ℝ) (value mean : Index → EuclideanSpace ℝ Color) :
    EuclideanSpace ℝ Color := scale • ∑ index, (value index - mean index)

theorem euclidean_decomposition (scale : ℝ) (value mean : Index → EuclideanSpace ℝ Color)
    (offset target : EuclideanSpace ℝ Color) (hmean : (∑ index, mean index) + offset = target) :
    euclideanSum scale value offset = euclideanCenteredSum scale value mean + scale • target := by
  unfold euclideanSum euclideanCenteredSum
  rw [← hmean, Finset.sum_sub_distrib, ← smul_add]
  congr 1
  abel

theorem euclidean_decomposition_coordinate (scale : ℝ) (value mean : Index → EuclideanSpace ℝ Color)
    (offset : EuclideanSpace ℝ Color) (target : Color → ℝ)
    (hmean : ∀ color, (∑ index, (mean index).ofLp color) + offset.ofLp color = target color)
    (color : Color) :
    (euclideanSum scale value offset).ofLp color =
      (euclideanCenteredSum scale value mean).ofLp color + scale * target color := by
  simp only [euclideanSum, euclideanCenteredSum, WithLp.ofLp_smul, WithLp.ofLp_add,
    WithLp.ofLp_sub, WithLp.ofLp_sum, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul, Finset.sum_sub_distrib]
  rw [← hmean color]
  ring

end Euclidean

end

end CurrentAFT.NormalizedMeanAlgebra

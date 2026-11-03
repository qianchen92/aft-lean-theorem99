import AFT.BinaryProtectedFeature
import AFT.BinaryProtectedScale

/-! Decoding a sampled chart index by actual binary long division. The
runtime data are three bounded counters; field casts appear only in the
semantic theorem. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration

structure ChartCounterResult where
  offset : ℕ
  scale : ℕ
  shear : ℕ
  work : ℕ

def binaryChartCoordinates (modulus chart : ℕ) : ChartCounterResult :=
  let square := multiplyCounter modulus modulus
  let outer := divideCounter chart square.count
  let inner := divideCounter outer.remainder modulus
  ⟨outer.quotient,inner.quotient,inner.remainder,square.work+outer.work+inner.work+3⟩

theorem binaryChartCoordinates_values (modulus chart : ℕ) (hm : 0 < modulus) :
    (binaryChartCoordinates modulus chart).offset=chart/(modulus*modulus) ∧
    (binaryChartCoordinates modulus chart).scale=(chart%(modulus*modulus))/modulus ∧
    (binaryChartCoordinates modulus chart).shear=(chart%(modulus*modulus))%modulus := by
  simp only [binaryChartCoordinates,multiplyCounter_value,
    (divideCounter_value _ _ (Nat.mul_pos hm hm)).1,(divideCounter_value _ _ (Nat.mul_pos hm hm)).2,
    (divideCounter_value _ _ hm).1,(divideCounter_value _ _ hm).2,and_self]

theorem binaryChartCoordinates_bounds (modulus chart : ℕ) (hm : 0 < modulus)
    (hi : chart < modulus*(modulus*modulus)) :
    (binaryChartCoordinates modulus chart).offset < modulus ∧
    (binaryChartCoordinates modulus chart).scale < modulus ∧
    (binaryChartCoordinates modulus chart).shear < modulus := by
  rcases binaryChartCoordinates_values modulus chart hm with ⟨ho,hs,ht⟩
  rw [ho,hs,ht]
  exact ⟨(Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hm)).mpr hi,
    (Nat.div_lt_iff_lt_mul hm).mpr (Nat.mod_lt _ (Nat.mul_pos hm hm)),Nat.mod_lt _ hm⟩

theorem binaryChartCoordinates_semantics (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) :
    (((binaryChartCoordinates modulus chart.val).offset : ZMod modulus),
      ((binaryChartCoordinates modulus chart.val).scale : ZMod modulus),
      ((binaryChartCoordinates modulus chart.val).shear : ZMod modulus))=
        finiteChartEquiv modulus chart := by
  have hm := NeZero.pos modulus
  rcases binaryChartCoordinates_values modulus chart.val hm with ⟨ho,hs,ht⟩
  rw [ho,hs,ht]
  rcases finiteChartEquiv_coordinate modulus chart with ⟨h0,h1,h2⟩
  apply Prod.ext h0.symm
  exact Prod.ext h1.symm h2.symm

theorem binaryChartCoordinates_work (modulus chart : ℕ) (hm : 0 < modulus) :
    (binaryChartCoordinates modulus chart).work ≤ protectedScaleWork modulus chart := by
  have hfirst := divideCounter_work chart (modulus*modulus) (Nat.mul_pos hm hm)
  have hsecond := divideCounter_work (chart%(modulus*modulus)) modulus hm
  have hmod := (Nat.mod_lt chart (Nat.mul_pos hm hm)).le
  have hsecond' : (divideCounter (chart%(modulus*modulus)) modulus).work ≤
      500*(modulus*modulus+modulus+2)^2 := hsecond.trans (by gcongr)
  simp only [binaryChartCoordinates,multiplyCounter_value,multiplyCounter_work,
    (divideCounter_value _ _ (Nat.mul_pos hm hm)).2,protectedScaleWork]
  omega

end AFT.BinaryArithmetic

import AFT.BinaryFiniteArithmetic
import AFT.BinaryLoopControl

/-! # Actual Gaussian input construction

The dimension and window coordinate are bounded unary counters. Explicit
counter arithmetic and the ripple encoder produce their rational binary
representations; an arbitrary rational encoder is never called.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def ofUnaryInteger : ℤ → RationalResult
  | .ofNat count =>
      let result := ofCounter count
      ⟨result.data,result.work+1⟩
  | .negSucc count =>
      let magnitude := ofCounter count.succ
      let result := negate magnitude.data
      ⟨result.data,magnitude.work+result.work+3⟩

theorem ofUnaryInteger_value (integer : ℤ) : (ofUnaryInteger integer).data.decode=(integer : ℚ) := by
  cases integer with
  | ofNat count => simp only [ofUnaryInteger,ofCounter_value,Int.ofNat_eq_natCast,Int.cast_natCast]
  | negSucc count => simp only [ofUnaryInteger,negate_value,ofCounter_value,Int.cast_negSucc,Nat.cast_succ]

theorem ofUnaryInteger_work (integer : ℤ) :
    (ofUnaryInteger integer).work≤ 60*(integer.natAbs+1)^2+5 := by
  cases integer with
  | ofNat count =>
      have hw := ofCounter_work count
      simp only [ofUnaryInteger,Int.ofNat_eq_natCast,Int.natAbs_natCast]
      omega
  | negSucc count =>
      have hw := ofCounter_work count.succ
      simp only [ofUnaryInteger,negate,Int.natAbs_negSucc]
      omega

def rootSquaredWidth (dimension : ℕ) : RationalResult :=
  let squared := multiplyCounter dimension dimension
  let scaled := multiplyCounter 8 squared.count
  let result := ofCounter scaled.count
  ⟨result.data,squared.work+scaled.work+result.work+3⟩

theorem rootSquaredWidth_value (dimension : ℕ) :
    (rootSquaredWidth dimension).data.decode=8*(dimension : ℚ)^2 := by
  simp only [rootSquaredWidth,ofCounter_value,multiplyCounter_value,Nat.cast_mul,Nat.cast_ofNat,pow_two]

theorem rootSquaredWidth_work (dimension : ℕ) :
    (rootSquaredWidth dimension).work≤ 60*(8*dimension^2+1)^2+30*(dimension+1)^2 := by
  have hw := ofCounter_work (8*(dimension*dimension))
  simp only [rootSquaredWidth,multiplyCounter_value,multiplyCounter_work]
  simp only [pow_two] at hw ⊢
  nlinarith

end AFT.BinaryArithmetic.RationalBits

import AFT.BinaryRationalControl
import AFT.BinaryLoopControl
import AFT.RationalSeriesHeight

/-! # Actual control parameters for the Gaussian series

Scale and precision are computed by binary ceiling and explicit conversion
into bounded unary loop counters. No decoded rational is inspected at run
time. The semantic ceiling occurs only in the correctness and cost bounds.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

structure ExponentialControl where
  clipped : RationalBits
  scaleDigits : List Bool
  scale : ℕ
  work : ℕ

def prepareExponential (argument : RationalBits) : ExponentialControl :=
  let clipped := argument.maxZero
  let ceiling := clipped.data.ceilNatural
  let counter := readCounter ceiling.digits
  let doubled := doubleCounter counter.count
  ⟨clipped.data,true::ceiling.digits,doubled.count.succ,
    clipped.work+ceiling.work+counter.work+doubled.work+5⟩

theorem prepareExponential_clipped (argument : RationalBits) :
    (prepareExponential argument).clipped.decode=max argument.decode 0 := by
  simp only [prepareExponential,RationalBits.maxZero_value]

theorem prepareExponential_digits (argument : RationalBits) :
    value (prepareExponential argument).scaleDigits=expScale argument.decode := by
  simp only [prepareExponential,value,Bool.toNat_true,RationalBits.ceilNatural_value,
    RationalBits.maxZero_value,expScale]
  omega

theorem prepareExponential_scale (argument : RationalBits) :
    (prepareExponential argument).scale=expScale argument.decode := by
  simp only [prepareExponential,doubleCounter_value,readCounter_value,RationalBits.ceilNatural_value,
    RationalBits.maxZero_value,expScale]

theorem prepareExponential_work (argument : RationalBits) (bits : ℕ)
    (hh : HeightBound argument.decode bits) :
    (prepareExponential argument).work≤
      900*(bits+2)^2+9*⌈max argument.decode 0⌉₊+4*(bits+1)+10 := by
  have hc : HeightBound argument.maxZero.data.decode bits := by
    rw [RationalBits.maxZero_value]
    exact max_zero_height _ _ hh
  have hw := RationalBits.ceilNatural_work_of_height argument.maxZero.data bits hc
  have hl := RationalBits.ceilNatural_length_of_height argument.maxZero.data bits hc
  have hr := readCounter_work argument.maxZero.data.ceilNatural.digits
  simp only [prepareExponential,RationalBits.maxZero_work,doubleCounter_work,readCounter_value,
    RationalBits.ceilNatural_value,RationalBits.maxZero_value] at hr ⊢
  omega

/-- The integer guard for the finite pi series, with all counter work. -/
def prepareGaussianPrecision (ratio : RationalBits) (bits : ℕ) : UnaryCounterResult :=
  let ceiling := ratio.ceilNatural
  let guard := readCounter ceiling.digits
  let total := addCounter bits guard.count
  ⟨total.count.succ,ceiling.work+guard.work+total.work+4⟩

theorem prepareGaussianPrecision_value (ratio : RationalBits) (bits : ℕ) :
    (prepareGaussianPrecision ratio bits).count=bits+⌈ratio.decode⌉₊+1 := by
  simp only [prepareGaussianPrecision,addCounter_value,readCounter_value,RationalBits.ceilNatural_value]

theorem prepareGaussianPrecision_work (ratio : RationalBits) (height bits : ℕ)
    (hh : HeightBound ratio.decode height) :
    (prepareGaussianPrecision ratio bits).work≤
      900*(height+2)^2+6*⌈ratio.decode⌉₊+4*(height+1)+2*bits+7 := by
  have hw := RationalBits.ceilNatural_work_of_height ratio height hh
  have hl := RationalBits.ceilNatural_length_of_height ratio height hh
  have hr := readCounter_work ratio.ceilNatural.digits
  simp only [prepareGaussianPrecision,addCounter_work,RationalBits.ceilNatural_value] at hr ⊢
  omega

end AFT.BinaryArithmetic

import AFT.BinaryExponentialProgram

/-! # The binary evaluator of the actual rational Gaussian approximation

The finite pi and exponential series, adaptive precision, range reduction,
and every rational primitive execute on the stored binary representation.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def gaussianFromRatio (ratio : RationalBits) (bits : ℕ) : RationalResult :=
  let precision := prepareGaussianPrecision ratio bits
  let piValue := pi precision.count
  let argument := multiply piValue.data ratio
  let result := exponential argument.data bits.succ
  ⟨result.data,precision.work+piValue.work+argument.work+result.work+5⟩

theorem gaussianFromRatio_value (ratio : RationalBits) (bits : ℕ) :
    (gaussianFromRatio ratio bits).data.decode=
      expNegApprox (piApprox (bits+⌈ratio.decode⌉₊+1)*ratio.decode) (bits+1) := by
  simp only [gaussianFromRatio,exponential_value,multiply_value,pi_value,prepareGaussianPrecision_value]

def gaussian (squaredWidth point : RationalBits) (bits : ℕ) : RationalResult :=
  let square := multiply point point
  let ratio := quotient square.data squaredWidth
  let result := gaussianFromRatio ratio.data bits
  ⟨result.data,square.work+ratio.work+result.work+4⟩

theorem gaussian_value (squaredWidth point : RationalBits) (integerPoint : ℤ) (bits : ℕ)
    (hp : point.decode=(integerPoint : ℚ)) :
    (gaussian squaredWidth point bits).data.decode=gaussianApprox squaredWidth.decode integerPoint bits := by
  simp only [gaussian,gaussianFromRatio_value,quotient_value,multiply_value,hp,gaussianApprox,gaussianGuard,
    gaussianRatio,pow_two]

def gaussianRatioWork (height guard scale bits : ℕ) : ℕ :=
  900*(height+2)^2+6*guard+4*(height+1)+2*bits+12+
    piWork (bits+guard+1)+primitiveWorkBound (piHeight (bits+guard+1)+height)+
    exponentialWork (piHeight (bits+guard+1)+height) scale (bits+1)

theorem gaussianFromRatio_work (ratio : RationalBits) (height bits : ℕ)
    (hh : HeightBound ratio.decode height) :
    (gaussianFromRatio ratio bits).work≤ gaussianRatioWork height ⌈ratio.decode⌉₊
      (expScale (piApprox (bits+⌈ratio.decode⌉₊+1)*ratio.decode)) bits := by
  let precision := prepareGaussianPrecision ratio bits
  let piValue := pi precision.count
  let argument := multiply piValue.data ratio
  have hp : precision.count=bits+⌈ratio.decode⌉₊+1 := prepareGaussianPrecision_value ratio bits
  have hpi : HeightBound piValue.data.decode (piHeight (bits+⌈ratio.decode⌉₊+1)) := by
    dsimp only [piValue]
    rw [pi_value,hp]
    exact piApprox_height _
  have harg : HeightBound argument.data.decode (piHeight (bits+⌈ratio.decode⌉₊+1)+height) := by
    dsimp only [argument]
    rw [multiply_value]
    exact hpi.mul hh
  have wp := prepareGaussianPrecision_work ratio height bits hh
  have wpi := pi_work precision.count
  rw [hp] at wpi
  have wm := multiply_work piValue.data ratio (piHeight (bits+⌈ratio.decode⌉₊+1)+height)
    (hpi.mono (Nat.le_add_right _ _)) (hh.mono (Nat.le_add_left _ _))
  have we := exponential_work argument.data (piHeight (bits+⌈ratio.decode⌉₊+1)+height) (bits+1) harg
  have ha : argument.data.decode=piApprox (bits+⌈ratio.decode⌉₊+1)*ratio.decode := by
    simp only [argument,multiply_value,piValue,pi_value,hp]
  rw [ha] at we
  change precision.work+piValue.work+argument.work+(exponential argument.data (bits+1)).work+5≤ _
  change precision.work≤ _ at wp
  change argument.work≤ _ at wm
  have wpi' : piValue.work≤ piWork (bits+⌈ratio.decode⌉₊+1) := by
    dsimp only [piValue]
    rw [hp]
    exact wpi
  simp only [gaussianRatioWork]
  omega

def gaussianWork (widthHeight pointHeight guard scale bits : ℕ) : ℕ :=
  primitiveWorkBound pointHeight+2*primitiveWorkBound (2*pointHeight+widthHeight)+
    gaussianRatioWork (2*pointHeight+widthHeight) guard scale bits+6

theorem gaussian_work (squaredWidth point : RationalBits) (integerPoint : ℤ)
    (widthHeight pointHeight bits : ℕ)
    (hw : HeightBound squaredWidth.decode widthHeight)
    (hp : HeightBound point.decode pointHeight)
    (he : point.decode=(integerPoint : ℚ)) :
    (gaussian squaredWidth point bits).work≤ gaussianWork widthHeight pointHeight
      (gaussianGuard squaredWidth.decode integerPoint)
      (gaussianExpScale squaredWidth.decode integerPoint bits) bits := by
  let square := multiply point point
  let ratio := quotient square.data squaredWidth
  have hs : HeightBound square.data.decode (2*pointHeight) := by
    dsimp only [square]
    rw [multiply_value]
    exact (hp.mul hp).mono (by omega)
  have hr : HeightBound ratio.data.decode (2*pointHeight+widthHeight) := by
    dsimp only [ratio]
    rw [quotient_value]
    exact hs.div hw
  have hre : ratio.data.decode=gaussianRatio squaredWidth.decode integerPoint := by
    simp only [ratio,quotient_value,square,multiply_value,he,gaussianRatio,pow_two]
  have ws := multiply_work point point pointHeight hp hp
  have wr := quotient_work square.data squaredWidth (2*pointHeight+widthHeight)
    (hs.mono (Nat.le_add_right _ _)) (hw.mono (Nat.le_add_left _ _))
  have wg := gaussianFromRatio_work ratio.data (2*pointHeight+widthHeight) bits hr
  rw [hre] at wg
  change square.work+ratio.work+(gaussianFromRatio ratio.data bits).work+4≤ _
  change square.work≤ _ at ws
  change ratio.work≤ _ at wr
  simp only [gaussianWork,gaussianGuard,gaussianExpScale,gaussianPiPrecision]
  omega

end AFT.BinaryArithmetic.RationalBits

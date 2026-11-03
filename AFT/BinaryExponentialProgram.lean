import AFT.BinaryGaussianControl
import AFT.BinaryFiniteSeries

/-! # The actual binary range-reduced exponential evaluator

All data arithmetic calls canonical binary rational programs. Control
parameters use binary ceiling and explicit unary-counter operations.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def exponential (argument : RationalBits) (bits : ℕ) : RationalResult :=
  let control := prepareExponential argument
  let scale := ofNat control.scaleDigits
  let reduced := quotient control.clipped scale.data
  let count := addCounter bits control.scale
  let polynomial := taylor reduced.data count.count.succ
  let inv := inverse polynomial.data
  let result := power inv.data control.scale
  ⟨result.data,control.work+scale.work+reduced.work+count.work+
    polynomial.work+inv.work+result.work+8⟩

theorem exponential_value (argument : RationalBits) (bits : ℕ) :
    (exponential argument bits).data.decode=expNegApprox argument.decode bits := by
  simp only [exponential,power_value,inverse_value,taylor_value,quotient_value,ofNat_value,
    prepareExponential_digits,prepareExponential_clipped,addCounter_value,prepareExponential_scale,
    expNegApprox,expNegScaled]

def exponentialSeriesHeight (height scale bits : ℕ) : ℕ :=
  (bits+scale+1)*((bits+scale+1)*(height+scale)+(bits+scale+1)^2+1)

def exponentialWork (height scale bits : ℕ) : ℕ :=
  900*(height+2)^2+9*scale+8*(height+2)+2*bits+100+
    2*primitiveWorkBound (height+scale)+seriesWork (height+scale) (bits+scale+1)+
    primitiveWorkBound (exponentialSeriesHeight height scale bits)+
    scale*(primitiveWorkBound (exponentialSeriesHeight height scale bits*(scale+1))+2)

attribute [local irreducible] prepareExponential ofNat quotient taylor inverse power maxZero

set_option maxHeartbeats 800000 in
theorem exponential_work (argument : RationalBits) (height bits : ℕ)
    (hh : HeightBound argument.decode height) :
    (exponential argument bits).work≤ exponentialWork height (expScale argument.decode) bits := by
  let control := prepareExponential argument
  let scale := ofNat control.scaleDigits
  let reduced := quotient control.clipped scale.data
  let count := addCounter bits control.scale
  let polynomial := taylor reduced.data count.count.succ
  let inv := inverse polynomial.data
  have hclip : HeightBound control.clipped.decode height := by
    dsimp only [control]
    rw [prepareExponential_clipped]
    exact max_zero_height _ _ hh
  have hscale : HeightBound scale.data.decode (expScale argument.decode) := by
    dsimp only [scale,control]
    rw [ofNat_value,prepareExponential_digits]
    exact HeightBound.nat_coarse _
  have hreduced : HeightBound reduced.data.decode (height+expScale argument.decode) := by
    dsimp only [reduced]
    rw [quotient_value]
    exact hclip.div hscale
  have hcount : count.count.succ=bits+expScale argument.decode+1 := by
    simp only [count,control,addCounter_value,prepareExponential_scale]
  have hpoly : HeightBound polynomial.data.decode
      (exponentialSeriesHeight height (expScale argument.decode) bits) := by
    dsimp only [polynomial]
    rw [taylor_value,hcount]
    exact expSum_height _ _ _ hreduced
  have hinv : HeightBound inv.data.decode
      (exponentialSeriesHeight height (expScale argument.decode) bits) := by
    dsimp only [inv]
    rw [inverse_value]
    exact hpoly.inv
  have wc := prepareExponential_work argument height hh
  have hl := ceilNatural_length_of_height argument.maxZero.data height (by
    rw [maxZero_value];exact max_zero_height _ _ hh)
  have ws : scale.work≤ 4*(height+2)+5 := by
    dsimp only [scale,control,prepareExponential]
    rw [ofNat_work]
    simp only [prepareExponential,List.length_cons]
    omega
  have wr := quotient_work control.clipped scale.data (height+expScale argument.decode)
    (hclip.mono (Nat.le_add_right _ _)) (hscale.mono (Nat.le_add_left _ _))
  have wt : polynomial.work≤ seriesWork (height+expScale argument.decode) (bits+expScale argument.decode+1) := by
    have ht := taylor_work reduced.data (height+expScale argument.decode) count.count.succ hreduced
    simpa only [polynomial,hcount] using ht
  have wi := inverse_work polynomial.data (exponentialSeriesHeight height (expScale argument.decode) bits)
  have wp := power_work inv.data (exponentialSeriesHeight height (expScale argument.decode) bits)
    control.scale hinv
  have hs : ⌈max argument.decode 0⌉₊≤ expScale argument.decode := by unfold expScale;omega
  change control.work+scale.work+reduced.work+count.work+polynomial.work+inv.work+
      (power inv.data control.scale).work+8≤ _
  change control.work≤ _ at wc
  change reduced.work≤ _ at wr
  change polynomial.work≤ _ at wt
  change inv.work≤ _ at wi
  have hsc : control.scale=expScale argument.decode := prepareExponential_scale argument
  simp only [hsc] at wp ⊢
  simp only [count,addCounter_work,exponentialWork]
  omega

end AFT.BinaryArithmetic.RationalBits

import AFT.BinarySliceProbability
import AFT.BinaryChartArray
import AFT.ActualPublicOffsetProgram

/-! Actual averaging over the finite anchor interval, with explicit counter
indices and signed binary slice arithmetic. -/
namespace AFT.BinaryArithmetic
open V7Calibration RationalNumerics RationalBits
open scoped BigOperators

 def binaryAnchorSliceTerm (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) : RationalResult :=
  let offset := canonicalCounter index.val
  let center := signedAdd startSign false start offset.digits
  let shifted := signedAdd center.negative (!sourceSign) center.digits source
  let probability := binarySliceProbability modulusSign boundarySign shifted.negative colorSign
    modulus boundary shifted.digits color
  let widthBits := RationalBits.ofCounter width
  let inverse := RationalBits.inverse widthBits.data
  let result := RationalBits.multiply inverse.data probability.data
  ⟨result.data,offset.work+center.work+shifted.work+probability.work+widthBits.work+inverse.work+result.work+8⟩

 theorem binaryAnchorSliceTerm_value (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) :
    (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width index).data.decode=
    (width : ℚ)⁻¹*sliceProbabilityProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
      (signedValue startSign start+index.val-signedValue sourceSign source) (signedValue colorSign color) := by
  have hneg : signedValue (!sourceSign) source= -signedValue sourceSign source := by cases sourceSign <;> simp [signedValue]
  simp only [binaryAnchorSliceTerm,RationalBits.multiply_value,RationalBits.inverse_value,RationalBits.ofCounter_value,
    binarySliceProbability_value]
  rw [signedAdd_value,signedAdd_value,hneg]
  simp only [signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value,sub_eq_add_neg]

 def binaryAveragedSlice (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) : RationalResult :=
  sumFin width (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
    modulus boundary start source color width)

 theorem averagedSliceProgram_indexed (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    averagedSliceProgram modulus boundary start source width color=
      ∑ index : Fin width,(width : ℚ)⁻¹*sliceProbabilityProgram modulus boundary (start+index.val-source) color := by
  unfold averagedSliceProgram
  rw [←Finset.sum_coe_sort (anchorInterval start width)]
  trans ∑ index : Fin width,intervalProbabilityProgram start width (start+index.val)*
    sliceProbabilityProgram modulus boundary (start+index.val-source) color
  · convert ((anchorIndexEquiv start width).sum_comp (fun point : {value : ℤ // value∈anchorInterval start width} =>
      intervalProbabilityProgram start width point.val*sliceProbabilityProgram modulus boundary (point.val-source) color)).symm using 1
  · apply Finset.sum_congr rfl
    intro index _
    have hi : start+index.val∈anchorInterval start width := (anchorIndexEquiv start width index).property
    simp only [intervalProbabilityProgram,if_pos hi]

 theorem binaryAveragedSlice_value (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) :
    (binaryAveragedSlice modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width).data.decode=
      averagedSliceProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
        (signedValue startSign start) (signedValue sourceSign source) width (signedValue colorSign color) := by
  simp only [binaryAveragedSlice,sumFin_value,binaryAnchorSliceTerm_value,averagedSliceProgram_indexed]

 def binaryAnchorSliceTermWork (bits : ℕ) : ℕ :=
  110*(bits+1)^2+40*(bits+1)+16+binarySliceProbabilityWork (bits+2)+
    RationalBits.primitiveWorkBound bits+RationalBits.primitiveWorkBound (2*bits+6)+8

 theorem binaryAnchorSliceTerm_height (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) (bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (ht : start.length≤bits)
    (hs : source.length≤bits) (hw : width≤bits) :
    HeightBound (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width index).data.decode (2*bits+6) := by
  have hi : (canonicalCounter index.val).digits.length≤bits := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=index.val))).trans (index.isLt.le.trans hw)
  have hc := signedAdd_length startSign false start (canonicalCounter index.val).digits
  have hshift := signedAdd_length (signedAdd startSign false start (canonicalCounter index.val).digits).negative
    (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source
  have hp := binarySliceProbability_height modulusSign boundarySign
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).negative colorSign
    modulus boundary
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).digits
    color (bits+2) (by omega) (by omega) (by omega)
  have hd : HeightBound (width : ℚ)⁻¹ bits := ((HeightBound.nat_coarse width).mono hw).inv
  simp only [binaryAnchorSliceTerm,RationalBits.multiply_value,RationalBits.inverse_value,RationalBits.ofCounter_value]
  exact (hd.mul hp).mono (by omega)

 theorem binaryAnchorSliceTerm_work (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) (bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (ht : start.length≤bits)
    (hs : source.length≤bits) (hcolor : color.length≤bits) (hw : width≤bits) :
    (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width index).work≤binaryAnchorSliceTermWork bits := by
  have hi : (canonicalCounter index.val).digits.length≤bits := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=index.val))).trans (index.isLt.le.trans hw)
  have wi := (canonicalCounter_work index.val).trans (show 50*(index.val+1)^2≤50*(bits+1)^2 by gcongr;exact index.isLt.le.trans hw)
  have wc := signedAdd_work startSign false start (canonicalCounter index.val).digits
  have hc := signedAdd_length startSign false start (canonicalCounter index.val).digits
  have ws := signedAdd_work (signedAdd startSign false start (canonicalCounter index.val).digits).negative
    (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source
  have hshift := signedAdd_length (signedAdd startSign false start (canonicalCounter index.val).digits).negative
    (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source
  have wp := binarySliceProbability_work modulusSign boundarySign
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).negative colorSign
    modulus boundary
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).digits
    color (bits+2) (by omega) (by omega) (by omega) (by omega)
  have hp := binarySliceProbability_height modulusSign boundarySign
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).negative colorSign
    modulus boundary
    (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
      (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).digits
    color (bits+2) (by omega) (by omega) (by omega)
  have wd := (RationalBits.ofCounter_work width).trans (show 60*(width+1)^2≤60*(bits+1)^2 by gcongr)
  have wdi := RationalBits.inverse_work (RationalBits.ofCounter width).data bits
  have hd : HeightBound (RationalBits.inverse (RationalBits.ofCounter width).data).data.decode (2*bits+6) := by
    rw [RationalBits.inverse_value,RationalBits.ofCounter_value]
    exact ((HeightBound.nat_coarse width).mono (hw.trans (by omega))).inv
  have wm := RationalBits.multiply_work (RationalBits.inverse (RationalBits.ofCounter width).data).data
    (binarySliceProbability modulusSign boundarySign
      (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
        (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).negative colorSign
      modulus boundary
      (signedAdd (signedAdd startSign false start (canonicalCounter index.val).digits).negative
        (!sourceSign) (signedAdd startSign false start (canonicalCounter index.val).digits).digits source).digits color).data
    (2*bits+6) hd (hp.mono (by omega))
  simp only [binaryAnchorSliceTerm,binaryAnchorSliceTermWork]
  omega

 def binaryAveragedSliceWork (bits : ℕ) : ℕ :=
  bits*(binaryAnchorSliceTermWork bits+RationalBits.primitiveWorkBound ((bits+1)*(2*bits+7))+2)+2

 theorem binaryAveragedSlice_work (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (ht : start.length≤bits)
    (hs : source.length≤bits) (hc : color.length≤bits) (hw : width≤bits) :
    (binaryAveragedSlice modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width).work≤binaryAveragedSliceWork bits := by
  have hh := sumFin_work width (2*bits+6) (binaryAnchorSliceTermWork bits)
    (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign modulus boundary start source color width)
    (fun index=>binaryAnchorSliceTerm_height _ _ _ _ _ _ _ _ _ _ _ index bits hm hb ht hs hw)
    (fun index=>binaryAnchorSliceTerm_work _ _ _ _ _ _ _ _ _ _ _ index bits hm hb ht hs hc hw)
  apply hh.trans
  unfold binaryAveragedSliceWork RationalBits.primitiveWorkBound
  gcongr

 theorem binaryAveragedSlice_height (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (ht : start.length≤bits)
    (hs : source.length≤bits) (hw : width≤bits) :
    HeightBound (binaryAveragedSlice modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width).data.decode (bits*(2*bits+7)) := by
  have hh := sumFin_height width (2*bits+6)
    (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign modulus boundary start source color width)
    (fun index=>binaryAnchorSliceTerm_height _ _ _ _ _ _ _ _ _ _ _ index bits hm hb ht hs hw)
  exact hh.mono (Nat.mul_le_mul_right _ hw)

end AFT.BinaryArithmetic

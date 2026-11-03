import CurrentAFT.BinaryMarkedFixedAnchor

/-! # Same-scalar marked centered profiles and their actual primary mean -/
namespace CurrentAFT.BinaryMarkedCenteredCache
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current BinaryMarkedFixedAnchor.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point (security : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) (center : RationalBits) : RationalResult :=
  let code := canonicalCounter output.val
  let anchor := BinaryMarkedFixedAnchor.current security scalar primary code.digits
  let ratio := RationalBits.quotient anchor.data center
  let result := RationalBits.add ratio.data minusOne
  ⟨result.data,code.work+anchor.work+ratio.work+result.work+4⟩

theorem point_value (security : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) (center : RationalBits) :
    (point security scalar primary output center).data.decode=
      RationalMarkedSeedProgram.fixedAnchor security primary.val scalar.decode output.val/center.decode-1 := by
  simp only [point,RationalBits.add_value,minusOne_value,quotient_value,BinaryMarkedFixedAnchor.current_value,
    canonicalCounter_value,sub_eq_add_neg]

def read {count : ℕ} (profile : Vector RationalBits count) (index : Fin count) : RationalResult :=
  let result := readVector zero profile index
  ⟨result.value,result.work+1⟩

structure Result (security : ℕ) where
  primary : Vector RationalBits (colors security)
  centered : Vector RationalBits (colors security)
  mean : RationalBits
  count : RationalBits
  work : ℕ

def current (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : Result security :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security bits
  let center := readVector zero reference.center output
  let profile := buildArray modulus.count (fun primary => point security scalar primary output center.value)
  let mean := BinaryWindowAverage.sum reference.primary (read profile.data)
  ⟨reference.primary,profile.data,mean.data,count.data,
    modulus.work+count.work+reference.work+center.work+profile.work+mean.work+6⟩

theorem primary_value (security bits : ℕ) (scalar : IntegerBits) (output color : Fin (colors security)) :
    ((current security bits scalar output).primary.get color).decode=RationalProposalProgram.primary security bits color.val :=
  BinaryReferenceTables.primary_value security bits color

theorem centered_value (security bits : ℕ) (scalar : IntegerBits) (output primary : Fin (colors security)) :
    ((current security bits scalar output).centered.get primary).decode=
      RationalMarkedSeedProgram.secondCentered security bits primary.val scalar.decode output.val := by
  simp only [current,buildArray_get,point_value,readVector_value,BinaryReferenceTables.center_value,
    RationalMarkedSeedProgram.secondCentered,RationalMarkedSeedProgram.rawDensity]

theorem mean_value (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) :
    (current security bits scalar output).mean.decode=RationalMarkedSeedProgram.secondMean security bits scalar.decode output.val := by
  simp only [current,BinaryWindowAverage.sum_value,read,readVector_value,buildArray_get,point_value,
    BinaryReferenceTables.primary_value,BinaryReferenceTables.center_value,RationalMarkedSeedProgram.secondMean,
    RationalMarkedSeedProgram.secondCentered,RationalMarkedSeedProgram.rawDensity]

theorem count_value (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) :
    (current security bits scalar output).count.decode=(colors security:ℚ) := by
  simp only [current,ofCounter_value,colors,BinaryFirstInverseProgram.colors]

noncomputable section
noncomputable def pointOperandHeightPolynomial (centerBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedFixedAnchor.heightPolynomial+centerBits
noncomputable def pointHeightPolynomial (centerBits : Polynomial ℕ) : Polynomial ℕ := pointOperandHeightPolynomial centerBits+1
noncomputable def pointWorkPolynomial (scalarBits centerBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryMarkedFixedAnchor.workPolynomial scalarBits BinaryFirstInverseProgram.colorsPolynomial+
    3*primitiveWorkPolynomial (pointOperandHeightPolynomial centerBits)+6
noncomputable def profileHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := pointHeightPolynomial (BinaryReferenceTables.heightPolynomial precision)
noncomputable def profileWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := pointWorkPolynomial scalarBits (BinaryReferenceTables.heightPolynomial precision)
noncomputable def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+profileHeightPolynomial precision+1)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+profileHeightPolynomial precision+meanHeightPolynomial precision+
    BinaryFirstInverseProgram.colorsPolynomial
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+60*(Q+1)^2+BinaryReferenceTables.currentWorkPolynomial precision+3*Q+3+
    Q*(profileWorkPolynomial precision scalarBits+2)+2+
    BinaryWindowAverage.sumWorkPolynomial Q (BinaryReferenceTables.heightPolynomial precision) (profileHeightPolynomial precision) (3*Q+4)+6

theorem point_bounds (security : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security))
    (center : RationalBits) (scalarBits centerBits : Polynomial ℕ)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (hc : HeightBound center.decode (centerBits.eval security)) :
    HeightBound (point security scalar primary output center).data.decode ((pointHeightPolynomial centerBits).eval security) ∧
      (point security scalar primary output center).work≤(pointWorkPolynomial scalarBits centerBits).eval security := by
  let code := canonicalCounter output.val
  let anchor := BinaryMarkedFixedAnchor.current security scalar primary code.digits
  let ratio := RationalBits.quotient anchor.data center
  let H := (pointOperandHeightPolynomial centerBits).eval security
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : code.digits.length≤BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have ha := BinaryMarkedFixedAnchor.current_bounds security scalar primary code.digits scalarBits BinaryFirstInverseProgram.colorsPolynomial hs hl
  have hH : H=BinaryMarkedFixedAnchor.heightPolynomial.eval security+centerBits.eval security := by
    simp only [H,pointOperandHeightPolynomial,Polynomial.eval_add]
  have hratio : HeightBound ratio.data.decode H := by
    rw [quotient_value]
    exact (ha.1.div hc).mono (by rw [hH])
  have hminus : HeightBound minusOne.decode 0 := by rw [minusOne_value]; exact HeightBound.one.neg
  have wc : code.work≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work output.val).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  have wa : anchor.work≤(BinaryMarkedFixedAnchor.workPolynomial scalarBits BinaryFirstInverseProgram.colorsPolynomial).eval security := ha.2
  have wr : ratio.work≤2*primitiveWorkBound H+2 := quotient_work _ _ H (ha.1.mono (by rw [hH]; omega)) (hc.mono (by rw [hH]; omega))
  have wresult := RationalBits.add_work ratio.data minusOne H hratio (hminus.mono (Nat.zero_le _))
  constructor
  · change HeightBound (RationalBits.add ratio.data minusOne).data.decode _
    rw [RationalBits.add_value]
    simpa only [pointHeightPolynomial,Polynomial.eval_add,Polynomial.eval_one,add_zero,H] using hratio.add hminus
  · change code.work+anchor.work+ratio.work+(RationalBits.add ratio.data minusOne).work+4≤_
    simp only [pointWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,primitiveWorkPolynomial_eval]
    change _≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
      (BinaryMarkedFixedAnchor.workPolynomial scalarBits BinaryFirstInverseProgram.colorsPolynomial).eval security+3*primitiveWorkBound H+6
    omega

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (output : Fin (colors security)) :
    (∀ color, HeightBound ((current security (precision.eval security) scalar output).primary.get color).decode ((heightPolynomial precision).eval security)) ∧
    (∀ color, HeightBound ((current security (precision.eval security) scalar output).centered.get color).decode ((heightPolynomial precision).eval security)) ∧
    HeightBound (current security (precision.eval security) scalar output).mean.decode ((heightPolynomial precision).eval security) ∧
    HeightBound (current security (precision.eval security) scalar output).count.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) scalar output).work≤(workPolynomial precision scalarBits).eval security := by
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let center := readVector zero reference.center output
  let profile := buildArray modulus.count (fun primary => point security scalar primary output center.value)
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  let R := (BinaryReferenceTables.heightPolynomial precision).eval security
  let F := (profileHeightPolynomial precision).eval security
  have hq : modulus.count≤Q := BinaryFirstInverseProgram.colors_bound security
  have hr := BinaryReferenceTables.current_bounds security precision
  have hcenter : HeightBound center.value.decode R := by rw [readVector_value]; exact hr.2.1 output
  have hp (color : Fin (colors security)) := point_bounds security scalar color output center.value scalarBits
    (BinaryReferenceTables.heightPolynomial precision) hs hcenter
  have hprofile (color : Fin (colors security)) : HeightBound (profile.data.get color).decode F := by
    rw [buildArray_get]
    exact (hp color).1
  have hread (color : Fin (colors security)) : HeightBound (read profile.data color).data.decode F := by
    rw [read,readVector_value]
    exact hprofile color
  have wread (color : Fin (colors security)) : (read profile.data color).work≤3*modulus.count+4 := by
    have h := readVector_work zero profile.data color
    change _+1≤_
    omega
  have hm := BinaryWindowAverage.sum_bounds reference.primary (read profile.data) R F (3*modulus.count+4) hr.1 hread wread
  have wm := hm.2.trans (BinaryWindowAverage.sumWork_mono hq (le_refl R) (le_refl F) (by omega : 3*modulus.count+4≤3*Q+4))
  have wp := (buildArray_work modulus.count ((profileWorkPolynomial precision scalarBits).eval security)
    (fun primary => point security scalar primary output center.value) (fun color => (hp color).2)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 2)
  have wq := PublicParameterProgram.modulus_work security
  have wc : count.work≤60*(Q+1)^2 := (ofCounter_work modulus.count).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wr : reference.work≤(BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  have wcenter := readVector_work zero reference.center output
  change center.work≤3*modulus.count+3 at wcenter
  change modulus.work≤_ at wq
  change profile.work≤_ at wp
  have hheight : (heightPolynomial precision).eval security=R+F+Q*(R+F+1)+Q := by
    simp only [heightPolynomial,meanHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,R,F,Q]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro color
    exact (hr.1 color).mono (by rw [hheight]; omega)
  · intro color
    exact (hprofile color).mono (by rw [hheight]; omega)
  · exact hm.1.mono (by unfold BinaryWindowAverage.sumHeight; rw [hheight]; nlinarith)
  · change HeightBound count.data.decode _
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse modulus.count).mono (hq.trans (by rw [hheight]; omega))
  · change modulus.work+count.work+reference.work+center.work+profile.work+
      (BinaryWindowAverage.sum reference.primary (read profile.data)).work+6≤_
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval,BinaryWindowAverage.sumWorkPolynomial,
      BinaryWindowAverage.termWorkPolynomial,primitiveWorkPolynomial_eval]
    change _≤PublicParameterProgram.workBound security+60*(Q+1)^2+(BinaryReferenceTables.currentWorkPolynomial precision).eval security+3*Q+3+
      Q*((profileWorkPolynomial precision scalarBits).eval security+2)+2+BinaryWindowAverage.sumWork Q R F (3*Q+4)+6
    omega

end
end CurrentAFT.BinaryMarkedCenteredCache

import CurrentAFT.BinaryMarkedCenteredCache
import CurrentAFT.BinaryDensityInverseInput

/-! # Original centered marked mixed density and its actual binary inverse -/
namespace CurrentAFT.BinaryMarkedSeed
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMarkedCenteredCache.current BinaryDensityInverseInput.current PublicParameterProgram.modulus

def point {security : ℕ} (cache : BinaryMarkedCenteredCache.Result security)
    (primary : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let value := readVector zero cache.centered primary
  let atom := readVector zero cache.primary primary
  let countInverse := RationalBits.inverse cache.count
  let atomInverse := RationalBits.inverse atom.value
  let reciprocal := RationalBits.multiply countInverse.data atomInverse.data
  let correction := RationalBits.multiply reciprocal.data cache.mean
  let negative := RationalBits.negate correction.data
  let result := RationalBits.add value.value negative.data
  ⟨result.data,value.work+atom.work+countInverse.work+atomInverse.work+reciprocal.work+correction.work+negative.work+result.work+9⟩

theorem point_value (security bits : ℕ) (scalar : IntegerBits)
    (primary center : Fin (BinaryFirstInverseProgram.colors security)) :
    (point (BinaryMarkedCenteredCache.current security bits scalar center) primary).data.decode=
      RationalMarkedSeedProgram.seedDensity security bits primary.val scalar.decode center.val := by
  simp only [point,RationalBits.add_value,RationalBits.negate_value,RationalBits.multiply_value,inverse_value,
    readVector_value,BinaryMarkedCenteredCache.centered_value,BinaryMarkedCenteredCache.primary_value,
    BinaryMarkedCenteredCache.mean_value,BinaryMarkedCenteredCache.count_value,RationalMarkedSeedProgram.seedDensity,
    RationalMarkedSeedProgram.uniformRelative,BinaryMarkedCenteredCache.colors,BinaryFirstInverseProgram.colors,
    RationalMarkedSeedProgram.colors,div_eq_mul_inv,sub_eq_add_neg,one_mul]

def current (security bits : ℕ) (scalar : IntegerBits)
    (primary center : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let cache := BinaryMarkedCenteredCache.current security bits scalar center
  let result := BinaryDensityInverseInput.current security bits (point cache) primary
  ⟨result.data,cache.work+result.work+3⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits)
    (primary center : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits scalar primary center).data.decode=
      RationalMarkedSeedProgram.inverseDensity security bits scalar.decode primary.val center.val := by
  change (BinaryDensityInverseInput.current _ _ _ _).data.decode=_
  exact BinaryDensityInverseInput.current_value security bits _
    (fun color => RationalMarkedSeedProgram.seedDensity security bits color scalar.decode center.val) primary
    (fun color => point_value security bits scalar color center)

def pointWork (count bits : ℕ) := 6*count+6*primitiveWorkBound (3*bits)+15

theorem point_bounds {security : ℕ} (cache : BinaryMarkedCenteredCache.Result security)
    (primary : Fin (BinaryFirstInverseProgram.colors security)) (bits : ℕ)
    (hp : ∀ color, HeightBound (cache.primary.get color).decode bits)
    (hf : ∀ color, HeightBound (cache.centered.get color).decode bits)
    (hm : HeightBound cache.mean.decode bits) (hc : HeightBound cache.count.decode bits) :
    HeightBound (point cache primary).data.decode (4*bits+1) ∧
      (point cache primary).work≤pointWork (BinaryFirstInverseProgram.colors security) bits := by
  let value := readVector zero cache.centered primary
  let atom := readVector zero cache.primary primary
  let countInverse := RationalBits.inverse cache.count
  let atomInverse := RationalBits.inverse atom.value
  let reciprocal := RationalBits.multiply countInverse.data atomInverse.data
  let correction := RationalBits.multiply reciprocal.data cache.mean
  let negative := RationalBits.negate correction.data
  have hv : HeightBound value.value.decode bits := by rw [readVector_value]; exact hf primary
  have ha : HeightBound atom.value.decode bits := by rw [readVector_value]; exact hp primary
  have hci : HeightBound countInverse.data.decode bits := by rw [inverse_value]; exact hc.inv
  have hai : HeightBound atomInverse.data.decode bits := by rw [inverse_value]; exact ha.inv
  have hr : HeightBound reciprocal.data.decode (2*bits) := by
    rw [RationalBits.multiply_value]
    exact (hci.mul hai).mono (by omega)
  have hcorr : HeightBound correction.data.decode (3*bits) := by
    rw [RationalBits.multiply_value]
    exact (hr.mul hm).mono (by omega)
  have hn : HeightBound negative.data.decode (3*bits) := by rw [RationalBits.negate_value]; exact hcorr.neg
  have wv := readVector_work zero cache.centered primary
  have wa := readVector_work zero cache.primary primary
  change value.work≤3*BinaryFirstInverseProgram.colors security+3 at wv
  change atom.work≤3*BinaryFirstInverseProgram.colors security+3 at wa
  have wci : countInverse.work≤primitiveWorkBound (3*bits) := inverse_work cache.count (3*bits)
  have wai : atomInverse.work≤primitiveWorkBound (3*bits) := inverse_work atom.value (3*bits)
  have wr : reciprocal.work≤primitiveWorkBound (3*bits) := RationalBits.multiply_work _ _ (3*bits)
    (hci.mono (by omega)) (hai.mono (by omega))
  have wcor : correction.work≤primitiveWorkBound (3*bits) := RationalBits.multiply_work _ _ (3*bits)
    (hr.mono (by omega)) (hm.mono (by omega))
  have wn : negative.work≤primitiveWorkBound (3*bits) := RationalBits.negate_work correction.data (3*bits)
  have wresult := RationalBits.add_work value.value negative.data (3*bits) (hv.mono (by omega)) hn
  constructor
  · change HeightBound (RationalBits.add value.value negative.data).data.decode _
    rw [RationalBits.add_value]
    exact (hv.add hn).mono (by omega)
  · change value.work+atom.work+countInverse.work+atomInverse.work+reciprocal.work+correction.work+negative.work+
      (RationalBits.add value.value negative.data).work+9≤_
    unfold pointWork
    omega

noncomputable section
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  4*BinaryMarkedCenteredCache.heightPolynomial precision+1
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  6*BinaryFirstInverseProgram.colorsPolynomial+6*primitiveWorkPolynomial (3*BinaryMarkedCenteredCache.heightPolynomial precision)+15
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedCenteredCache.workPolynomial precision scalarBits+
    BinaryDensityInverseInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)+3

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (primary center : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) scalar primary center).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) scalar primary center).work≤(workPolynomial precision scalarBits).eval security := by
  let cache := BinaryMarkedCenteredCache.current security (precision.eval security) scalar center
  have hc := BinaryMarkedCenteredCache.current_bounds security precision scalarBits scalar hs center
  have hp (color : Fin (BinaryFirstInverseProgram.colors security)) := point_bounds cache color
    ((BinaryMarkedCenteredCache.heightPolynomial precision).eval security) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
  have hpoint (color : Fin (BinaryFirstInverseProgram.colors security)) :
      HeightBound (point cache color).data.decode ((pointHeightPolynomial precision).eval security) := by
    simpa only [pointHeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one] using (hp color).1
  have wpoint (color : Fin (BinaryFirstInverseProgram.colors security)) :
      (point cache color).work≤(pointWorkPolynomial precision).eval security := by
    apply (hp color).2.trans
    simp only [pointWorkPolynomial,pointWork,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (BinaryFirstInverseProgram.colors_bound security)) _) _
  have hi := BinaryDensityInverseInput.current_bounds security precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)
    (point cache) primary hpoint wpoint
  constructor
  · exact hi.1
  · change cache.work+(BinaryDensityInverseInput.current security (precision.eval security) (point cache) primary).work+3≤_
    have wcache : cache.work≤(BinaryMarkedCenteredCache.workPolynomial precision scalarBits).eval security := hc.2.2.2.2
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
    omega

end
end CurrentAFT.BinaryMarkedSeed

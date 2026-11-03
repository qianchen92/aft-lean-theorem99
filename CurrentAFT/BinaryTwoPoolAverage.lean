import CurrentAFT.BinaryDistinctTuples

/-! # Binary averaging over actual distinct choices in two pools -/
namespace CurrentAFT.BinaryTwoPoolAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → RationalResult) : RationalResult :=
  let numerator := BinaryDistinctTuples.sum primaryPool r hp (fun primary =>
    BinaryDistinctTuples.sum bodyPool s hb (kernel primary))
  let primaryMass := BinaryDistinctTuples.normalizer primaryPool r hp
  let bodyMass := BinaryDistinctTuples.normalizer bodyPool s hb
  let denominator := RationalBits.multiply primaryMass.data bodyMass.data
  let result := quotient numerator.data denominator.data
  ⟨result.data, numerator.work+primaryMass.work+bodyMass.work+denominator.work+result.work+5⟩

def normalizerHeight (pool count : ℕ) : ℕ := BinaryTupleSum.height pool count 0
def normalizerWork (pool count : ℕ) : ℕ := BinaryTupleSum.work pool count 0 (BinaryDistinctTuples.work pool count+3)
def numeratorHeight (primaryPool bodyPool r s leafHeight : ℕ) : ℕ :=
  BinaryTupleSum.height primaryPool r (BinaryTupleSum.height bodyPool s leafHeight)
def numeratorWork (primaryPool bodyPool r s leafHeight leafWork : ℕ) : ℕ :=
  BinaryTupleSum.work primaryPool r (BinaryTupleSum.height bodyPool s leafHeight)
    (BinaryDistinctTuples.work primaryPool r+
      BinaryTupleSum.work bodyPool s leafHeight (BinaryDistinctTuples.work bodyPool s+leafWork+2)+2)
def height (primaryPool bodyPool r s leafHeight : ℕ) : ℕ :=
  numeratorHeight primaryPool bodyPool r s leafHeight+normalizerHeight primaryPool r+normalizerHeight bodyPool s
def work (primaryPool bodyPool r s leafHeight leafWork : ℕ) : ℕ :=
  numeratorWork primaryPool bodyPool r s leafHeight leafWork+normalizerWork primaryPool r+normalizerWork bodyPool s+
    primitiveWorkBound (normalizerHeight primaryPool r+normalizerHeight bodyPool s)+
    2*primitiveWorkBound (height primaryPool bodyPool r s leafHeight)+7

noncomputable section
open scoped Classical

theorem current_value (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → RationalResult) :
    (current primaryPool bodyPool r s hp hb kernel).data.decode =
      (∑ primary : Fin r ↪ Fin primaryPool, ∑ body : Fin s ↪ Fin bodyPool,
        (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)/
        ((primaryPool.descFactorial r:ℚ)*(bodyPool.descFactorial s:ℚ)) := by
  simp only [current, quotient_value, RationalBits.multiply_value, BinaryDistinctTuples.normalizer_value,
    BinaryDistinctTuples.sum_value]

theorem current_bounds (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → RationalResult)
    (leafHeight leafWork : ℕ)
    (hk : ∀ first second, HeightBound (kernel first second).data.decode leafHeight)
    (hw : ∀ first second, (kernel first second).work ≤ leafWork) :
    HeightBound (current primaryPool bodyPool r s hp hb kernel).data.decode (height primaryPool bodyPool r s leafHeight) ∧
      (current primaryPool bodyPool r s hp hb kernel).work ≤ work primaryPool bodyPool r s leafHeight leafWork := by
  let numerator := BinaryDistinctTuples.sum primaryPool r hp (fun primary => BinaryDistinctTuples.sum bodyPool s hb (kernel primary))
  let first := BinaryDistinctTuples.normalizer primaryPool r hp
  let second := BinaryDistinctTuples.normalizer bodyPool s hb
  let denominator := RationalBits.multiply first.data second.data
  let N := numeratorHeight primaryPool bodyPool r s leafHeight
  let A := normalizerHeight primaryPool r
  let B := normalizerHeight bodyPool s
  let H := height primaryPool bodyPool r s leafHeight
  have hbody (first : Vector (Fin primaryPool) r) := BinaryDistinctTuples.sum_bounds bodyPool s hb (kernel first) leafHeight leafWork (hk first) (hw first)
  have hn := BinaryDistinctTuples.sum_bounds primaryPool r hp (fun primary => BinaryDistinctTuples.sum bodyPool s hb (kernel primary))
    (BinaryTupleSum.height bodyPool s leafHeight)
    (BinaryTupleSum.work bodyPool s leafHeight (BinaryDistinctTuples.work bodyPool s+leafWork+2))
    (fun first => (hbody first).1) (fun first => (hbody first).2)
  have ha := BinaryDistinctTuples.sum_bounds primaryPool r hp (fun _ => (⟨one, 1⟩ : RationalResult)) 0 1
    (fun _ => by rw [one_value]; exact HeightBound.one) (fun _ => le_refl _)
  have hb' := BinaryDistinctTuples.sum_bounds bodyPool s hb (fun _ => (⟨one, 1⟩ : RationalResult)) 0 1
    (fun _ => by rw [one_value]; exact HeightBound.one) (fun _ => le_refl _)
  have han : HeightBound first.data.decode A := ha.1
  have hbn : HeightBound second.data.decode B := hb'.1
  have hden : HeightBound denominator.data.decode (A+B) := by rw [RationalBits.multiply_value]; exact han.mul hbn
  have wm : denominator.work ≤ primitiveWorkBound (A+B) := RationalBits.multiply_work first.data second.data (A+B) (han.mono (Nat.le_add_right _ _)) (hbn.mono (Nat.le_add_left _ _))
  have hnum : HeightBound numerator.data.decode N := hn.1
  have wh := quotient_work numerator.data denominator.data H
    (hnum.mono (by unfold H height N; omega)) (hden.mono (by unfold H height A B; omega))
  have hq := hnum.div hden
  constructor
  · change HeightBound (quotient numerator.data denominator.data).data.decode _
    rw [quotient_value]
    exact hq.mono (by unfold N A B height; omega)
  · have wn : numerator.work ≤ numeratorWork primaryPool bodyPool r s leafHeight leafWork := hn.2
    have wa : first.work ≤ normalizerWork primaryPool r := by simpa only [normalizerWork, BinaryDistinctTuples.normalizer, Nat.add_assoc, Nat.reduceAdd] using ha.2
    have wb : second.work ≤ normalizerWork bodyPool s := by simpa only [normalizerWork, BinaryDistinctTuples.normalizer, Nat.add_assoc, Nat.reduceAdd] using hb'.2
    change numerator.work+first.work+second.work+denominator.work+(quotient numerator.data denominator.data).work+5 ≤ _
    unfold work
    change _ ≤ numeratorWork primaryPool bodyPool r s leafHeight leafWork+normalizerWork primaryPool r+normalizerWork bodyPool s+
      primitiveWorkBound (A+B)+2*primitiveWorkBound H+7
    omega

end
end CurrentAFT.BinaryTwoPoolAverage

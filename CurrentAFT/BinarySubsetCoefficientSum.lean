import CurrentAFT.BinaryFamilyArithmetic
import CurrentAFT.BinaryCoefficientInput

/-! Summation over a finite stored list of local subset descriptors. Each
runtime descriptor read and each rational addition is actually executed. -/
namespace CurrentAFT.BinarySubsetCoefficientSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Descriptor : Type*} {count : ℕ}

def term (order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) (index : Fin count) : RationalResult :=
  let entry := readVector fallback entries index
  let value := evaluate entry.value arity colors centers
  ⟨value.value,entry.work+value.work+2⟩

def current (order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin count (term order fallback entries evaluate arity colors centers)
    ⟨result.data,result.work+1⟩

theorem current_value (order base : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order)
    (ideal : Descriptor → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ index arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      (evaluate (entries.get index) arity colors centers).value.decode=ideal (entries.get index) arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    (current order fallback entries evaluate arity colors centers).value.decode=
      ∑ index, ideal (entries.get index) arity colors.get centers.get := by
  simp only [current, sumFin_value, term, readVector_value, hvalue _ _ _ _ hc hb]

noncomputable section
open scoped Classical

theorem sum_reindex {totalSlots : ℕ} (labels : Fin count → Finset (Fin totalSlots))
    (ordering : Fin count ≃ {selected : Finset (Fin totalSlots) // selected ≠ ∅})
    (hlabels : ∀ index, labels index=(ordering index).val) (value : Finset (Fin totalSlots) → ℚ) :
    (∑ index, value (labels index)) = ∑ selected ∈ (Finset.univ : Finset (Finset (Fin totalSlots))).erase ∅, value selected := by
  simp_rw [hlabels]
  rw [Equiv.sum_comp ordering (fun selected => value selected.val)]
  exact (Finset.sum_subtype ((Finset.univ : Finset (Finset (Fin totalSlots))).erase ∅)
    (fun selected => by simp) value).symm

theorem full_reindex {totalSlots : ℕ} (labels : Fin count → Finset (Fin totalSlots))
    (ordering : Fin count ≃ Finset (Fin totalSlots)) (hlabels : ∀ index, labels index=ordering index)
    (value : Finset (Fin totalSlots) → ℚ) : (∑ index, value (labels index)) = ∑ selected, value selected := by
  simp_rw [hlabels]
  exact Equiv.sum_comp ordering value

noncomputable def heightPolynomial (count : ℕ) (leafBits : Polynomial ℕ) : Polynomial ℕ := Polynomial.C count*(leafBits+1)
noncomputable def workPolynomial (count : ℕ) (leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C count*(Polynomial.C (3*count+5)+leafWork+primitiveWorkPolynomial (Polynomial.C (count+1)*(leafBits+1))+2)+3

theorem current_bounds (order base security : ℕ) (fallback : Descriptor) (entries : Vector Descriptor count)
    (evaluate : Descriptor → CoefficientProgram order) (leafBits leafWork : Polynomial ℕ)
    (hentry : ∀ index arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
      HeightBound (evaluate (entries.get index) arity colors centers).value.decode (leafBits.eval security) ∧
        (evaluate (entries.get index) arity colors centers).work ≤ leafWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hb : ∀ i, centers.get i<base) :
    HeightBound (current order fallback entries evaluate arity colors centers).value.decode ((heightPolynomial count leafBits).eval security) ∧
      (current order fallback entries evaluate arity colors centers).work ≤ (workPolynomial count leafBits leafWork).eval security := by
  have hh (index : Fin count) : HeightBound (term order fallback entries evaluate arity colors centers index).data.decode (leafBits.eval security) := by
    simp only [term, readVector_value]
    exact (hentry index arity colors centers hc hb).1
  have hw (index : Fin count) : (term order fallback entries evaluate arity colors centers index).work ≤ 3*count+5+leafWork.eval security := by
    have hr := readVector_work fallback entries index
    have he : (evaluate (readVector fallback entries index).value arity colors centers).work ≤ leafWork.eval security := by
      rw [readVector_value]
      exact (hentry index arity colors centers hc hb).2
    change _+_+2 ≤ _
    omega
  have h := sumFin_height count (leafBits.eval security) _ hh
  have w := sumFin_work count (leafBits.eval security) (3*count+5+leafWork.eval security) _ hh hw
  constructor
  · simpa only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one] using h
  · change (sumFin count _).work+1 ≤ _
    simp only [workPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_ofNat,
      Polynomial.eval_one, primitiveWorkPolynomial_eval]
    omega

end
end CurrentAFT.BinarySubsetCoefficientSum

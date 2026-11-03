import CurrentAFT.BinaryFamilyPower
import CurrentAFT.RationalFamilyWordProduct

/-! Executed heterogeneous products of fixed-order local coefficient tables.
The public metadata for each leaf is read from its stored vector whenever a
product program requests it. No coefficient evaluation oracle is introduced. -/
namespace CurrentAFT.BinaryFamilyWordProduct
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def product (order : ℕ) (programs : List (Entry order)) :
    (count : ℕ) → (Fin count → CoefficientProgram order) → CoefficientProgram order
  | 0, _ => BinaryFamilyPower.unit order
  | count+1, tables => BinaryFamilyArithmetic.multiply order programs
      (product order programs count (fun index => tables index.succ)) (tables 0)


def storedTerm {Metadata : Type*} {count : ℕ} (order : ℕ) (fallback : Metadata) (items : Vector Metadata count)
    (evaluate : Metadata → CoefficientProgram order) (index : Fin count) : CoefficientProgram order :=
  fun arity colors centers =>
    let selected := readVector fallback items index
    let result := evaluate selected.value arity colors centers
    ⟨result.value, selected.work + result.work + count + 3⟩


def current {Metadata : Type*} {count : ℕ} (order : ℕ) (programs : List (Entry order))
    (fallback : Metadata) (items : Vector Metadata count) (evaluate : Metadata → CoefficientProgram order) :
    CoefficientProgram order := product order programs count (storedTerm order fallback items evaluate)

noncomputable section
open scoped BigOperators Classical

 theorem product_value (order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (count : ℕ) (tables : Fin count → CoefficientProgram order)
    (ideal : Fin count → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ index arity colors centers, (tables index arity colors centers).value.decode = ideal index arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (product order programs count tables arity colors centers).value.decode =
      RationalFamilyWordProduct.current order count ideal arity colors.get centers.get := by
  induction count generalizing arity colors centers with
  | zero => exact BinaryFamilyPower.unit_value order arity colors centers
  | succ count ih =>
    exact BinaryFamilyArithmetic.multiply_value order programs hcorrect hcomplete
      (product order programs count (fun index => tables index.succ)) (tables 0)
      (RationalFamilyWordProduct.current order count (fun index => ideal index.succ)) (ideal 0)
      (ih (fun index => tables index.succ) (fun index => ideal index.succ) (fun index => hvalue index.succ))
      (hvalue 0) arity colors centers

 theorem storedTerm_value {Metadata : Type*} {count : ℕ} (order : ℕ) (fallback : Metadata) (items : Vector Metadata count)
    (evaluate : Metadata → CoefficientProgram order) (index : Fin count) (arity : TruncatedArity order)
    (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (storedTerm order fallback items evaluate index arity colors centers).value =
      (evaluate (items.get index) arity colors centers).value := by
  simp only [storedTerm, readVector_value]

 theorem current_value {Metadata : Type*} {count : ℕ} (order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : Metadata) (items : Vector Metadata count) (evaluate : Metadata → CoefficientProgram order)
    (ideal : Metadata → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ data arity colors centers, (evaluate data arity colors centers).value.decode = ideal data arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current order programs fallback items evaluate arity colors centers).value.decode =
      RationalFamilyWordProduct.current order count (fun index => ideal (items.get index)) arity colors.get centers.get := by
  apply product_value order programs hcorrect hcomplete count _ _
  intro index arity colors centers
  rw [storedTerm_value, hvalue]

 theorem product_polynomial_bounds (order base security : ℕ) (programs : List (Entry order))
    (count : ℕ) (tables : Fin count → CoefficientProgram order) (bits budget : Polynomial ℕ)
    (htable : ∀ index arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (tables index arity colors centers).value.decode (bits.eval security) ∧
        (tables index arity colors centers).work ≤ budget.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (product order programs count tables arity colors centers).value.decode
      ((BinaryFamilyPower.heightPolynomial order programs bits count).eval security) ∧
    (product order programs count tables arity colors centers).work ≤
      (BinaryFamilyPower.workPolynomial order programs bits budget count).eval security := by
  induction count generalizing arity colors centers with
  | zero => simpa only [product, BinaryFamilyPower.heightPolynomial, BinaryFamilyPower.workPolynomial,
      Polynomial.eval_zero, Polynomial.eval_C] using BinaryFamilyPower.unit_bounds order arity colors centers
  | succ count ih =>
    have hp : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
        HeightBound (product order programs count (fun index => tables index.succ) arity colors centers).value.decode
          (((BinaryFamilyPower.heightPolynomial order programs bits count).eval security)+bits.eval security) ∧
        (product order programs count (fun index => tables index.succ) arity colors centers).work ≤
          ((BinaryFamilyPower.workPolynomial order programs bits budget count).eval security)+budget.eval security := by
      intro arity colors centers hc hb
      have h := ih (fun index => tables index.succ) (fun index => htable index.succ) arity colors centers hc hb
      exact ⟨h.1.mono (Nat.le_add_right _ _), h.2.trans (Nat.le_add_right _ _)⟩
    have hs : ∀ arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
        HeightBound (tables 0 arity colors centers).value.decode
          (((BinaryFamilyPower.heightPolynomial order programs bits count).eval security)+bits.eval security) ∧
        (tables 0 arity colors centers).work ≤
          ((BinaryFamilyPower.workPolynomial order programs bits budget count).eval security)+budget.eval security := by
      intro arity colors centers hc hb
      have h := htable 0 arity colors centers hc hb
      exact ⟨h.1.mono (Nat.le_add_left _ _), h.2.trans (Nat.le_add_left _ _)⟩
    simpa only [product, BinaryFamilyPower.heightPolynomial, BinaryFamilyPower.workPolynomial,
      BinaryFamilyArithmetic.heightPolynomial_eval, BinaryFamilyArithmetic.workPolynomial_eval, Polynomial.eval_add] using
      BinaryFamilyArithmetic.multiply_bounds order base _ _ programs _ _ hp hs arity colors centers hcolors hcenters


def heightPolynomial (order limit : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryFamilyPower.heightPolynomial order programs bits count


def workPolynomial (order limit : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryFamilyPower.workPolynomial order programs bits (budget+Polynomial.C (4*limit+6)) count

 theorem current_polynomial_bounds {Metadata : Type*} {count : ℕ} (order limit base security : ℕ)
    (hcount : count ≤ limit) (programs : List (Entry order)) (fallback : Metadata) (items : Vector Metadata count)
    (evaluate : Metadata → CoefficientProgram order) (bits budget : Polynomial ℕ)
    (hleaf : ∀ data arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (evaluate data arity colors centers).value.decode (bits.eval security) ∧
        (evaluate data arity colors centers).work ≤ budget.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hcolors : ∀ i, colors.get i < base) (hcenters : ∀ i, centers.get i < base) :
    HeightBound (current order programs fallback items evaluate arity colors centers).value.decode
      ((heightPolynomial order limit programs bits).eval security) ∧
    (current order programs fallback items evaluate arity colors centers).work ≤
      (workPolynomial order limit programs bits budget).eval security := by
  have ht : ∀ index arity colors centers, (∀ i, colors.get i < base) → (∀ i, centers.get i < base) →
      HeightBound (storedTerm order fallback items evaluate index arity colors centers).value.decode (bits.eval security) ∧
        (storedTerm order fallback items evaluate index arity colors centers).work ≤ (budget+Polynomial.C (4*limit+6)).eval security := by
    intro index arity colors centers hc hb
    have h := hleaf (readVector fallback items index).value arity colors centers hc hb
    have hr := readVector_work fallback items index
    refine ⟨h.1, ?_⟩
    change (readVector fallback items index).work + (evaluate _ arity colors centers).work + count + 3 ≤ _
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  have h := product_polynomial_bounds order base security programs count (storedTerm order fallback items evaluate) bits
    (budget+Polynomial.C (4*limit+6)) ht arity colors centers hcolors hcenters
  have hh : (BinaryFamilyPower.heightPolynomial order programs bits count).eval security ≤
      (heightPolynomial order limit programs bits).eval security := by
    simp only [heightPolynomial, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun index => (BinaryFamilyPower.heightPolynomial order programs bits index).eval security)
      (a := count) (s := Finset.range (limit+1)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hw : (BinaryFamilyPower.workPolynomial order programs bits (budget+Polynomial.C (4*limit+6)) count).eval security ≤
      (workPolynomial order limit programs bits budget).eval security := by
    simp only [workPolynomial, Polynomial.eval_finset_sum]
    exact Finset.single_le_sum (f := fun index => (BinaryFamilyPower.workPolynomial order programs bits (budget+Polynomial.C (4*limit+6)) index).eval security)
      (a := count) (s := Finset.range (limit+1)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  exact ⟨h.1.mono hh, h.2.trans hw⟩

end
end CurrentAFT.BinaryFamilyWordProduct

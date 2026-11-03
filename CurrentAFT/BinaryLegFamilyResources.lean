import CurrentAFT.BinaryLegFamily

/-! # Full joint subset-table production with every stored read charged -/
namespace CurrentAFT.BinaryLegFamily
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
open BinaryLegSelectedCoefficient
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def leafHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ index : Fin 8, BinaryLegSelectedCoefficient.heightPolynomial (entries.get index) precision inputBits
def leafWorkPolynomial (order lower : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*lower+13)+∑ index : Fin 8,
    BinaryLegSelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork

theorem guarded_bounds (security order lower : ℕ) (entries : Vector Entry 8) (index : Fin 8)
    (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (guarded security (precision.eval security) order lower (entries.get index) mass arity colors centers).value.decode
      ((leafHeightPolynomial entries precision inputBits).eval security) ∧
      (guarded security (precision.eval security) order lower (entries.get index) mass arity colors centers).work ≤
        (leafWorkPolynomial order lower entries precision inputBits inputWork).eval security := by
  let entry := entries.get index
  change HeightBound (guarded security (precision.eval security) order lower entry mass arity colors centers).value.decode _ ∧
    (guarded security (precision.eval security) order lower entry mass arity colors centers).work ≤ _
  have h := BinaryLegSelectedCoefficient.current_bounds security order entry precision inputBits inputWork mass hh hw arity colors centers hc hd
  have hH : (BinaryLegSelectedCoefficient.heightPolynomial entry precision inputBits).eval security ≤
      (leafHeightPolynomial entries precision inputBits).eval security := by
    rw [leafHeightPolynomial,Polynomial.eval_finset_sum]
    simpa only [entry] using Finset.single_le_sum
      (f := fun index : Fin 8 => (BinaryLegSelectedCoefficient.heightPolynomial (entries.get index) precision inputBits).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hW : (BinaryLegSelectedCoefficient.workPolynomial order entry precision inputBits inputWork).eval security ≤
      (∑ index : Fin 8, BinaryLegSelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork).eval security := by
    rw [Polynomial.eval_finset_sum]
    simpa only [entry] using Finset.single_le_sum
      (f := fun index : Fin 8 => (BinaryLegSelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork).eval security)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hcard : entry.selected.card≤3 := by simpa only [Fintype.card_fin] using Finset.card_le_univ entry.selected
  have wg : (lessCounter (lower-1) entry.selected.card).work≤3*lower+11 :=
    (lessCounter_work _ _).trans (by omega)
  by_cases ht : (lessCounter (lower-1) entry.selected.card).value=true
  · simp only [guarded,if_pos ht]
    constructor
    · exact h.1.mono hH
    · simp only [leafWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
      have wh : (BinaryLegSelectedCoefficient.current security (precision.eval security) order entry mass arity colors centers).work ≤
          (∑ index : Fin 8, BinaryLegSelectedCoefficient.workPolynomial order (entries.get index) precision inputBits inputWork).eval security :=
        h.2.trans hW
      omega
  · simp only [guarded,if_neg ht,zero_value]
    exact ⟨HeightBound.zero.mono (Nat.zero_le _),by simp only [leafWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]; omega⟩

def sumHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.heightPolynomial 8 (leafHeightPolynomial entries precision inputBits)
def sumWorkPolynomial (order lower : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  BinarySubsetCoefficientSum.workPolynomial 8 (leafHeightPolynomial entries precision inputBits)
    (leafWorkPolynomial order lower entries precision inputBits inputWork)

theorem sum_bounds (security order lower : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (sum security (precision.eval security) order lower fallback entries mass arity colors centers).value.decode
      ((sumHeightPolynomial entries precision inputBits).eval security) ∧
      (sum security (precision.eval security) order lower fallback entries mass arity colors centers).work ≤
        (sumWorkPolynomial order lower entries precision inputBits inputWork).eval security :=
  BinarySubsetCoefficientSum.current_bounds order (BinaryFirstInverseProgram.colors security) security fallback entries
    (fun entry => guarded security (precision.eval security) order lower entry mass)
    (leafHeightPolynomial entries precision inputBits) (leafWorkPolynomial order lower entries precision inputBits inputWork)
    (fun index => guarded_bounds security order lower entries index precision inputBits inputWork mass hh hw) arity colors centers hc hd

def positiveHeightPolynomial (entries : Vector Entry 8) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  sumHeightPolynomial entries precision inputBits+1
def positiveWorkPolynomial (order : ℕ) (entries : Vector Entry 8) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+8)+sumWorkPolynomial order 1 entries precision inputBits inputWork+
    primitiveWorkPolynomial (sumHeightPolynomial entries precision inputBits)

theorem positive_bounds (security order : ℕ) (fallback : Entry) (entries : Vector Entry 8)
    (precision inputBits inputWork : Polynomial ℕ)
    (mass : Vector (Fin (BinaryFirstInverseProgram.colors security)) 3 → RationalResult)
    (hh : ∀ source, HeightBound (mass source).data.decode (inputBits.eval security))
    (hw : ∀ source, (mass source).work ≤ inputWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (positive security (precision.eval security) order fallback entries mass arity colors centers).value.decode
      ((positiveHeightPolynomial entries precision inputBits).eval security) ∧
      (positive security (precision.eval security) order fallback entries mass arity colors centers).work ≤
        (positiveWorkPolynomial order entries precision inputBits inputWork).eval security := by
  let unit := BinaryFamilyPower.unit order arity colors centers
  let terms := sum security (precision.eval security) order 1 fallback entries mass arity colors centers
  have hu := BinaryFamilyPower.unit_bounds order arity colors centers
  have ht := sum_bounds security order 1 fallback entries precision inputBits inputWork mass hh hw arity colors centers hc hd
  have wm := RationalBits.add_work unit.value terms.value ((sumHeightPolynomial entries precision inputBits).eval security)
    (hu.1.mono (Nat.zero_le _)) ht.1
  constructor
  · change HeightBound (RationalBits.add unit.value terms.value).data.decode _
    rw [RationalBits.add_value]
    simpa only [positiveHeightPolynomial,Polynomial.eval_add,Polynomial.eval_one,zero_add] using hu.1.add ht.1
  · change unit.work+terms.work+(RationalBits.add unit.value terms.value).work+2 ≤ _
    have wu : unit.work≤12*order+6 := hu.2
    have wt : terms.work ≤ (sumWorkPolynomial order 1 entries precision inputBits inputWork).eval security := ht.2
    simp only [positiveWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C,primitiveWorkPolynomial_eval]
    omega

end
end CurrentAFT.BinaryLegFamily

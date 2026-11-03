import CurrentAFT.BinaryReferenceTables
import CurrentAFT.FamilyProductSyntax
import CurrentAFT.WeightedPointKernelProgram

/-! Executed reference-weighted canonical point columns. Slot permutations are
finite stored arithmetic syntax fixed before security; each dynamic atom reads
its two palette positions and the generated proposal table. -/
namespace CurrentAFT.BinaryWeightedPointKernel
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current

abbrev Color (security : ℕ) := Fin (PublicParameterProgram.modulus security).count
abbrev Atom (r s : ℕ) := (Fin r × Fin r) ⊕ (Fin s × Fin s)
abbrev Program (r s : ℕ) := StoredScalarProgram (Atom r s) RationalBits

def firstColor (security : ℕ) : Color security :=
  ⟨0, by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.pos⟩

def factor {degree : ℕ} (security : ℕ) (table : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (source output : Vector (Color security) degree) (indices : Fin degree × Fin degree) : CountedValue RationalBits :=
  let input := readVector (firstColor security) source indices.1
  let color := readVector (firstColor security) output indices.2
  let matched := equalCounter color.value.val input.value.val
  let reference := readVector RationalBits.zero table input.value
  let negative := RationalBits.negate reference.value
  let difference := RationalBits.add (if matched.value then RationalBits.one else RationalBits.zero) negative.data
  ⟨difference.data,input.work+color.work+matched.work+reference.work+negative.work+difference.work+6⟩

 theorem factor_value {degree : ℕ} (security : ℕ) (table : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (source output : Vector (Color security) degree) (indices : Fin degree × Fin degree) :
    (factor security table source output indices).value.decode =
      (if (output.get indices.2).val = (source.get indices.1).val then 1 else 0) -
        (table.get (source.get indices.1)).decode := by
  simp only [factor,readVector_value,RationalBits.add_value,RationalBits.negate_value]
  by_cases h : (equalCounter (output.get indices.2).val (source.get indices.1).val).value = true
  · simp only [if_pos h,if_pos ((equalCounter_value _ _).mp h),RationalBits.one_value,sub_eq_add_neg]
  · simp only [if_neg h,if_neg (fun he => h ((equalCounter_value _ _).mpr he)),RationalBits.zero_value,sub_eq_add_neg]


def atom {r s : ℕ} (security : ℕ) (tables : BinaryReferenceTables.Result security)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) :
    Atom r s → CountedValue RationalBits
  | .inl indices => factor security tables.primary sourcePrimary colors indices
  | .inr indices => factor security tables.center sourceBody centers indices


def withTables {r s : ℕ} (security : ℕ) (program : Program r s) (tables : BinaryReferenceTables.Result security)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) : RationalResult :=
  let result := program.binaryRun (atom security tables sourcePrimary colors sourceBody centers)
  ⟨result.value,result.work+1⟩


def current {r s : ℕ} (security bits : ℕ) (program : Program r s)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) : RationalResult :=
  let tables := BinaryReferenceTables.current security bits
  let result := withTables security program tables sourcePrimary colors sourceBody centers
  ⟨result.data,tables.work+result.work+1⟩


def productList {Index : Type*} : List (ScalarProgram Index) → ScalarProgram Index
  | [] => .rational 1
  | head::tail => .multiply head (productList tail)

 theorem productList_run {Index : Type*} (leaf : Index → ℚ) (list : List (ScalarProgram Index)) :
    (productList list).run leaf = (list.map (fun program => program.run leaf)).prod := by
  induction list with
  | nil => rfl
  | cons head tail ih => simp only [productList,ScalarProgram.run,List.map_cons,List.prod_cons,ih]

noncomputable section
open scoped Classical


def product {Index Leaf : Type*} [Fintype Index] (term : Index → ScalarProgram Leaf) : ScalarProgram Leaf :=
  productList (List.ofFn (fun index : Fin (Fintype.card Index) => term ((Fintype.equivFin Index).symm index)))

 theorem product_run {Index Leaf : Type*} [Fintype Index] (leaf : Leaf → ℚ) (term : Index → ScalarProgram Leaf) :
    (product term).run leaf = ∏ index, (term index).run leaf := by
  rw [product,productList_run,List.map_ofFn,List.prod_ofFn]
  exact Equiv.prod_comp (Fintype.equivFin Index).symm (fun index => (term index).run leaf)


def pointSyntax (r s : ℕ) : ScalarProgram (Atom r s) :=
  .multiply (.rational ((r.factorial:ℚ)⁻¹*(s.factorial:ℚ)⁻¹))
    (FamilyProductSyntax.sum (fun primaryOrder : Equiv.Perm (Fin r) =>
      FamilyProductSyntax.sum (fun bodyOrder : Equiv.Perm (Fin s) =>
        .multiply (product (fun index : Fin r => .atom (.inl (index,primaryOrder index))))
          (product (fun index : Fin s => .atom (.inr (index,bodyOrder index)))))))

 theorem exists_stored (r s : ℕ) : ∃ program : Program r s, program.meaning RationalBits.decode = pointSyntax r s :=
  ScalarProgram.exists_binaryStored (pointSyntax r s)

 theorem current_value {r s : ℕ} (security bits : ℕ) (program : Program r s)
    (hprogram : program.meaning RationalBits.decode = pointSyntax r s)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) :
    (current security bits program sourcePrimary colors sourceBody centers).data.decode =
      WeightedPointKernelProgram.current security bits r s (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) (fun index => (colors.get index).val) (fun index => (centers.get index).val) := by
  change (program.binaryRun _).value.decode = _
  rw [StoredScalarProgram.binaryRun_value,hprogram]
  simp only [pointSyntax,ScalarProgram.run,FamilyProductSyntax.sum_run,product_run,atom,factor_value,
    BinaryReferenceTables.primary_value,BinaryReferenceTables.center_value,WeightedPointKernelProgram.current,
    RationalFamilyProductProgram.average,RationalPrimaryColumnProgram.centerDelta,WeightedPointKernelProgram.bodyDelta]


def atomWorkPolynomial (limit : ℕ) (height : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryProposalMetadata.sizePolynomial
  Polynomial.C (6*limit)+9*Q+2*RationalBits.primitiveWorkPolynomial (height+1)+30

 theorem factor_bounds {degree : ℕ} (security limit : ℕ) (height : Polynomial ℕ)
    (table : Vector RationalBits (PublicParameterProgram.modulus security).count)
    (hh : ∀ color, HeightBound (table.get color).decode (height.eval security))
    (source output : Vector (Color security) degree) (indices : Fin degree × Fin degree) (hd : degree ≤ limit) :
    HeightBound (factor security table source output indices).value.decode ((height+1).eval security) ∧
      (factor security table source output indices).work ≤ (atomWorkPolynomial limit height).eval security := by
  let input := readVector (firstColor security) source indices.1
  let color := readVector (firstColor security) output indices.2
  let matched := equalCounter color.value.val input.value.val
  let reference := readVector RationalBits.zero table input.value
  let negative := RationalBits.negate reference.value
  let indicator := if matched.value then RationalBits.one else RationalBits.zero
  let difference := RationalBits.add indicator negative.data
  have hr : HeightBound reference.value.decode (height.eval security) := by rw [readVector_value];exact hh _
  have hi : HeightBound indicator.decode 0 := by
    dsimp only [indicator]
    split_ifs
    · exact HeightBound.one
    · exact HeightBound.zero
  have hn : HeightBound negative.data.decode (height.eval security) := by rw [RationalBits.negate_value];exact hr.neg
  constructor
  · change HeightBound difference.data.decode _
    rw [RationalBits.add_value]
    simpa only [Polynomial.eval_add,Polynomial.eval_one,Nat.zero_add] using hi.add hn
  · have wi := readVector_work (firstColor security) source indices.1
    have wo := readVector_work (firstColor security) output indices.2
    have we := equalCounter_work color.value.val input.value.val
    have wr := readVector_work RationalBits.zero table input.value
    have wn := RationalBits.negate_work reference.value ((height+1).eval security)
    have wa := RationalBits.add_work indicator negative.data ((height+1).eval security)
      (hi.mono (Nat.zero_le _)) (hn.mono (by simp only [Polynomial.eval_add,Polynomial.eval_one];omega))
    have hq : (PublicParameterProgram.modulus security).count ≤ BinaryProposalMetadata.sizePolynomial.eval security := by
      rw [BinaryProposalMetadata.sizePolynomial_eval]
      exact (PublicParameterProgram.modulus_value security) ▸ ((BinaryProposalMetadata.counts_value security).1 ▸ (BinaryProposalMetadata.counts_bounds security).1)
    have hx := input.value.isLt
    have hy := color.value.isLt
    change input.work+color.work+matched.work+reference.work+negative.work+difference.work+6 ≤ _
    change input.work ≤ _ at wi
    change color.work ≤ _ at wo
    change matched.work ≤ _ at we
    change reference.work ≤ _ at wr
    change negative.work ≤ _ at wn
    change difference.work ≤ _ at wa
    simp only [Polynomial.eval_add,Polynomial.eval_one] at wn wa
    simp only [atomWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,
      RationalBits.primitiveWorkPolynomial_eval]
    omega


def heightPolynomial {r s : ℕ} (program : Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedScalarProgram.heightPolynomial program (BinaryReferenceTables.heightPolynomial precision+1)

def workPolynomial {r s : ℕ} (program : Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryFixedScalarProgram.workPolynomial program (BinaryReferenceTables.heightPolynomial precision+1)
      (atomWorkPolynomial (r+s) (BinaryReferenceTables.heightPolynomial precision))+2

 theorem current_bounds {r s : ℕ} (security : ℕ) (precision : Polynomial ℕ) (program : Program r s)
    (sourcePrimary colors : Vector (Color security) r) (sourceBody centers : Vector (Color security) s) :
    HeightBound (current security (precision.eval security) program sourcePrimary colors sourceBody centers).data.decode
      ((heightPolynomial program precision).eval security) ∧
    (current security (precision.eval security) program sourcePrimary colors sourceBody centers).work ≤
      (workPolynomial program precision).eval security := by
  let tables := BinaryReferenceTables.current security (precision.eval security)
  have ht := BinaryReferenceTables.current_bounds security precision
  have hl (entry : Atom r s) : HeightBound (atom security tables sourcePrimary colors sourceBody centers entry).value.decode
      ((BinaryReferenceTables.heightPolynomial precision+1).eval security) ∧
      (atom security tables sourcePrimary colors sourceBody centers entry).work ≤
        (atomWorkPolynomial (r+s) (BinaryReferenceTables.heightPolynomial precision)).eval security := by
    cases entry with
    | inl indices => exact factor_bounds security (r+s) _ tables.primary ht.1 sourcePrimary colors indices (by omega)
    | inr indices => exact factor_bounds security (r+s) _ tables.center ht.2.1 sourceBody centers indices (by omega)
  constructor
  · simpa only [heightPolynomial,BinaryFixedScalarProgram.heightPolynomial_eval] using
      BinaryFixedScalarProgram.run_height program _ _ (fun entry => (hl entry).1)
  · have hw := BinaryFixedScalarProgram.run_work program _ _ _ (fun entry => (hl entry).1) (fun entry => (hl entry).2)
    change tables.work+((program.binaryRun (atom security tables sourcePrimary colors sourceBody centers)).work+1)+1 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one,BinaryFixedScalarProgram.workPolynomial_eval]
    simp only [Polynomial.eval_add,Polynomial.eval_one] at hw
    have tw := ht.2.2.2.2
    change tables.work ≤ _ at tw
    omega

end
end CurrentAFT.BinaryWeightedPointKernel

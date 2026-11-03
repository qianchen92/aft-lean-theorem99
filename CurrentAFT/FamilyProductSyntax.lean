import CurrentAFT.RationalFamilyProductProgram
import CurrentAFT.BinaryFixedScalarProgram

/-! # Fixed-order arithmetic syntax for exact joint family multiplication

The syntax and all its rational literals depend only on the fixed order
and output arity. Dynamic palette values enter exclusively through leaf
reads specified by stored slot vectors. No security-dependent literal is
encoded by the interpreter.
-/
namespace CurrentAFT.FamilyProductSyntax
open AFT RationalNumerics GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Leaf (order : ℕ) (output : TruncatedArity order) where
  second : Bool
  arity : TruncatedArity order
  primarySlots : Vector (Fin output.val.1.val) arity.val.1.val
  bodySlots : Vector (Fin output.val.2.val) arity.val.2.val

def value {Primary Body : Type*} (order : ℕ) (output : TruncatedArity order)
    (first second : Table ℚ Primary Body order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) (leaf : Leaf order output) : ℚ :=
  (if leaf.second then second else first) leaf.arity
    (fun index => colors (leaf.primarySlots.get index)) (fun index => centers (leaf.bodySlots.get index))

def sumList {Atom : Type*} : List (ScalarProgram Atom) → ScalarProgram Atom
  | [] => .rational 0
  | first::tail => .add first (sumList tail)

theorem sumList_run {Atom : Type*} (leaf : Atom → ℚ) (list : List (ScalarProgram Atom)) :
    (sumList list).run leaf = (list.map (fun program => program.run leaf)).sum := by
  induction list with
  | nil => rfl
  | cons first tail ih => simp only [sumList, ScalarProgram.run, List.map_cons, List.sum_cons, ih]

noncomputable section
open scoped Classical

def sum {Index Atom : Type*} [Fintype Index] (term : Index → ScalarProgram Atom) : ScalarProgram Atom :=
  sumList (List.ofFn (fun index : Fin (Fintype.card Index) => term ((Fintype.equivFin Index).symm index)))

theorem sum_run {Index Atom : Type*} [Fintype Index] (leaf : Atom → ℚ) (term : Index → ScalarProgram Atom) :
    (sum term).run leaf = ∑ index, (term index).run leaf := by
  rw [sum, sumList_run, List.map_ofFn, List.sum_ofFn]
  exact Equiv.sum_comp (Fintype.equivFin Index).symm (fun index => (term index).run leaf)

def splitLeaf (order : ℕ) (output left right : TruncatedArity order)
    (hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val)
    (primaryOrder : Equiv.Perm (Fin (left.val.1.val+right.val.1.val)))
    (bodyOrder : Equiv.Perm (Fin (left.val.2.val+right.val.2.val))) (useSecond : Bool) : Leaf order output :=
  if useSecond then
    ⟨true, right,
      Vector.ofFn (fun index => finCongr hmatch.1 (primaryOrder (finSumFinEquiv (Sum.inr index)))),
      Vector.ofFn (fun index => finCongr hmatch.2 (bodyOrder (finSumFinEquiv (Sum.inr index))))⟩
  else
    ⟨false, left,
      Vector.ofFn (fun index => finCongr hmatch.1 (primaryOrder (finSumFinEquiv (Sum.inl index)))),
      Vector.ofFn (fun index => finCongr hmatch.2 (bodyOrder (finSumFinEquiv (Sum.inl index))))⟩

def homogeneous (order : ℕ) (output left right : TruncatedArity order)
    (hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val) : ScalarProgram (Leaf order output) :=
  .multiply (.rational (((left.val.1.val+right.val.1.val).factorial : ℚ)⁻¹ *
    ((left.val.2.val+right.val.2.val).factorial : ℚ)⁻¹))
    (sum (fun primaryOrder => sum (fun bodyOrder =>
      .multiply (.atom (splitLeaf order output left right hmatch primaryOrder bodyOrder false))
        (.atom (splitLeaf order output left right hmatch primaryOrder bodyOrder true)))))

def product (order : ℕ) (output : TruncatedArity order) : ScalarProgram (Leaf order output) :=
  sum (fun left : TruncatedArity order => sum (fun right : TruncatedArity order =>
    if hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val then
        homogeneous order output left right hmatch else .rational 0))

theorem homogeneous_run {Primary Body : Type*} (order : ℕ) (output left right : TruncatedArity order)
    (hmatch : left.val.1.val+right.val.1.val = output.val.1.val ∧
      left.val.2.val+right.val.2.val = output.val.2.val)
    (first second : Table ℚ Primary Body order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    (homogeneous order output left right hmatch).run (value order output first second colors centers) =
      RationalFamilyProductProgram.homogeneous (first left) (second right)
        (colors ∘ finCongr hmatch.1) (centers ∘ finCongr hmatch.2) := by
  simp only [homogeneous, ScalarProgram.run, sum_run, RationalFamilyProductProgram.homogeneous,
    average, tensor, splitLeaf, Bool.false_eq_true, if_false, if_true, value, Vector.get_ofFn,
    Function.comp_def]

theorem product_run {Primary Body : Type*} (order : ℕ) (output : TruncatedArity order)
    (first second : Table ℚ Primary Body order) (colors : Fin output.val.1.val → Primary)
    (centers : Fin output.val.2.val → Body) :
    (product order output).run (value order output first second colors centers) =
      RationalFamilyProductProgram.product order first second output colors centers := by
  simp only [product, sum_run, RationalFamilyProductProgram.product]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · exact homogeneous_run order output left right hmatch first second colors centers
  · rfl

/-- Stored syntax is selected once for each fixed order and arity, before
any security parameter, public palette values, or randomness are supplied. -/
theorem exists_stored (order : ℕ) (output : TruncatedArity order) :
    ∃ stored : StoredScalarProgram (Leaf order output) BinaryArithmetic.RationalBits,
      stored.meaning BinaryArithmetic.RationalBits.decode = product order output :=
  ScalarProgram.exists_binaryStored (product order output)

end
end CurrentAFT.FamilyProductSyntax

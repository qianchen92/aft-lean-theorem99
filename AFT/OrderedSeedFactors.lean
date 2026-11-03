import AFT.CanonicalColumnOperator
import AFT.PrimaryMonomialSeed

/-! # Finite ordered factor programs without equality tests on real kernels

The executable data keep occurrences separate.  Collisions between decoded
real seed labels are handled only by the semantic interpretation.
-/
namespace AFT.RationalNumerics

structure OrderedSeedTerm (Code : Type*) where
  coefficient : ℚ
  factors : List Code

abbrev OrderedSeedTable (Code : Type*) := List (OrderedSeedTerm Code)

def OrderedSeedTerm.scale {Code : Type*} (scalar : ℚ) (term : OrderedSeedTerm Code) : OrderedSeedTerm Code :=
  ⟨scalar*term.coefficient,term.factors⟩

def OrderedSeedTerm.multiply {Code : Type*} (first second : OrderedSeedTerm Code) : OrderedSeedTerm Code :=
  ⟨first.coefficient*second.coefficient,first.factors++second.factors⟩

def OrderedSeedTable.scale {Code : Type*} (scalar : ℚ) (table : OrderedSeedTable Code) : OrderedSeedTable Code :=
  table.map (OrderedSeedTerm.scale scalar)

def OrderedSeedTable.multiply {Code : Type*} (first second : OrderedSeedTable Code) : OrderedSeedTable Code :=
  first.flatMap (fun term => second.map term.multiply)

def OrderedSeedTable.truncate {Code : Type*} (order : Code → ℕ) (cutoff : ℕ)
    (table : OrderedSeedTable Code) : OrderedSeedTable Code :=
  table.filter (fun term => (term.factors.map order).sum ≤ cutoff)

/-- The column routine receives a concrete ordered list, never a real-kernel
map or a decision procedure for real canonicality. -/
def OrderedSeedTable.applyColumns {Code : Type*} (columns : List Code → OrderedSeedTable Code)
    (table : OrderedSeedTable Code) : OrderedSeedTable Code :=
  table.flatMap (fun term => (columns term.factors).scale term.coefficient)

/-- `depth` agrees with the mathematical finite correction: depth zero
already includes the target. -/
def OrderedSeedTable.correction {Code : Type*} (columns : List Code → OrderedSeedTable Code)
    (target : OrderedSeedTable Code) : ℕ → OrderedSeedTable Code
  | 0 => target
  | depth+1 => target ++ ((OrderedSeedTable.applyColumns columns (OrderedSeedTable.correction columns target depth)).scale (-1))

open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Code Seed : Type*}

def orderedSeedPowers (decode : Code → Seed) : List Code → (Seed →₀ ℕ)
  | [] => 0
  | code::rest => Finsupp.single (decode code) 1+orderedSeedPowers decode rest

def OrderedSeedTerm.interpret (decode : Code → Seed) (term : OrderedSeedTerm Code) : Table Seed :=
  (term.coefficient : ℝ) • (term.factors.map (fun code => MvPolynomial.X (decode code))).prod

def OrderedSeedTable.interpret (decode : Code → Seed) (table : OrderedSeedTable Code) : Table Seed :=
  (table.map (OrderedSeedTerm.interpret decode)).sum

theorem orderedSeedPowers_order (decode : Code → Seed) (order : Seed → ℕ) (factors : List Code) :
    weightedOrder order (orderedSeedPowers decode factors)=(factors.map (fun code => order (decode code))).sum := by
  induction factors with
  | nil => simp [orderedSeedPowers,weightedOrder]
  | cons code rest ih =>
    rw [orderedSeedPowers,weightedOrder_add,ih]
    simp [weightedOrder]

theorem orderedSeedPowers_support (decode : Code → Seed) (factors : List Code) {seed : Seed}
    (hs : seed∈(orderedSeedPowers decode factors).support) : ∃ code∈factors,decode code=seed := by
  induction factors with
  | nil => simp [orderedSeedPowers] at hs
  | cons code rest ih =>
    have hs := Finset.mem_union.mp (Finsupp.support_add hs)
    rcases hs with hs|hs
    · have heq : decode code=seed := by
        by_contra he
        simp only [Finsupp.mem_support_iff,Finsupp.single_eq_of_ne (Ne.symm he)] at hs
        exact hs rfl
      exact ⟨code,List.mem_cons_self,heq⟩
    · obtain ⟨other,ho,he⟩ := ih hs
      exact ⟨other,List.mem_cons_of_mem _ ho,he⟩

theorem orderedSeedPowers_monomial (decode : Code → Seed) (factors : List Code) :
    MvPolynomial.monomial (orderedSeedPowers decode factors) (1 : ℝ)=
      (factors.map (fun code => MvPolynomial.X (decode code))).prod := by
  induction factors with
  | nil => simp [orderedSeedPowers]
  | cons code rest ih =>
    change MvPolynomial.monomial (Finsupp.single (decode code) 1+orderedSeedPowers decode rest) 1 = _
    calc
      _ = MvPolynomial.monomial (Finsupp.single (decode code) 1) (1 : ℝ) *
          MvPolynomial.monomial (orderedSeedPowers decode rest) 1 := by rw [MvPolynomial.monomial_mul,mul_one]
      _ = _ := by rw [ih]; rfl

theorem OrderedSeedTerm.interpret_monomial (decode : Code → Seed) (term : OrderedSeedTerm Code) :
    term.interpret decode=MvPolynomial.monomial (orderedSeedPowers decode term.factors) (term.coefficient : ℝ) := by
  rw [OrderedSeedTerm.interpret,←orderedSeedPowers_monomial,MvPolynomial.smul_monomial,smul_eq_mul,mul_one]

theorem OrderedSeedTerm.interpret_scale (decode : Code → Seed) (scalar : ℚ) (term : OrderedSeedTerm Code) :
    (term.scale scalar).interpret decode=(scalar : ℝ) • term.interpret decode := by
  simp only [OrderedSeedTerm.interpret,OrderedSeedTerm.scale,Rat.cast_mul,mul_smul]

theorem OrderedSeedTerm.interpret_multiply (decode : Code → Seed) (first second : OrderedSeedTerm Code) :
    (first.multiply second).interpret decode=first.interpret decode*second.interpret decode := by
  simp only [OrderedSeedTerm.interpret,OrderedSeedTerm.multiply,Rat.cast_mul,List.map_append,List.prod_append,
    MvPolynomial.smul_eq_C_mul,MvPolynomial.C_mul]
  ring

@[simp] theorem OrderedSeedTable.interpret_nil (decode : Code → Seed) :
    OrderedSeedTable.interpret decode []=0 := rfl

@[simp] theorem OrderedSeedTable.interpret_cons (decode : Code → Seed) (term : OrderedSeedTerm Code)
    (table : OrderedSeedTable Code) :
    OrderedSeedTable.interpret decode (term::table)=term.interpret decode+table.interpret decode := rfl

theorem OrderedSeedTable.interpret_append (decode : Code → Seed) (first second : OrderedSeedTable Code) :
    (first++second).interpret decode=first.interpret decode+second.interpret decode := by
  simp only [OrderedSeedTable.interpret,List.map_append,List.sum_append]

theorem OrderedSeedTable.interpret_scale (decode : Code → Seed) (scalar : ℚ) (table : OrderedSeedTable Code) :
    (table.scale scalar).interpret decode=(scalar : ℝ) • table.interpret decode := by
  induction table with
  | nil => simp [OrderedSeedTable.scale]
  | cons term table ih => simpa only [OrderedSeedTable.scale,List.map_cons,interpret_cons,
      OrderedSeedTerm.interpret_scale,smul_add] using congrArg (fun value => (scalar : ℝ) • term.interpret decode+value) ih

/-- Exact linear-column interpretation. There is no bound or approximation
premise, and interpreted label collisions do not require a runtime test. -/
theorem OrderedSeedTable.interpret_applyColumns (decode : Code → Seed)
    (columns : List Code → OrderedSeedTable Code) (linear : Module.End ℝ (Table Seed))
    (table : OrderedSeedTable Code)
    (hcolumns : ∀ term∈table,(columns term.factors).interpret decode=
      linear ((term.factors.map (fun code => MvPolynomial.X (decode code))).prod)) :
    (table.applyColumns columns).interpret decode=linear (table.interpret decode) := by
  induction table with
  | nil => simp [OrderedSeedTable.applyColumns]
  | cons term table ih =>
    simp only [OrderedSeedTable.applyColumns,List.flatMap_cons,interpret_append,interpret_scale,
      interpret_cons,map_add,map_smul,OrderedSeedTerm.interpret]
    rw [hcolumns term (List.mem_cons_self ..)]
    exact congrArg (fun value => (term.coefficient : ℝ) • linear
      ((term.factors.map (fun code => MvPolynomial.X (decode code))).prod)+value)
      (ih (fun other ho => hcolumns other (List.mem_cons_of_mem _ ho)))

/-- Canonicality of decoded factors discharges the semantic column-domain
predicate, without making it part of the executable data. -/
theorem canonicalColumnLinear_ordered {Color : Type*} [Fintype Color]
    (decode : Code → InputSeed Color) (primary body : FiniteDist Color)
    (order : InputSeed Color → ℕ) (cutoff : ℕ)
    (columns : (InputSeed Color →₀ ℕ) → Table (InputSeed Color)) (term : OrderedSeedTerm Code)
    (horder : (term.factors.map (fun code => order (decode code))).sum ≤ cutoff)
    (hc : ∀ code∈term.factors,Hoeffding.Canonical (inputReference primary body (decode code)) Finset.univ (decode code).kernel) :
    canonicalColumnLinear primary body order cutoff columns (term.interpret decode)=
      (term.coefficient : ℝ) • truncate order cutoff (columns (orderedSeedPowers decode term.factors)) := by
  rw [OrderedSeedTerm.interpret_monomial]
  apply canonicalColumnLinear_monomial
  constructor
  · rwa [orderedSeedPowers_order]
  · intro seed hs
    obtain ⟨code,hm,rfl⟩ := orderedSeedPowers_support decode term.factors hs
    exact hc code hm

end
end AFT.RationalNumerics

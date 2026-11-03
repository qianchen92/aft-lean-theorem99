import AFT.OrderedSeedFactors
import AFT.Correction

/-! # Executable ordered products and finite reciprocal factors -/
namespace AFT.RationalNumerics

def OrderedSeedTable.power {Code : Type*} (table : OrderedSeedTable Code) : ℕ → OrderedSeedTable Code
  | 0 => [⟨1,[]⟩]
  | count+1 => (table.power count).multiply table

def OrderedSeedTable.reciprocal {Code : Type*} (table : OrderedSeedTable Code) (depth : ℕ) : OrderedSeedTable Code :=
  (List.range (depth+1)).flatMap (fun count => (table.power count).scale ((-1 : ℚ)^count))

open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Code Seed : Type*}

theorem OrderedSeedTable.interpret_multiply (decode : Code → Seed) (first second : OrderedSeedTable Code) :
    (first.multiply second).interpret decode=first.interpret decode*second.interpret decode := by
  have hmap (term : OrderedSeedTerm Code) (other : OrderedSeedTable Code) :
      OrderedSeedTable.interpret decode (other.map term.multiply)=term.interpret decode*other.interpret decode := by
    induction other with
    | nil => simp
    | cons item other ih =>
      simp only [List.map_cons,interpret_cons,OrderedSeedTerm.interpret_multiply,mul_add,ih]
  induction first with
  | nil => simp [multiply]
  | cons term rest ih =>
    simp only [multiply,List.flatMap_cons,interpret_append,interpret_cons,add_mul]
    rw [hmap]
    exact congrArg (term.interpret decode*second.interpret decode+·) ih

theorem OrderedSeedTable.interpret_power (decode : Code → Seed) (table : OrderedSeedTable Code) (count : ℕ) :
    (table.power count).interpret decode=(table.interpret decode)^count := by
  induction count with
  | zero => simp [power,OrderedSeedTerm.interpret]
  | succ count ih => rw [power,interpret_multiply,ih,pow_succ]

theorem OrderedSeedTable.interpret_reciprocal (decode : Code → Seed) (table : OrderedSeedTable Code) (depth : ℕ) :
    (table.reciprocal depth).interpret decode=finiteCorrection (table.interpret decode) depth := by
  have hs (count : ℕ) : OrderedSeedTable.interpret decode ((List.range count).flatMap
      (fun index => (table.power index).scale ((-1 : ℚ)^index)))=
      ∑ index∈Finset.range count,(-(table.interpret decode))^index := by
    induction count with
    | zero => simp
    | succ count ih =>
      rw [List.range_succ,List.flatMap_append,interpret_append,Finset.sum_range_succ,ih]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,interpret_scale,interpret_power,
        Rat.cast_pow,Rat.cast_neg,Rat.cast_one,MvPolynomial.smul_eq_C_mul,map_pow,map_neg,map_one]
      congr 1
      exact (neg_pow (table.interpret decode) count).symm
  exact hs (depth+1)

theorem OrderedSeedTable.multiply_length (first second : OrderedSeedTable Code) :
    (first.multiply second).length=first.length*second.length := by
  induction first with
  | nil => simp [multiply]
  | cons term rest ih => simpa only [multiply,List.flatMap_cons,List.length_append,List.length_map,
      List.length_cons,Nat.add_mul,Nat.one_mul,add_comm] using congrArg (second.length+·) ih

theorem OrderedSeedTable.power_length (table : OrderedSeedTable Code) (count : ℕ) :
    (table.power count).length=table.length^count := by
  induction count with
  | zero => simp [power]
  | succ count ih => rw [power,multiply_length,ih,pow_succ]

/-- Fixed-depth expansion has a fixed power of the actual finite local
column size; no compression or equality of decoded labels is required. -/
theorem OrderedSeedTable.reciprocal_length (table : OrderedSeedTable Code) (depth : ℕ) :
    (table.reciprocal depth).length=∑ count∈Finset.range (depth+1),table.length^count := by
  have hs (count : ℕ) : ((List.range count).flatMap
      (fun index => (table.power index).scale ((-1 : ℚ)^index))).length=
      ∑ index∈Finset.range count,table.length^index := by
    induction count with
    | zero => simp
    | succ count ih =>
      rw [List.range_succ,List.flatMap_append,List.length_append,Finset.sum_range_succ,ih]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,scale,List.length_map,power_length]
  exact hs (depth+1)

end
end AFT.RationalNumerics

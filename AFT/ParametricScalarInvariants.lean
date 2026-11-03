import AFT.ScalarProgramApproximation
import AFT.ParametricWholeBoundary

/-! # Scalar syntax and fixed node bounds through the actual U/J transforms -/
namespace AFT.RationalNumerics

 def ParametricSeedTable.ScalarSafe {Scalar Code : Type*} (table : ParametricSeedTable Scalar Code) : Prop :=
  ∀ term∈table,term.coefficient.exactInverseSyntax

 theorem ParametricSeedTable.ScalarSafe.append {Scalar Code : Type*} {first second : ParametricSeedTable Scalar Code}
    (hf : first.ScalarSafe) (hs : second.ScalarSafe) : (first++second).ScalarSafe := by
  intro term ht
  rcases List.mem_append.mp ht with ht|ht
  · exact hf term ht
  · exact hs term ht

 theorem ParametricSeedTable.ScalarSafe.scale {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (scalar : ScalarProgram Scalar) (hs : scalar.exactInverseSyntax) :
    (table.scale scalar).ScalarSafe := by
  intro term ht
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp ht
  exact ⟨hs,h old ho⟩

 theorem ParametricSeedTable.ScalarSafe.rename {Scalar Code Other : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (rename : Code → Other) : (table.rename rename).ScalarSafe := by
  intro term ht
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp ht
  exact h old ho

 theorem ParametricSeedTable.ScalarSafe.multiply {Scalar Code : Type*} {first second : ParametricSeedTable Scalar Code}
    (hf : first.ScalarSafe) (hs : second.ScalarSafe) : (first.multiply second).ScalarSafe := by
  intro term ht
  obtain ⟨left,hl,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨right,hr,rfl⟩ := List.mem_map.mp ht
  exact ⟨hf left hl,hs right hr⟩

 theorem ParametricSeedTable.ScalarSafe.one {Scalar Code : Type*} :
    (ParametricSeedTable.one : ParametricSeedTable Scalar Code).ScalarSafe := by
  intro term ht
  simp only [ParametricSeedTable.one,List.mem_singleton] at ht
  subst term
  trivial

 theorem ParametricSeedTable.ScalarSafe.power {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (count : ℕ) : (table.power count).ScalarSafe := by
  induction count with
  | zero => exact .one
  | succ count ih => exact ih.multiply h

 theorem ParametricSeedTable.ScalarSafe.truncate {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (order : Code → ℕ) (cutoff : ℕ) : (table.truncate order cutoff).ScalarSafe := by
  intro term ht
  exact h term (List.mem_filter.mp ht).1

 theorem ParametricSeedTable.ScalarSafe.exponential {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (cutoff : ℕ) : (table.exponential cutoff).ScalarSafe := by
  intro term ht
  obtain ⟨count,_,ht⟩ := List.mem_flatMap.mp ht
  exact ((h.power count).scale (.rational ((count.factorial : ℚ)⁻¹)) trivial) term ht

 theorem ParametricSeedTable.ScalarSafe.logarithm {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (cutoff : ℕ) : (table.logarithm cutoff).ScalarSafe := by
  intro term ht
  obtain ⟨count,_,ht⟩ := List.mem_flatMap.mp ht
  exact ((h.power (count+1)).scale (.rational ((-1 : ℚ)^count/(count+1))) trivial) term ht

 theorem ParametricSeedTable.ScalarSafe.finiteCorrection {Scalar Code : Type*} {table : ParametricSeedTable Scalar Code}
    (h : table.ScalarSafe) (cutoff : ℕ) : (table.finiteCorrection cutoff).ScalarSafe := by
  intro term ht
  obtain ⟨count,_,ht⟩ := List.mem_flatMap.mp ht
  exact ((h.power count).scale (.rational ((-1 : ℚ)^count)) trivial) term ht

 theorem ParametricSeedTable.ofOrdered_scalarSafe {Scalar Code : Type*} (table : OrderedSeedTable Code) :
    (ParametricSeedTable.ofOrdered (Scalar:=Scalar) table).ScalarSafe := by
  intro term ht
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp ht
  trivial

 theorem parametricIndependentUpperTable_scalarSafe {Scalar Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape) (cutoff depth : ℕ)
    (table : ParametricSeedTable Scalar Leaf) (hsafe : table.ScalarSafe) :
    (parametricIndependentUpperTable numbering shape cutoff depth table).ScalarSafe := by
  intro term ht
  obtain ⟨old,ho,ht⟩ := List.mem_flatMap.mp ht
  exact ((ParametricSeedTable.ofOrdered_scalarSafe _).scale _ (hsafe old ho)) term ht

 theorem parametricWholeBoundaryTable_scalarSafe {Scalar Leaf : Type*}
    (table : ParametricSeedTable Scalar Leaf) (hsafe : table.ScalarSafe) :
    (parametricWholeBoundaryTable table).ScalarSafe :=
  (hsafe.rename _).append ((hsafe.rename _).scale _ trivial)

 theorem parametricIndependentUpperTable_scalarNodes {Scalar Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape) (cutoff depth : ℕ)
    (table : ParametricSeedTable Scalar Leaf) (nodes : ℕ)
    (h : ∀ term∈table,term.coefficient.nodes≤nodes) :
    ∀ term∈parametricIndependentUpperTable numbering shape cutoff depth table,term.coefficient.nodes≤nodes+2 := by
  intro term ht
  obtain ⟨old,ho,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp ht
  obtain ⟨base,_,rfl⟩ := List.mem_map.mp hr
  change old.coefficient.nodes+1+1≤nodes+2
  have hh := h old ho
  omega

 theorem parametricWholeBoundaryTable_scalarNodes {Scalar Leaf : Type*}
    (table : ParametricSeedTable Scalar Leaf) (nodes : ℕ)
    (h : ∀ term∈table,term.coefficient.nodes≤nodes) :
    ∀ term∈parametricWholeBoundaryTable table,term.coefficient.nodes≤nodes+2 := by
  intro term ht
  rcases List.mem_append.mp ht with ht|ht
  · obtain ⟨old,ho,rfl⟩ := List.mem_map.mp ht
    exact (h old ho).trans (Nat.le_add_right _ _)
  · obtain ⟨renamed,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hr
    change 1+old.coefficient.nodes+1≤nodes+2
    have hh := h old ho
    omega

end AFT.RationalNumerics

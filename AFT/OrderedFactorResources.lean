import AFT.PendingExpansionResources

/-! # Factor counts in the actual ordered reciprocal and U programs -/
namespace AFT.RationalNumerics
open V7Calibration

 theorem OrderedSeedTable.multiply_factor_length {Code : Type*}
    (first second : OrderedSeedTable Code) (left right : ℕ)
    (hf : ∀ term∈first,term.factors.length ≤ left)
    (hs : ∀ term∈second,term.factors.length ≤ right)
    (term : OrderedSeedTerm Code) (ht : term∈first.multiply second) :
    term.factors.length ≤ left+right := by
  obtain ⟨one,ho,htwo⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_map] at htwo
  obtain ⟨two,hm,rfl⟩ := htwo
  simpa only [OrderedSeedTerm.multiply,List.length_append] using Nat.add_le_add (hf one ho) (hs two hm)

 theorem OrderedSeedTable.power_factor_length {Code : Type*}
    (table : OrderedSeedTable Code) (bound : ℕ) (h : ∀ term∈table,term.factors.length ≤ bound)
    (count : ℕ) (term : OrderedSeedTerm Code) (ht : term∈table.power count) :
    term.factors.length ≤ count*bound := by
  induction count generalizing term with
  | zero =>
    simp only [OrderedSeedTable.power,List.mem_cons,List.not_mem_nil,or_false] at ht
    subst term
    simp
  | succ count ih =>
    exact (table.power count).multiply_factor_length table (count*bound) bound ih h term ht |>.trans_eq (by ring)

 theorem OrderedSeedTable.scale_factor_length {Code : Type*}
    (table : OrderedSeedTable Code) (bound : ℕ) (h : ∀ term∈table,term.factors.length ≤ bound)
    (scalar : ℚ) (term : OrderedSeedTerm Code) (ht : term∈table.scale scalar) :
    term.factors.length ≤ bound := by
  change term∈table.map (OrderedSeedTerm.scale scalar) at ht
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
  exact h original ho

 theorem OrderedSeedTable.relabel_factor_length {Code Target : Type*}
    (table : OrderedSeedTable Code) (rename : Code → Target) (bound : ℕ)
    (h : ∀ term∈table,term.factors.length ≤ bound)
    (term : OrderedSeedTerm Target) (ht : term∈table.relabel rename) :
    term.factors.length ≤ bound := by
  change term∈table.map (fun term => ⟨term.coefficient,term.factors.map rename⟩) at ht
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
  simpa only [List.length_map] using h original ho

 theorem OrderedSeedTable.reciprocal_factor_length {Code : Type*}
    (table : OrderedSeedTable Code) (bound : ℕ) (h : ∀ term∈table,term.factors.length ≤ bound)
    (depth : ℕ) (term : OrderedSeedTerm Code) (ht : term∈table.reciprocal depth) :
    term.factors.length ≤ depth*bound := by
  obtain ⟨count,hc,ht⟩ := List.mem_flatMap.mp ht
  have hc : count ≤ depth := by have hh := List.mem_range.mp hc;omega
  exact ((table.power count).scale_factor_length (count*bound) (table.power_factor_length bound h count)
    _ term ht).trans (Nat.mul_le_mul_right bound hc)

 theorem actualPairedReciprocalFactors_factor_length (depth : ℕ)
    (term : OrderedSeedTerm (Finset (Fin 4))) (ht : term∈actualPairedReciprocalFactors depth) :
    term.factors.length ≤ depth := by
  have hh := actualPairedInputFactors.reciprocal_factor_length 1 (fun term ht => by
    obtain ⟨selected,hs,rfl⟩ := List.mem_map.mp ht
    exact le_refl _) depth term ht
  simpa only [Nat.mul_one] using hh

 theorem actualBodyReciprocalFactors_factor_length (depth : ℕ)
    (term : OrderedSeedTerm Unit) (ht : term∈actualBodyReciprocalFactors depth) :
    term.factors.length ≤ depth := by
  obtain ⟨count,hc,rfl⟩ := List.mem_map.mp ht
  simp only [List.length_replicate]
  have hh := List.mem_range.mp hc
  omega

 theorem orderedSeedExpansion_factor_length {State Branch Code : Type*}
    (base : State → Code) (linear : State → State) (choices : State → List Branch) (higher : State → Branch → State)
    (steps : ℕ) (state : State) (term : OrderedSeedTerm Code)
    (ht : term∈orderedSeedExpansion base linear choices higher steps state) :
    term.factors.length=1 := by
  obtain ⟨result,_,rfl,_⟩ := orderedSeedExpansion_member_invariant base linear choices higher
    (fun _ => True) (fun _ => 0) (fun _ _ => ⟨True.intro,by change 0 ≤ 0+1; omega⟩) (fun _ _ _ _ => ⟨True.intro,by change 0 ≤ 0+1; omega⟩)
    steps state True.intro term ht
  rfl

 theorem independentQuotientFactors_factor_length {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (code : PendingKernelCode Leaf) (depth : ℕ)
    (term : OrderedSeedTerm (IndependentQuotientCode Leaf))
    (ht : term∈independentQuotientFactors numbering shape code depth) :
    term.factors.length ≤ 1+depth*((code.shape shape).primary+(code.shape shape).body) := by
  have hnum := (independentNumeratorFactors numbering shape code).relabel_factor_length (Sum.inl : PendingKernelCode Leaf → IndependentQuotientCode Leaf) 1
    (fun term ht => (orderedSeedExpansion_factor_length _ _ _ _ _ _ term ht).le)
  have hp := ((actualPairedReciprocalFactors depth).relabel (fun selected => (Sum.inr (Sum.inl selected) : IndependentQuotientCode Leaf))).power_factor_length
    depth ((actualPairedReciprocalFactors depth).relabel_factor_length _ depth (actualPairedReciprocalFactors_factor_length depth))
    (code.shape shape).primary
  have hb := ((actualBodyReciprocalFactors depth).relabel (fun value => (Sum.inr (Sum.inr value) : IndependentQuotientCode Leaf))).power_factor_length
    depth ((actualBodyReciprocalFactors depth).relabel_factor_length _ depth (actualBodyReciprocalFactors_factor_length depth))
    (code.shape shape).body
  have hh := OrderedSeedTable.multiply_factor_length _ _ (1+(code.shape shape).primary*depth) ((code.shape shape).body*depth)
    (OrderedSeedTable.multiply_factor_length _ _ 1 ((code.shape shape).primary*depth) hnum hp) hb term ht
  exact hh.trans_eq (by ring)

 theorem orderedIndependentColumnFactors_factor_length {Leaf : Type*} {bound : ℕ}
    (numbering : FixedOrderNumberingCode bound) (shape : Leaf → KernelShape)
    (factors : List Leaf) (depth : ℕ)
    (term : OrderedSeedTerm (IndependentQuotientCode (List Leaf)))
    (ht : term∈orderedIndependentColumnFactors numbering shape factors depth) :
    term.factors.length ≤ 1+depth*((orderedJointShape shape factors).primary+(orderedJointShape shape factors).body) := by
  rcases List.mem_append.mp ht with ht|ht
  · exact independentQuotientFactors_factor_length numbering (orderedJointShape shape) (.leaf factors) depth term ht
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    subst term
    simp

end AFT.RationalNumerics

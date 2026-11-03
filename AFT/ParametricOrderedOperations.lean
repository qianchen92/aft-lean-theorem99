import AFT.ParametricOrderedTable

/-! # Exact truncation, substitution, and finite sums of parametric programs -/
namespace AFT.RationalNumerics

def ParametricSeedTable.rename {Scalar Code Target : Type*} (rename : Code → Target)
    (table : ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Target :=
  table.map (fun term => ⟨term.coefficient,term.factors.map rename⟩)

def ParametricSeedTable.sum {Scalar Code Index : Type*} (indices : List Index)
    (tables : Index → ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Code := indices.flatMap tables

def ParametricSeedTable.substitute {Scalar Code Target : Type*} (images : Code → ParametricSeedTable Scalar Target)
    (table : ParametricSeedTable Scalar Code) : ParametricSeedTable Scalar Target :=
  table.flatMap (fun term => ((term.factors.map images).foldl ParametricSeedTable.multiply ParametricSeedTable.one).scale term.coefficient)

open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Scalar Code Seed Target : Type*}
set_option backward.isDefEq.respectTransparency false

theorem ParametricSeedTerm.interpret_monomial (leaf : Scalar → ℝ) (decode : Code → Seed)
    (term : ParametricSeedTerm Scalar Code) :
    term.interpret leaf decode=MvPolynomial.monomial (orderedSeedPowers decode term.factors) (term.coefficient.denote leaf) := by
  rw [ParametricSeedTerm.interpret,←orderedSeedPowers_monomial,MvPolynomial.smul_monomial,smul_eq_mul,mul_one]

private theorem truncate_single (order : Seed → ℕ) (cutoff : ℕ) (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    RepresentedPolynomial.truncate order cutoff (MvPolynomial.monomial powers coefficient)=
      if weightedOrder order powers≤cutoff then MvPolynomial.monomial powers coefficient else 0 := by
  ext other
  by_cases he : powers=other
  · subst other
    simp only [coeff_truncate,MvPolynomial.coeff_monomial,if_true]
    split_ifs <;> simp
  · simp only [coeff_truncate,MvPolynomial.coeff_monomial,if_neg he,ite_self]
    split_ifs <;> simp [MvPolynomial.coeff_monomial,he]

theorem ParametricSeedTable.interpret_truncate (leaf : Scalar → ℝ) (decode : Code → Seed)
    (order : Seed → ℕ) (cutoff : ℕ) (table : ParametricSeedTable Scalar Code) :
    (table.truncate (fun code => order (decode code)) cutoff).interpret leaf decode=
      RepresentedPolynomial.truncate order cutoff (table.interpret leaf decode) := by
  induction table with
  | nil => simp [truncate,RepresentedPolynomial.truncate_zero]
  | cons term rest ih =>
    simp only [truncate] at ih
    simp only [truncate,List.filter_cons,interpret_cons,RepresentedPolynomial.truncate_add]
    split_ifs with ht
    · simp only [decide_eq_true_eq] at ht
      rw [interpret_cons,ih,ParametricSeedTerm.interpret_monomial,truncate_single,
        orderedSeedPowers_order,if_pos ht]
    · simp only [decide_eq_true_eq] at ht
      rw [ih,ParametricSeedTerm.interpret_monomial,truncate_single,
        orderedSeedPowers_order,if_neg ht,zero_add]

theorem ParametricSeedTable.interpret_rename {Other : Type*} (leaf : Scalar → ℝ) (decode : Other → Seed)
    (rename : Code → Other) (table : ParametricSeedTable Scalar Code) :
    (table.rename rename).interpret leaf decode=table.interpret leaf (decode ∘ rename) := by
  unfold ParametricSeedTable.rename ParametricSeedTable.interpret
  simp only [List.map_map,Function.comp_def,ParametricSeedTerm.interpret]
  rfl

theorem ParametricSeedTable.interpret_sum {Index : Type*} (leaf : Scalar → ℝ) (decode : Code → Seed)
    (indices : List Index) (tables : Index → ParametricSeedTable Scalar Code) :
    (ParametricSeedTable.sum indices tables).interpret leaf decode=
      (indices.map (fun index => (tables index).interpret leaf decode)).sum := by
  induction indices with
  | nil => simp [sum]
  | cons index rest ih => simp only [sum,List.flatMap_cons,interpret_append,List.map_cons,List.sum_cons];exact congrArg (fun value => (tables index).interpret leaf decode+value) ih

theorem ParametricSeedTable.interpret_flatten (leaf : Scalar → ℝ) (decode : Code → Seed)
    (tables : List (ParametricSeedTable Scalar Code)) :
    ParametricSeedTable.interpret leaf decode tables.flatten=
      (tables.map (fun table => table.interpret leaf decode)).sum := by
  induction tables with
  | nil => simp
  | cons table rest ih => simp only [List.flatten_cons,interpret_append,List.map_cons,List.sum_cons,ih]

theorem ParametricSeedTable.interpret_sum_range (leaf : Scalar → ℝ) (decode : Code → Seed)
    (count : ℕ) (tables : ℕ → ParametricSeedTable Scalar Code) :
    (ParametricSeedTable.sum (List.range count) tables).interpret leaf decode=
      ∑ index∈Finset.range count,(tables index).interpret leaf decode := by
  rw [interpret_sum]
  induction count with
  | zero => simp
  | succ count ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

theorem ParametricSeedTable.interpret_foldMultiply (leaf : Scalar → ℝ) (decode : Code → Seed)
    (tables : List (ParametricSeedTable Scalar Code)) (initial : ParametricSeedTable Scalar Code) :
    (tables.foldl ParametricSeedTable.multiply initial).interpret leaf decode=
      initial.interpret leaf decode*(tables.map (fun table => table.interpret leaf decode)).prod := by
  induction tables generalizing initial with
  | nil => simp
  | cons table rest ih =>
    simp only [List.foldl_cons,ih,interpret_multiply,List.map_cons,List.prod_cons,mul_assoc]

theorem ParametricSeedTable.interpret_substitute {Other : Type*} (leaf : Scalar → ℝ) (decode : Code → Seed)
    (otherDecode : Other → Target) (images : Code → ParametricSeedTable Scalar Other)
    (hom : Table Seed →ₐ[ℝ] Table Target)
    (himages : ∀ code,(images code).interpret leaf otherDecode=hom (MvPolynomial.X (decode code)))
    (table : ParametricSeedTable Scalar Code) :
    (table.substitute images).interpret leaf otherDecode=hom (table.interpret leaf decode) := by
  induction table with
  | nil => simp [substitute]
  | cons term rest ih =>
    simp only [substitute,List.flatMap_cons,interpret_append,interpret_scale,interpret_foldMultiply,
      interpret_one,one_mul,List.map_map,Function.comp_def,himages,interpret_cons,map_add]
    have hterm : term.coefficient.denote leaf •
        (term.factors.map (fun code => hom (MvPolynomial.X (decode code)))).prod=hom (term.interpret leaf decode) := by
      simp only [ParametricSeedTerm.interpret,map_smul,map_list_prod,List.map_map,Function.comp_def]
    exact congrArg₂ (·+·) hterm ih

end
end AFT.RationalNumerics

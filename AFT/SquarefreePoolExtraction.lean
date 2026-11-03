import AFT.KernelPolynomial
import AFT.PairedTableLinear

/-! # Extracting distinct public placements from a polynomial

Squarefree public-position monomials retain exactly the injective placements.
The two falling-factorial denominators are kept separately, including the
zero-denominator convention when a pool is too small.
-/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
local instance extractionSumDecEq {First Second : Type*} : DecidableEq (First⊕Second) := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {Slot Position Primary Body PP BP : Type*}
  [Fintype Slot] [DecidableEq Slot] [Fintype Position] [DecidableEq Position]
  [Fintype Primary] [DecidableEq Primary] [Fintype Body] [DecidableEq Body]
  [Fintype PP] [DecidableEq PP] [Fintype BP] [DecidableEq BP]

/-- Exponents record how many old coordinates selected each public position. -/
def placementPowers (placement : Slot → Position) : Position →₀ ℕ :=
  ∑ slot,Finsupp.single (placement slot) 1

omit [DecidableEq Slot] [Fintype Position] in
theorem placementPowers_apply (placement : Slot → Position) (position : Position) :
    placementPowers placement position =
      (Finset.univ.filter (fun slot => placement slot=position)).card := by
  simp [placementPowers,Finsupp.single_apply,eq_comm]

omit [DecidableEq Slot] [Fintype Position] in
theorem placementPowers_squarefree (placement : Slot → Position) :
    (∀ position,placementPowers placement position≤1) ↔ Function.Injective placement := by
  simp only [placementPowers_apply,Finset.card_le_one,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h a b he
    exact h (placement b) a he b rfl
  · intro h position a ha b hb
    exact h (ha.trans hb.symm)

omit [Fintype Position] [DecidableEq Position] in
theorem prod_X_placement (placement : Slot → Position) :
    (∏ slot,MvPolynomial.X (placement slot) : Table Position)=
      MvPolynomial.monomial (placementPowers placement) 1 := by
  unfold placementPowers
  have hh (set : Finset Slot) :
      (∏ slot ∈ set,MvPolynomial.X (placement slot) : Table Position)=
        MvPolynomial.monomial (∑ slot ∈ set,Finsupp.single (placement slot) 1) 1 := by
    induction set using Finset.induction_on with
    | empty => simp
    | @insert index set hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,ih]
      rw [MvPolynomial.X, MvPolynomial.monomial_mul]
      simp
  exact hh Finset.univ

def poolCoefficientWeight (powers : (PP⊕BP) →₀ ℕ) : ℝ :=
  if ∀ position,powers position≤1 then
    (((Fintype.card PP).descFactorial (∑ position : PP,powers (.inl position)) : ℝ)*
      ((Fintype.card BP).descFactorial (∑ position : BP,powers (.inr position)) : ℝ))⁻¹
  else 0

/-- The linear coefficient extractor kills collisions and normalizes each
role by its original distinct-placement count. -/
def poolCoefficientExtraction : Table (PP⊕BP) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ poolCoefficientWeight

omit [DecidableEq PP] [DecidableEq BP] in
@[simp] theorem poolCoefficientExtraction_monomial (powers : (PP⊕BP) →₀ ℕ) (scalar : ℝ) :
    poolCoefficientExtraction (MvPolynomial.monomial powers scalar)=
      scalar*poolCoefficientWeight powers := by
  exact Finsupp.linearCombination_single ℝ scalar powers

omit [DecidableEq Primary] [DecidableEq Body] [Fintype BP] [DecidableEq BP] in
theorem placementPowers_primary_degree (primary : Primary → PP) (body : Body → BP) :
    (∑ position : PP,placementPowers (Sum.map primary body) (.inl position))=Fintype.card Primary := by
  simp only [placementPowers,Fintype.sum_sum_type,Sum.map_inl,Sum.map_inr]
  simp [Finsupp.single_apply]
  exact (Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
    (f:=primary) (fun _ _ => Finset.mem_univ _)).symm

omit [DecidableEq Primary] [DecidableEq Body] [Fintype PP] [DecidableEq PP] in
theorem placementPowers_body_degree (primary : Primary → PP) (body : Body → BP) :
    (∑ position : BP,placementPowers (Sum.map primary body) (.inr position))=Fintype.card Body := by
  simp only [placementPowers,Fintype.sum_sum_type,Sum.map_inl,Sum.map_inr]
  simp [Finsupp.single_apply]
  exact (Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=Finset.univ)
    (f:=body) (fun _ _ => Finset.mem_univ _)).symm

omit [Fintype Primary] [DecidableEq Primary] [Fintype Body] [DecidableEq Body]
  [Fintype PP] [DecidableEq PP] [Fintype BP] [DecidableEq BP] in
theorem sum_map_injective_iff (primary : Primary → PP) (body : Body → BP) :
    Function.Injective (Sum.map primary body) ↔ Function.Injective primary ∧ Function.Injective body := by
  constructor
  · intro h
    constructor
    · intro a b he
      exact Sum.inl.inj (h (congrArg Sum.inl he))
    · intro a b he
      exact Sum.inr.inj (h (congrArg Sum.inr he))
  · rintro ⟨hp,hb⟩ (a|a) (b|b) he <;> simp only [Sum.map_inl,Sum.map_inr] at he
    · exact congrArg Sum.inl (hp (Sum.inl.inj he))
    · cases he
    · cases he
    · exact congrArg Sum.inr (hb (Sum.inr.inj he))

omit [DecidableEq Primary] [DecidableEq Body] in
theorem poolCoefficientWeight_placement (primary : Primary → PP) (body : Body → BP) :
    poolCoefficientWeight (placementPowers (Sum.map primary body))=
      if Function.Injective primary ∧ Function.Injective body then
        (((Fintype.card PP).descFactorial (Fintype.card Primary) : ℝ)*
          ((Fintype.card BP).descFactorial (Fintype.card Body) : ℝ))⁻¹ else 0 := by
  simp only [poolCoefficientWeight,placementPowers_squarefree,sum_map_injective_iff,
    placementPowers_primary_degree,placementPowers_body_degree]

omit [DecidableEq PP] [DecidableEq BP] in
/-- The product of the two role-specific linear forms retains every
assignment before the squarefree projection. -/
theorem poolForms_expansion (primary : Primary → PP → ℝ) (body : Body → BP → ℝ) :
    (∏ slot,∑ position,MvPolynomial.C (primary slot position)*MvPolynomial.X (Sum.inl position)) *
      (∏ slot,∑ position,MvPolynomial.C (body slot position)*MvPolynomial.X (Sum.inr position)) =
      ∑ first : Primary → PP,∑ second : Body → BP,
        MvPolynomial.monomial (placementPowers (Sum.map first second))
          ((∏ slot,primary slot (first slot))*(∏ slot,body slot (second slot))) := by
  rw [Fintype.prod_sum,Fintype.prod_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [Finset.prod_mul_distrib,← map_prod MvPolynomial.C]
  have hx := prod_X_placement (Sum.map first second)
  simp only [Fintype.prod_sum_type,Sum.map_inl,Sum.map_inr] at hx
  calc
    _ = MvPolynomial.C ((∏ slot,primary slot (first slot))*(∏ slot,body slot (second slot)))*
        ((∏ slot,MvPolynomial.X (Sum.inl (first slot)))*
          (∏ slot,MvPolynomial.X (Sum.inr (second slot)))) := by rw [map_mul]; ring
    _ = _ := by rw [hx,MvPolynomial.C_mul_monomial,mul_one]

/-- A sum over injective functions is exactly a sum over stored embeddings. -/
theorem sum_injective_functions {Value : Type*} [AddCommMonoid Value] (value : (Slot → Position) → Value) :
    (∑ assignment : Slot → Position,if Function.Injective assignment then value assignment else 0)=
      ∑ assignment : Slot ↪ Position,value assignment := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p:=Function.Injective) (by simp)]
  exact (Equiv.subtypeInjectiveEquivEmbedding Slot Position).sum_comp
    (fun embedding => value embedding)

/-- Extraction of the pool-position polynomial gives exactly the original
average over distinct placements in each pool. -/
theorem poolCoefficientExtraction_forms (primary : Primary → PP → ℝ) (body : Body → BP → ℝ) :
    poolCoefficientExtraction
      ((∏ slot,∑ position,MvPolynomial.C (primary slot position)*MvPolynomial.X (Sum.inl position)) *
        (∏ slot,∑ position,MvPolynomial.C (body slot position)*MvPolynomial.X (Sum.inr position))) =
      (∑ placement : (Primary ↪ PP)×(Body ↪ BP),
        (∏ slot,primary slot (placement.1 slot))*(∏ slot,body slot (placement.2 slot))) /
        (((Fintype.card PP).descFactorial (Fintype.card Primary) : ℝ)*
          ((Fintype.card BP).descFactorial (Fintype.card Body) : ℝ)) := by
  rw [poolForms_expansion]
  simp only [map_sum,poolCoefficientExtraction_monomial,poolCoefficientWeight_placement,
    div_eq_mul_inv,Finset.sum_mul,Fintype.sum_prod_type]
  have he (first : Primary → PP) (second : Body → BP) :
      (∏ slot,primary slot (first slot))*(∏ slot,body slot (second slot))*
        (if Function.Injective first ∧ Function.Injective second then
          (((Fintype.card PP).descFactorial (Fintype.card Primary) : ℝ)*
            ((Fintype.card BP).descFactorial (Fintype.card Body) : ℝ))⁻¹ else 0)=
      if Function.Injective first then
        if Function.Injective second then
          (∏ slot,primary slot (first slot))*(∏ slot,body slot (second slot))*
            (((Fintype.card PP).descFactorial (Fintype.card Primary) : ℝ)*
              ((Fintype.card BP).descFactorial (Fintype.card Body) : ℝ))⁻¹ else 0
      else 0 := by split_ifs <;> simp_all
  simp_rw [he,Finset.sum_ite_irrel,Finset.sum_const_zero,sum_injective_functions]

variable {Color : Type*} [Fintype Color]

/-- Linear forms mark the actual paired public observations by position. -/
def pairedPrimaryForm (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (word : (PP⊕BP) → Color×Color) (color : Color) : Table (PP⊕BP) :=
  ∑ position : PP,MvPolynomial.C (pairedPublicMatrix primary body anchor activation color (word (.inl position)))*
    MvPolynomial.X (.inl position)

def pairedBodyForm (word : (PP⊕BP) → Color×Color) (color : Color) : Table (PP⊕BP) :=
  ∑ position : BP,MvPolynomial.C (bodyPublicMatrix color (word (.inr position)))*
    MvPolynomial.X (.inr position)

/-- An arbitrary joint kernel, without a product or canonical assumption,
is recovered as the full two-pool paired statistic. -/
theorem poolCoefficientExtraction_kernelPolynomial (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ)
    (kernel : (Primary⊕Body → Color) → ℝ) (word : (PP⊕BP) → Color×Color) :
    poolCoefficientExtraction
      (kernelPolynomial
        (Sum.elim (fun _ : Primary => pairedPrimaryForm primary body anchor activation word)
          (fun _ : Body => pairedBodyForm word)) kernel) =
      CanonicalMoments.twoPoolStatistic
        (pairedPublicKernel primary body anchor activation
          (Sum.elim (fun _ : Primary => true) (fun _ : Body => false)) kernel) word := by
  unfold kernelPolynomial
  simp only [map_sum,MvPolynomial.C_mul',map_smul,smul_eq_mul,Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr]
  simp only [pairedPrimaryForm,pairedBodyForm]
  simp_rw [poolCoefficientExtraction_forms,← mul_div_assoc,Finset.mul_sum]
  rw [← Finset.sum_div]
  unfold CanonicalMoments.twoPoolStatistic CanonicalMoments.placedKernel pairedPublicKernel MixedKernel.matrixApply
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro placement _
  apply Finset.sum_congr rfl
  intro colors _
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,publicInputMatrix,
    ite_true,Bool.false_eq_true,ite_false,Function.Embedding.sumMap,
    Function.Embedding.coeFn_mk,Sum.map_inl,Sum.map_inr,Function.comp_apply]

end
end AFT.RepresentedPolynomial

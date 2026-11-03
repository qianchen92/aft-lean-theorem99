import CurrentAFT.GroupedFamilyTensor
import CurrentAFT.GroupedKernelLinear
import CurrentAFT.FamilyEvaluation

/-! # Exact source formula and filtration of joint family tensor synthesis -/
namespace CurrentAFT.GroupedFamilyIdentity
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  GroupedKernelNorm GroupedKernelProduct GroupedFamilyTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input : Group → Type*} [∀ group, Fintype (Input group)]
  (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)

def columnKernel (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group) :
    canonicalKernels primary body (totalPrimary order pattern) (totalBody order pattern) :=
  finiteProduct primary body (fun group => (pattern group).val.1.val) (fun group => (pattern group).val.2.val)
    (fun group => channels group (Pi.single (source group) 1) (pattern group))

theorem kernel_column_formula (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternKernel primary body order channels pattern input =
      ∑ source, input source • columnKernel primary body order channels pattern source := by
  apply Subtype.ext
  change canonicalize _ _ _ _
    (DependentTensorChannel.apply (componentChannel primary body order channels pattern) input) = _
  rw [canonicalize_tensor_formula]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  rw [columnKernel, finiteProduct_val]
  rfl

omit [∀ group, Fintype (Input group)] in
theorem column_retained (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group)
    (hdegree : totalPrimary order pattern + totalBody order pattern ≤ order) :
    (∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
      KernelFamily primary body order)) =
      embed primary body order hdegree (columnKernel primary body order channels pattern source) :=
  finite_product_embed primary body order (fun group => (pattern group).val.1.val)
    (fun group => (pattern group).val.2.val)
    (fun group => channels group (Pi.single (source group) 1) (pattern group)) hdegree
    (fun group => (pattern group).property)

omit [∀ group, Fintype (Input group)] in
theorem column_dropped (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group)
    (hdegree : order < totalPrimary order pattern + totalBody order pattern) :
    (∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
      KernelFamily primary body order)) = 0 := by
  have h := GlobalRaising.vanishesBelow_prod primary body order (Finset.univ : Finset Group)
    (fun group => (pattern group).val.1.val + (pattern group).val.2.val)
    (fun group => Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group))) (by
      intro group _ output hsmall
      dsimp only
      rw [Pi.single_eq_of_ne]
      intro hequal
      subst output
      dsimp only at hsmall
      omega)
  rw [Finset.sum_add_distrib] at h
  funext output
  exact h output (by have := output.property; unfold totalPrimary totalBody at hdegree; omega)

theorem family_column_formula (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternFamily primary body order channels pattern input =
      ∑ source, input source •
        ∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
          KernelFamily primary body order) := by
  unfold patternFamily
  split_ifs with hdegree
  · simp_rw [column_retained primary body order channels pattern _ hdegree]
    rw [kernel_column_formula]
    unfold embed
    funext output
    by_cases hequal : output = embedArity order (totalPrimary order pattern) (totalBody order pattern) hdegree
    · subst output; simp
    · simp [Pi.single_eq_of_ne hequal]
  · simp_rw [column_dropped primary body order channels pattern _ (Nat.lt_of_not_ge hdegree),
      smul_zero, Finset.sum_const_zero]

/-- The norm-controlled assembly is the original finite joint source sum
of local response products, as an equality of canonical coefficient data. -/
theorem response_eq (input : ((group : Group) → Input group) → ℝ) :
    response primary body order channels input =
      ∑ source, input source • ∏ group, channels group (Pi.single (source group) 1) := by
  unfold response
  simp_rw [family_column_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.smul_sum, ← product_family_arity_expansion]

theorem response_vanishes (degree : Group → ℕ)
    (hchannel : ∀ group score, VanishesBelow primary body order (degree group) (channels group score))
    (input : ((group : Group) → Input group) → ℝ) :
    VanishesBelow primary body order (∑ group, degree group) (response primary body order channels input) := by
  rw [response_eq]
  apply LocalRaisingFirst.vanishesBelow_sum
  intro source _
  apply GlobalRaising.vanishesBelow_smul
  exact GlobalRaising.vanishesBelow_prod primary body order Finset.univ degree
    (fun group => channels group (Pi.single (source group) 1)) (fun group _ => hchannel group _)

theorem response_image {Variable : Type*}
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    (hp : ∀ color, (primaryForm color).IsHomogeneous 1) (hb : ∀ color, (bodyForm color).IsHomogeneous 1)
    (input : ((group : Group) → Input group) → ℝ) :
    LeadingEvaluation.familyHom primary body primaryForm bodyForm hp hb order
      (response primary body order channels input) =
      ∑ source, input source • ∏ group,
        LeadingEvaluation.familyHom primary body primaryForm bodyForm hp hb order
          (channels group (Pi.single (source group) 1)) := by
  rw [response_eq]
  simp only [map_sum, map_smul, map_prod]

end
end CurrentAFT.GroupedFamilyIdentity

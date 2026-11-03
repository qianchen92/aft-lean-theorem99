import AFT.FiniteJointExpectation

/-! # The genuine joint primary/compensator pool law -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot First Second FullBody : Type*}
  [Fintype Slot] [Fintype First] [Fintype Second] [Fintype FullBody]

omit [Fintype FullBody] in
/-- Pairing independent coordinates is exactly the product of the paired
laws, for every finite test function including powers of a joint score. -/
theorem independent_prod_expectation (first : Slot → FiniteDist First)
    (second : Slot → FiniteDist Second) (value : (Slot → First × Second) → ℝ) :
    (independent (fun slot => (first slot).prod (second slot))).expectation value =
      (independent first).expectation (fun left => (independent second).expectation
        (fun right => value (fun slot => (left slot, right slot)))) := by
  unfold expectation independent
  rw [← (Equiv.arrowProdEquivProdArrow Slot (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, prod_weight,
    Finset.prod_mul_distrib, mul_assoc]

/-- A single injection of both the compensator and ordinary-body pools
into the full body word gives the actual paired reference law. -/
theorem joint_paired_embedding_expectation (primary : Slot → FiniteDist First)
    (body : FiniteDist Second) (embedding : Slot ↪ FullBody)
    (value : (Slot → First × Second) → ℝ) :
    (joint (independent primary) (fun _ => independent (fun _ : FullBody => body))).expectation
      (fun pair => value (fun slot => (pair.1 slot, pair.2 (embedding slot)))) =
      (independent (fun slot => (primary slot).prod body)).expectation value := by
  rw [expectation_joint, independent_prod_expectation]
  apply Finset.sum_congr rfl
  intro marks _
  congr 1
  exact CanonicalMoments.independent_embedding_expectation_general (fun _ : FullBody => body) embedding
    (fun centers => value (fun slot => (marks slot, centers slot)))
end
end AFT.FiniteDist

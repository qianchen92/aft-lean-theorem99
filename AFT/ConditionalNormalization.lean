import AFT.ChargeRepair

/-! # The conditional signed normalization costs only the actual mean error -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Skeleton State Output : Type*} [Fintype Skeleton] [Fintype State] [Fintype Output]

def conditionalRawMass (skeleton : FiniteDist Skeleton) (proposal : Skeleton → FiniteDist State)
    (weight : Skeleton → State → ℝ) : Skeleton × State → ℝ :=
  fun pair => skeleton.weight pair.1 * weightedMass (proposal pair.1) (weight pair.1) pair.2

omit [Fintype Output] in
/-- Normalization is controlled uniformly in the public cell, without
paying the reciprocal of that cell's probability. -/
theorem conditional_signed_normalization_l1 (skeleton : FiniteDist Skeleton)
    (proposal : Skeleton → FiniteDist State) (weight : Skeleton → State → ℝ)
    (meanError envelope : ℝ)
    (hmean : ∀ cell, |(proposal cell).expectation (weight cell)-1| ≤ meanError)
    (hsmall : meanError ≤ 1/2)
    (henvelope : ∀ cell point, |weight cell point| ≤ envelope) :
    (∑ pair, |conditionalSignedMass skeleton proposal weight pair - conditionalRawMass skeleton proposal weight pair|) ≤
      2*meanError*envelope := by
  have hm0 : 0 ≤ meanError := by
    have hs : Nonempty Skeleton := by
      by_contra hh
      haveI : IsEmpty Skeleton := not_nonempty_iff.mp hh
      have hz := skeleton.sum_one
      simp at hz
    exact hs.elim fun cell => (abs_nonneg _).trans (hmean cell)
  have hfloor (cell) : (1/2 : ℝ) ≤ (proposal cell).expectation (weight cell) := by
    have hh := (abs_le.mp (hmean cell)).1
    linarith
  have hfactor (cell) : |1/(proposal cell).expectation (weight cell)-1| ≤ 2*meanError := by
    have hp : 0 < (proposal cell).expectation (weight cell) := lt_of_lt_of_le (by norm_num) (hfloor cell)
    rw [div_sub_one hp.ne', abs_div, abs_of_pos hp, abs_sub_comm]
    apply (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0:ℝ)<1/2) (hfloor cell)).trans
    have hh := div_le_div_of_nonneg_right (hmean cell) (by norm_num : (0:ℝ)≤1/2)
    exact hh.trans_eq (by ring)
  have hpoint (pair : Skeleton × State) :
      |conditionalSignedMass skeleton proposal weight pair - conditionalRawMass skeleton proposal weight pair| ≤
        skeleton.weight pair.1 * (proposal pair.1).weight pair.2 * (2*meanError*envelope) := by
    have he : conditionalSignedMass skeleton proposal weight pair - conditionalRawMass skeleton proposal weight pair =
        skeleton.weight pair.1 * (proposal pair.1).weight pair.2 * weight pair.1 pair.2 *
          (1/(proposal pair.1).expectation (weight pair.1)-1) := by
      unfold conditionalSignedMass conditionalRawMass weightedMass signedMass expectation
      ring
    rw [he, abs_mul, abs_mul, abs_mul, abs_of_nonneg (skeleton.nonneg _), abs_of_nonneg ((proposal _).nonneg _)]
    have hh := mul_le_mul (henvelope pair.1 pair.2) (hfactor pair.1) (abs_nonneg _) (by
      exact (abs_nonneg _).trans (henvelope pair.1 pair.2))
    simpa only [mul_assoc, mul_comm envelope (2*meanError)] using
      mul_le_mul_of_nonneg_left hh (mul_nonneg (skeleton.nonneg _) ((proposal _).nonneg _))
  apply (Finset.sum_le_sum (fun pair _ => hpoint pair)).trans_eq
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_one, one_mul, ← Finset.sum_mul, sum_one]
  ring

/-- The same normalization estimate passes through the full physical
output channel, including all remaining correlated randomness. -/
theorem conditional_signed_normalization_kernel_l1 (skeleton : FiniteDist Skeleton)
    (proposal : Skeleton → FiniteDist State) (weight : Skeleton → State → ℝ)
    (meanError envelope : ℝ)
    (hmean : ∀ cell, |(proposal cell).expectation (weight cell)-1| ≤ meanError)
    (hsmall : meanError ≤ 1/2)
    (henvelope : ∀ cell point, |weight cell point| ≤ envelope)
    (channel : Skeleton × State → FiniteDist Output) :
    (∑ output, |(∑ pair, conditionalSignedMass skeleton proposal weight pair * (channel pair).weight output) -
      ∑ pair, conditionalRawMass skeleton proposal weight pair * (channel pair).weight output|) ≤
        2*meanError*envelope := by
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  exact (signed_kernel_l1_contraction _ channel).trans
    (conditional_signed_normalization_l1 skeleton proposal weight meanError envelope hmean hsmall henvelope)
/-- The actual positive conditional law is close to the unnormalized
signed physical input, paying both clipping and conditional normalization. -/
theorem conditionalRepair_raw_kernel_bound (skeleton : FiniteDist Skeleton)
    (proposal : Skeleton → FiniteDist State) (weight : Skeleton → State → ℝ)
    (meanError envelope : ℝ)
    (hmean : ∀ cell, |(proposal cell).expectation (weight cell)-1| ≤ meanError)
    (hsmall : meanError ≤ 1/2) (henvelope : ∀ cell point, |weight cell point| ≤ envelope)
    (moment : ℕ) (hmoment : 0 < moment) (channel : Skeleton × State → FiniteDist Output) :
    ∃ hpositive : ∀ cell, 0 < signedMass (weightedMass (proposal cell) (weight cell)),
      (conditionalRepair skeleton proposal weight hpositive).map Prod.fst=skeleton ∧
      (∑ output, |((conditionalRepair skeleton proposal weight hpositive).mix channel).weight output-
        ∑ pair,conditionalRawMass skeleton proposal weight pair*(channel pair).weight output|)≤
        4*skeleton.expectation (fun cell => (proposal cell).expectation
          (fun point => |weight cell point-1|^(2*moment)))+2*meanError*envelope := by
  have hfloor (cell) : (1/2 : ℝ)≤signedMass (weightedMass (proposal cell) (weight cell)) := by
    change (1/2 : ℝ)≤(proposal cell).expectation (weight cell)
    have hh := (abs_le.mp (hmean cell)).1
    linarith
  let hpositive := fun cell => lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) (hfloor cell)
  refine ⟨hpositive,conditionalRepair_skeleton _ _ _ _,?_⟩
  have hrepair := conditionalRepair_kernel_bound skeleton proposal weight (1/2) (by norm_num)
    hfloor moment hmoment channel
  norm_num only [div_div,div_one,one_mul] at hrepair
  have hnormal := conditional_signed_normalization_kernel_l1 skeleton proposal weight
    meanError envelope hmean hsmall henvelope channel
  have htriangle := Finset.sum_le_sum (fun output (_ : output∈(Finset.univ : Finset Output)) =>
    abs_sub_le (((conditionalRepair skeleton proposal weight hpositive).mix channel).weight output)
      (∑ pair,conditionalSignedMass skeleton proposal weight pair*(channel pair).weight output)
      (∑ pair,conditionalRawMass skeleton proposal weight pair*(channel pair).weight output))
  rw [Finset.sum_add_distrib] at htriangle
  exact htriangle.trans (add_le_add hrepair hnormal)

end
end AFT.FiniteDist

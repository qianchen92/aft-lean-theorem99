import AFT.TotalVariation

/-!
# Conditional positive repair as an actual finite probability law

Repair is performed separately within each retained public skeleton.  The
skeleton's entire marginal law is therefore preserved, including rare events.
The error bound averages the centered moment before applying any physical
output channel and has no extra charge-conditioning factor.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

def joint (skeleton : FiniteDist S) (proposal : S → FiniteDist A) : FiniteDist (S × A) where
  weight pair := skeleton.weight pair.1 * (proposal pair.1).weight pair.2
  nonneg pair := mul_nonneg (skeleton.nonneg _) ((proposal _).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_one, mul_one]
    exact skeleton.sum_one

@[simp] theorem joint_weight (skeleton : FiniteDist S) (proposal : S → FiniteDist A) (s : S) (a : A) :
    (joint skeleton proposal).weight (s, a) = skeleton.weight s * (proposal s).weight a := rfl

@[simp] theorem joint_skeleton (skeleton : FiniteDist S) (proposal : S → FiniteDist A) :
    (joint skeleton proposal).map Prod.fst = skeleton := by
  ext s
  simp only [map_weight, Fintype.sum_prod_type, joint_weight]
  trans ∑ x, if x = s then skeleton.weight x else 0
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = s
    · simp only [if_pos hx, ← Finset.mul_sum, sum_one, mul_one]
    · simp only [if_neg hx, Finset.sum_const_zero]
  · simp

def weightedMass (proposal : FiniteDist A) (weight : A → ℝ) : A → ℝ :=
  fun a => proposal.weight a * weight a

def positiveRepairLaw (proposal : FiniteDist A) (weight : A → ℝ)
    (hmean : 0 < signedMass (weightedMass proposal weight)) : FiniteDist A where
  weight a := max (weightedMass proposal weight a) 0 / positiveMass (weightedMass proposal weight)
  nonneg := (positive_repair_normalized _ hmean).1
  sum_one := (positive_repair_normalized _ hmean).2

@[simp] theorem positiveRepairLaw_weight (proposal : FiniteDist A) (weight : A → ℝ)
    (hmean : 0 < signedMass (weightedMass proposal weight)) (a : A) :
    (positiveRepairLaw proposal weight hmean).weight a =
      proposal.weight a * max (weight a) 0 / positiveMass (weightedMass proposal weight) := by
  change max (proposal.weight a * weight a) 0 / _ = _
  rw [mul_max_of_nonneg _ _ (proposal.nonneg a), mul_zero]

theorem positiveRepairLaw_support (proposal : FiniteDist A) (weight : A → ℝ)
    (hmean : 0 < signedMass (weightedMass proposal weight)) (a : A)
    (ha : proposal.weight a = 0) : (positiveRepairLaw proposal weight hmean).weight a = 0 := by
  simp only [positiveRepairLaw_weight, ha, zero_mul, zero_div]

def conditionalRepair (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) (hmean : ∀ s, 0 < signedMass (weightedMass (proposal s) (weight s))) :
    FiniteDist (S × A) := joint skeleton fun s => positiveRepairLaw (proposal s) (weight s) (hmean s)

/-- Preservation holds for the complete skeleton law, with no lower bound
on a skeleton's own probability. -/
theorem conditionalRepair_skeleton (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) (hmean : ∀ s, 0 < signedMass (weightedMass (proposal s) (weight s))) :
    (conditionalRepair skeleton proposal weight hmean).map Prod.fst = skeleton := joint_skeleton _ _

def conditionalSignedMass (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) : S × A → ℝ :=
  fun pair => skeleton.weight pair.1 * weightedMass (proposal pair.1) (weight pair.1) pair.2 /
    signedMass (weightedMass (proposal pair.1) (weight pair.1))

/-- Exact global L1 cost, averaged over the unchanged public skeleton. -/
theorem conditionalRepair_l1 (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) (hmean : ∀ s, 0 < signedMass (weightedMass (proposal s) (weight s))) :
    (∑ pair, |(conditionalRepair skeleton proposal weight hmean).weight pair -
      conditionalSignedMass skeleton proposal weight pair|) =
      ∑ s, skeleton.weight s * (2 * negativeMass (weightedMass (proposal s) (weight s)) /
        signedMass (weightedMass (proposal s) (weight s))) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  have hfactor (a : A) :
      (conditionalRepair skeleton proposal weight hmean).weight (s, a) -
        conditionalSignedMass skeleton proposal weight (s, a) = skeleton.weight s *
          (max (weightedMass (proposal s) (weight s) a) 0 /
            positiveMass (weightedMass (proposal s) (weight s)) -
            weightedMass (proposal s) (weight s) a / signedMass (weightedMass (proposal s) (weight s))) := by
    dsimp [conditionalRepair, joint, positiveRepairLaw, conditionalSignedMass]
    ring
  simp_rw [hfactor, abs_mul, abs_of_nonneg (skeleton.nonneg s), ← Finset.mul_sum]
  rw [positive_repair_l1 _ (hmean s)]

theorem weightedMass_negativeMoment (proposal : FiniteDist A) (weight : A → ℝ)
    (moment : ℕ) (hmoment : 0 < moment) :
    negativeMass (weightedMass proposal weight) ≤
      ∑ a, proposal.weight a * |weight a - 1| ^ (2 * moment) := by
  unfold negativeMass weightedMass
  have hpoint (a : A) : max (-(proposal.weight a * weight a)) 0 =
      proposal.weight a * max (-weight a) 0 := by
    rw [mul_max_of_nonneg _ _ (proposal.nonneg a), mul_zero, mul_neg]
  simp_rw [hpoint]
  exact weighted_negative_part_le_even_moment proposal.weight weight proposal.nonneg moment hmoment

/-- The repaired joint distribution has L1 error at most the averaged even
moment divided by the uniform conditional mean floor. -/
theorem conditionalRepair_moment_bound (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) (meanFloor : ℝ) (hfloor : 0 < meanFloor)
    (hmean : ∀ s, meanFloor ≤ signedMass (weightedMass (proposal s) (weight s)))
    (moment : ℕ) (hmoment : 0 < moment) :
    (∑ pair, |(conditionalRepair skeleton proposal weight
      (fun s => lt_of_lt_of_le hfloor (hmean s))).weight pair -
      conditionalSignedMass skeleton proposal weight pair|) ≤
      (2 / meanFloor) * ∑ s, skeleton.weight s *
        ∑ a, (proposal s).weight a * |weight s a - 1| ^ (2 * moment) := by
  rw [conditionalRepair_l1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hn := negativeMass_nonneg (weightedMass (proposal s) (weight s))
  have hh := (div_le_div_of_nonneg_left (by positivity :
      0 ≤ 2 * negativeMass (weightedMass (proposal s) (weight s))) hfloor (hmean s)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (weightedMass_negativeMoment (proposal s) (weight s) moment hmoment)
        (by norm_num)) hfloor.le)
  have h := mul_le_mul_of_nonneg_left hh (skeleton.nonneg s)
  convert h using 1
  ring

/-- The complete physical channel, including shared hidden randomness,
contracts the same pre-channel repair estimate. -/
theorem conditionalRepair_kernel_bound (skeleton : FiniteDist S) (proposal : S → FiniteDist A)
    (weight : S → A → ℝ) (meanFloor : ℝ) (hfloor : 0 < meanFloor)
    (hmean : ∀ s, meanFloor ≤ signedMass (weightedMass (proposal s) (weight s)))
    (moment : ℕ) (hmoment : 0 < moment) (kernel : S × A → FiniteDist B) :
    (∑ output, |((conditionalRepair skeleton proposal weight
      (fun s => lt_of_lt_of_le hfloor (hmean s))).mix kernel).weight output -
        ∑ pair, conditionalSignedMass skeleton proposal weight pair * (kernel pair).weight output|) ≤
      (2 / meanFloor) * ∑ s, skeleton.weight s *
        ∑ a, (proposal s).weight a * |weight s a - 1| ^ (2 * moment) := by
  simp only [mix_weight, ← Finset.sum_sub_distrib, ← sub_mul]
  exact (signed_kernel_l1_contraction _ kernel).trans
    (conditionalRepair_moment_bound skeleton proposal weight meanFloor hfloor hmean moment hmoment)

end

end AFT.FiniteDist

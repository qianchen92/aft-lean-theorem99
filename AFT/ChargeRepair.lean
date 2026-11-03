import AFT.FiniteJointExpectation
import AFT.ActualTableChargeMean
import AFT.ActualTableChargeMoment

/-! # Conditional positive repair with the charge error paid before the channel -/

namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Skeleton State Output : Type*} [Fintype Skeleton] [Fintype State] [Fintype Output]

omit [Fintype Skeleton] in
/-- The signed conditional mean is protected by the exact pre-charge
skeleton identity and the local first-moment transfer. -/
theorem charge_mean_floor (productProposal chargedProposal : Skeleton → FiniteDist State)
    (weight : Skeleton → State → ℝ) (error : ℝ)
    (hproduct : ∀ cell, (productProposal cell).expectation (weight cell) = 1)
    (htransfer : ∀ cell, |(chargedProposal cell).expectation (weight cell) -
      (productProposal cell).expectation (weight cell)| ≤ error)
    (hsmall : error ≤ 1 / 2) :
    ∀ cell, 1 / 2 ≤ signedMass (weightedMass (chargedProposal cell) (weight cell)) := by
  intro cell
  have hh := htransfer cell
  rw [hproduct cell] at hh
  change 1 / 2 ≤ (chargedProposal cell).expectation (weight cell)
  linarith [(abs_le.mp hh).1]

/-- Only the moment averaged over the unchanged skeleton is needed. There
is no uniform moment hypothesis on a rare individual skeleton cell. -/
theorem conditionalRepair_after_charge (skeleton : FiniteDist Skeleton)
    (productProposal chargedProposal : Skeleton → FiniteDist State)
    (weight : Skeleton → State → ℝ) (meanError productMoment chargeMomentError : ℝ)
    (hproduct : ∀ cell, (productProposal cell).expectation (weight cell) = 1)
    (hmeanTransfer : ∀ cell, |(chargedProposal cell).expectation (weight cell) -
      (productProposal cell).expectation (weight cell)| ≤ meanError)
    (hsmall : meanError ≤ 1 / 2) (moment : ℕ) (hmoment : 0 < moment)
    (hproductMoment : skeleton.expectation (fun cell => (productProposal cell).expectation
      (fun point => |weight cell point - 1| ^ (2 * moment))) ≤ productMoment)
    (hchargeTransfer : skeleton.expectation (fun cell => (chargedProposal cell).expectation
        (fun point => |weight cell point - 1| ^ (2 * moment))) ≤
      skeleton.expectation (fun cell => (productProposal cell).expectation
        (fun point => |weight cell point - 1| ^ (2 * moment))) + chargeMomentError)
    (channel : Skeleton × State → FiniteDist Output) :
    let hmean := fun cell => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (charge_mean_floor productProposal chargedProposal weight meanError hproduct hmeanTransfer hsmall cell)
    (conditionalRepair skeleton chargedProposal weight hmean).map Prod.fst = skeleton ∧
    (∑ output, |((conditionalRepair skeleton chargedProposal weight hmean).mix channel).weight output -
      ∑ pair, conditionalSignedMass skeleton chargedProposal weight pair * (channel pair).weight output|) ≤
        4 * (productMoment + chargeMomentError) := by
  dsimp only
  refine ⟨conditionalRepair_skeleton .., ?_⟩
  have hh := conditionalRepair_kernel_bound skeleton chargedProposal weight (1 / 2) (by norm_num)
    (charge_mean_floor productProposal chargedProposal weight meanError hproduct hmeanTransfer hsmall)
    moment hmoment channel
  norm_num only [div_div, div_one, one_mul] at hh
  apply hh.trans
  change 4 * skeleton.expectation (fun cell => (chargedProposal cell).expectation
      (fun point => |weight cell point - 1| ^ (2 * moment))) ≤ _
  exact mul_le_mul_of_nonneg_left (hchargeTransfer.trans (add_le_add hproductMoment le_rfl)) (by norm_num)

end
end AFT.FiniteDist

import CurrentAFT.RootTaggedLegFirst
import CurrentAFT.LocalCoefficientNorm

/-! Actual root-tagged full same-scalar unselected leg mass and higher channels. -/

namespace CurrentAFT.RootTaggedLegHigher

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock PositiveFirstCoefficient CycleRootExpansion RootTaggedLocal
  PrimaryTensorInverse PhysicalBlockTensors BlockFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _

def rawMassLinear (security : ℕ) :
    (Root security → ℝ) →ₗ[ℝ] ((Fin 3 → ActualControls.Palette security) → ℝ) where
  toFun input := fun word => ∑ root, (rootReference security).weight root * input root *
    (primaryLawAt security root.val).weight word
  map_add' first second := by
    funext word
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext word
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

def massLinear (security : ℕ) :
    (Root security → ℝ) →ₗ[ℝ] ((Fin 3 → ActualControls.Palette security) → ℝ) :=
  (rawMassLinear security).comp (TensorChannel.center (rootReference security))

def sourceLaw (security : ℕ) := (rootReference security).prod (scalarLaw security)

theorem tripleMassAt_const_score (security : ℕ) (root : ℤ) (scalar : LocalReferenceEnergy.Scalar security) (score : ℝ)
    (first second third : ActualControls.Palette security) :
    tripleMassAt security root scalar (fun _ => score) first second third =
      score * tripleMassAt security root scalar (fun _ => 1) first second third := by
  unfold tripleMassAt signedPairAt
  simp only [mul_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem rawMass_joint_source (security : ℕ) (input : Root security → ℝ) :
    rawMassLinear security input = tripleMass (jointTripleMass security (sourceLaw security)
      (fun source => (source.1.val : ℤ)) Prod.snd (fun source _ => input source.1)) := by
  funext word
  simp only [rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk, primaryLawAt, FiniteDist.mix_weight,
    tripleMass, jointTripleMass, sourceLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
  simp_rw [positiveTriple_weight, tripleMass]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro scalar _
  rw [tripleMassAt_const_score security root.val scalar (input root)]
  ring

theorem rawMass_mass (security : ℕ) (input : Root security → ℝ) :
    (∑ word, rawMassLinear security input word) = (rootReference security).expectation input := by
  unfold rawMassLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one]
  rfl

theorem massLinear_mass (security : ℕ) (input : Root security → ℝ) :
    (∑ word, massLinear security input word) = 0 := by
  rw [massLinear, LinearMap.comp_apply, rawMass_mass, TensorChannel.center_mean]

theorem massLinear_constant (security : ℕ) : massLinear security (fun _ => 1) = 0 := by
  have hcenter : TensorChannel.center (rootReference security) (fun _ => 1) = 0 := by
    funext root
    simp only [TensorChannel.center_apply, FiniteDist.expectation_const, sub_self, Pi.zero_apply]
  rw [massLinear, LinearMap.comp_apply, hcenter, map_zero]

def degreeLinear (security degree : ℕ) :
    (Root security → ℝ) →ₗ[ℝ] ((Fin degree → ActualControls.Palette security) → ℝ) :=
  (LocalTensors.degreeTensorLinear (fun _ : Fin 3 => uniformReference security) degree).comp (massLinear security)

theorem rawMass_degree_energy (security degree : ℕ) (input : Root security → ℝ) :
    tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (rawMassLinear security input) degree) ≤
        (32 * pairBudget security) * (rootReference security).l2Sq input := by
  rw [rawMass_joint_source]
  have h := jointTriple_degree_energy security (sourceLaw security)
    (fun source => (source.1.val : ℤ)) Prod.snd (fun source _ => input source.1) degree
  simpa only [sourceLaw, FiniteDist.expectation_prod, FiniteDist.expectation_const, FiniteDist.l2Sq] using h

theorem degreeLinear_energy (security degree : ℕ) (input : Root security → ℝ) :
    tensorEnergy (degreeLinear security degree input) ≤
      (32 * pairBudget security) * (rootReference security).l2Sq input := by
  change tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
    (rawMassLinear security (TensorChannel.center (rootReference security) input)) degree) ≤ _
  apply (rawMass_degree_energy security degree _).trans
  apply mul_le_mul_of_nonneg_left (TensorChannel.center_energy_le _ _)
  have hmark := markMass_pos security
  unfold pairBudget primaryMaximum
  positivity

theorem rawMass_uniform_energy (security : ℕ) (input : Root security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => uniformReference security)).weight
      (rawMassLinear security input) ≤ (4 * pairBudget security) * (rootReference security).l2Sq input := by
  rw [rawMass_joint_source]
  have hidentity := triple_density_energy (uniformReference security)
    (jointTripleMass security (sourceLaw security) (fun source => (source.1.val : ℤ)) Prod.snd (fun source _ => input source.1))
  change densitySquareNorm _ _ = _ at hidentity
  rw [densityScore_square] at hidentity
  rw [hidentity]
  have havg := tripleEnergy_average_le (sourceLaw security) (uniformReference security).weight
    (uniformReference security).nonneg (fun source => tripleMassAt security source.1.val source.2 (fun _ => input source.1))
  apply havg.trans
  calc
    _ ≤ ∑ source, (sourceLaw security).weight source *
        ((4 * pairBudget security) * (primaryLaw security).expectation (fun _ => input source.1 ^ 2)) :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
        (tripleMassAt_energy security source.1.val source.2 (fun _ => input source.1)) ((sourceLaw security).nonneg source)
    _ = _ := by
      simp only [FiniteDist.expectation_const, sourceLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
      unfold FiniteDist.l2Sq FiniteDist.expectation
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro root _
      ring

theorem massLinear_uniform_energy (security : ℕ) (input : Root security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => uniformReference security)).weight
      (massLinear security input) ≤ (4 * pairBudget security) * (rootReference security).l2Sq input := by
  change profileSquareNorm _ (rawMassLinear security (TensorChannel.center (rootReference security) input)) ≤ _
  apply (rawMass_uniform_energy security _).trans
  apply mul_le_mul_of_nonneg_left (TensorChannel.center_energy_le _ _)
  have hmark := markMass_pos security
  unfold pairBudget primaryMaximum
  positivity

end

end CurrentAFT.RootTaggedLegHigher

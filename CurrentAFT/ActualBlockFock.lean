import CurrentAFT.PositiveFirstCoefficient
import CurrentAFT.ActualCycleMeanMGF
import AFT.BlockProducts
import AFT.LocalCoefficientLinear
import AFT.BlockCoefficientNorms

/-!
# The actual current conditional independent physical block law

Each leg is a genuine three-output law with its shared protected scalar
averaged inside that block. Every remaining body position is a one-output
center or queue law. The full finite product includes all output positions.
-/

namespace CurrentAFT.ActualBlockFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PositiveFirstCoefficient
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  DiffuseProfiles.scalarLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security

/-- Probability mixtures contract the actual full homogeneous coefficient
energy, before any bound on individual frequency coordinates. -/
theorem degreeTensor_mix_energy {Choice Slot Color : Type*} [Fintype Choice]
    [Fintype Slot] [Fintype Color] (reference : Slot → FiniteDist Color)
    (source : FiniteDist Choice) (channel : Choice → FiniteDist (Slot → Color)) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor reference (source.mix channel).weight degree) ≤
      source.expectation (fun choice => BlockFock.tensorEnergy
        (LocalTensors.degreeTensor reference (channel choice).weight degree)) := by
  have hmass : (source.mix channel).weight = ∑ choice, source.weight choice • (channel choice).weight := by
    funext word
    simp only [FiniteDist.mix_weight, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have htensor : LocalTensors.degreeTensor reference (source.mix channel).weight degree =
      ∑ choice, source.weight choice • LocalTensors.degreeTensor reference (channel choice).weight degree := by
    rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
    simp only [map_smul, LocalTensors.degreeTensorLinear_apply]
  rw [htensor]
  unfold BlockFock.tensorEnergy FiniteDist.expectation
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ word, ∑ choice, source.weight choice *
        LocalTensors.degreeTensor reference (channel choice).weight degree word ^ 2 :=
      Finset.sum_le_sum (fun word _ => BlockFock.mean_square_le source _)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

def centerCount (security : ℕ) : ℕ :=
  Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

abbrev BlockIndex (security : ℕ) :=
  Fin (Parameters.legCount security) ⊕ (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))

def Slots (security : ℕ) : BlockIndex security → Type
  | .inl _ => Fin 3
  | .inr _ => Fin 1

instance slotsFintype (security : ℕ) (index : BlockIndex security) : Fintype (Slots security index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 3))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def singletonLaw {Color : Type*} [Fintype Color] (law : FiniteDist Color) : FiniteDist (Fin 1 → Color) :=
  law.map (fun color _ => color)

def primaryLawAt (security : ℕ) (root : ℤ) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (positiveTripleLaw security root)

def blockLawAt (security : ℕ)
    (attachmentRoot : Fin (Parameters.legCount security) → ℤ)
    (centerRoot : Fin (centerCount security) → ℤ)
    (queueRoot : Fin (Parameters.modulus security) → ℤ) (queue : ℤ) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security)
  | .inl leg => primaryLawAt security (attachmentRoot leg)
  | .inr (.inl center) => singletonLaw ((centerLaw security).map (shiftEquiv security (centerRoot center)))
  | .inr (.inr point) => singletonLaw ((safeLaw security).map (shiftEquiv security (queueRoot point + queue)))

theorem slots_card_le_three (security : ℕ) (index : BlockIndex security) :
    Fintype.card (Slots security index) ≤ 3 := by
  cases index with
  | inl _ => change Fintype.card (Fin 3) ≤ 3; norm_num
  | inr _ => change Fintype.card (Fin 1) ≤ 3; norm_num

theorem physical_card (security : ℕ) :
    Fintype.card (Sigma (Slots security)) = Parameters.dimension security := by
  have hroom := population_room security
  simp only [Fintype.card_sigma, Fintype.sum_sum_type]
  have hprimary : (∑ index : Fin (Parameters.legCount security),
      Fintype.card (Slots security (.inl index))) = 3 * Parameters.legCount security := by
    simp [Slots, mul_comm]
  have hcenter : (∑ index : Fin (centerCount security),
      Fintype.card (Slots security (.inr (.inl index)))) = centerCount security := by
    simp [Slots]
  have hqueue : (∑ index : Fin (Parameters.modulus security),
      Fintype.card (Slots security (.inr (.inr index)))) = Parameters.modulus security := by
    simp [Slots]
  rw [hprimary, hcenter, hqueue, Parameters.dimension]
  unfold centerCount
  omega

theorem primary_first_energy (security : ℕ) (root : ℤ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (primaryLawAt security root).weight 1) ≤
      (240 + 6291552 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by
  apply (degreeTensor_mix_energy _ (scalarLaw security) (positiveTripleLaw security root) 1).trans
  calc
    _ ≤ (scalarLaw security).expectation (fun _ =>
        (240 + 6291552 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) :=
      Finset.sum_le_sum (fun scalar _ => mul_le_mul_of_nonneg_left
        (positiveTriple_first_polynomial security root scalar) ((scalarLaw security).nonneg scalar))
    _ = _ := FiniteDist.expectation_const _ _

theorem primary_degree_energy (security : ℕ) (root : ℤ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (primaryLawAt security root).weight degree) ≤ 32 * pairBudget security := by
  apply (degreeTensor_mix_energy _ (scalarLaw security) (positiveTripleLaw security root) degree).trans
  calc
    _ ≤ (scalarLaw security).expectation (fun _ => 32 * pairBudget security) :=
      Finset.sum_le_sum (fun scalar _ => mul_le_mul_of_nonneg_left
        (positiveTriple_degree_energy security root scalar degree) ((scalarLaw security).nonneg scalar))
    _ = _ := FiniteDist.expectation_const _ _

theorem singleton_marginal {Color : Type*} [Fintype Color] (law : FiniteDist Color) :
    (singletonLaw law).map (fun word => word 0) = law := by
  apply FiniteDist.ext
  intro color
  rw [singletonLaw, FiniteDist.map_map]
  simp only [FiniteDist.map_weight, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem singleton_first_energy (security : ℕ) (law : FiniteDist (Palette security)) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 1 => uniformReference security)
      (singletonLaw law).weight 1) ≤
      2 * ‖UniformBodyProfiles.uniformVector security law.weight‖ ^ 2 := by
  have h := LocalTensors.first_degree_energy_le (fun _ : Fin 1 => uniformReference security)
    (fun _ color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (singletonLaw law)
  simp only [Fintype.card_fin, Fin.sum_univ_one, singleton_marginal] at h
  rw [UniformBodyProfiles.uniformVector, ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg]
  simpa only [pow_one] using h

theorem singleton_degree_zero {Color : Type*} [Fintype Color] (reference : FiniteDist Color)
    (law : FiniteDist Color) (degree : ℕ) (hdegree : 1 < degree) :
    LocalTensors.degreeTensor (fun _ : Fin 1 => reference) (singletonLaw law).weight degree = 0 := by
  have hz (selected : Finset (Fin 1)) : Fintype.card selected ≠ degree := by
    have hh := Finset.card_le_univ selected
    simp only [Fintype.card_fin] at hh
    simp only [Fintype.card_coe]
    omega
  funext word
  simp only [LocalTensors.degreeTensor, LocalTensors.degreePiece, dif_neg (hz _),
    Finset.sum_const_zero, BlockFock.symmetrize, mul_zero, Pi.zero_apply]

def firstConstant : ℝ := 240 + 6291552 * Real.exp Real.pi
def higherConstant : ℝ := 32 * (524288 + 17180131328 * Real.exp Real.pi) + 1

theorem firstConstant_nonneg : 0 ≤ firstConstant := by unfold firstConstant; positivity
theorem higherConstant_one_le : 1 ≤ higherConstant := by
  unfold higherConstant
  linarith [Real.exp_pos Real.pi]

theorem primary_higher_norm_budget (security : ℕ) (root : ℤ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => uniformReference security)
      (primaryLawAt security root).weight degree) ≤
      (higherConstant * (Parameters.base security : ℝ) ^ 24) ^ 2 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hp := (primary_degree_energy security root degree).trans
    (mul_le_mul_of_nonneg_left (pairBudget_polynomial security) (by norm_num : (0 : ℝ) ≤ 32))
  have hpower : (Parameters.base security : ℝ) ^ 47 ≤ (Parameters.base security : ℝ) ^ 48 :=
    pow_le_pow_right₀ hb1 (by omega)
  have hc : 32 * (524288 + 17180131328 * Real.exp Real.pi) ≤ higherConstant ^ 2 := by
    have := higherConstant_one_le
    unfold higherConstant at *
    nlinarith [Real.exp_pos Real.pi]
  calc
    _ ≤ (32 * (524288 + 17180131328 * Real.exp Real.pi)) * (Parameters.base security : ℝ) ^ 47 :=
      hp.trans_eq (by ring)
    _ ≤ (higherConstant ^ 2) * (Parameters.base security : ℝ) ^ 48 :=
      mul_le_mul hc hpower (pow_nonneg hb.le _) (sq_nonneg _)
    _ = _ := by ring

theorem block_first_energy (security : ℕ) (ar : Fin (Parameters.legCount security) → ℤ)
    (cr : Fin (centerCount security) → ℤ) (qr : Fin (Parameters.modulus security) → ℤ)
    (queue : ℤ) (index : BlockIndex security) :
    BlockFock.tensorEnergy (BlockProducts.localCoefficient (Slots security) (uniformReference security)
      (blockLawAt security ar cr qr queue) index 1) ≤
      match index with
      | .inl _ => firstConstant * (Parameters.base security : ℝ) ^ 31
      | .inr _ => 2 * UniformBodyProfiles.deviation security ^ 2 := by
  cases index with
  | inl leg => exact primary_first_energy security (ar leg)
  | inr body =>
    have hn : ∀ law : FiniteDist (Palette security),
        ‖UniformBodyProfiles.uniformVector security law.weight‖ ≤ UniformBodyProfiles.deviation security →
        BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 1 => uniformReference security)
          (singletonLaw law).weight 1) ≤ 2 * UniformBodyProfiles.deviation security ^ 2 := by
      intro law hbound
      exact (singleton_first_energy security law).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hbound 2) (by norm_num))
    cases body with
    | inl point =>
      apply hn
      rw [UniformBodyProfiles.uniformVector_map_equiv_norm]
      exact UniformBodyProfiles.preRootLaw_norm_le security .free queue
    | inr point =>
      apply hn
      rw [UniformBodyProfiles.uniformVector_map_equiv_norm]
      exact (UniformBodyProfiles.safe_uniform_norm_le security).trans
        (by
          unfold UniformBodyProfiles.deviation
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity))

/-- The whole finite coefficient norm of an actual independent product.
All degrees from zero through the physical population remain in the sum. -/
def productFockEnergy {Index Color : Type*} [Fintype Index] [Fintype Color]
    (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : FiniteDist Color) (law : (index : Index) → FiniteDist (slots index → Color))
    (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card (Sigma slots)) radius
    (fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Sigma slots => reference)
      (BlockProducts.blockMass slots law) degree))

theorem productFockEnergy_le {Index Color : Type*} [Fintype Index] [Fintype Color] [Nonempty Color]
    (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : FiniteDist Color) (law : (index : Index) → FiniteDist (slots index → Color))
    (hslots : ∀ index, Fintype.card (slots index) ≤ 3) (capacity : ℕ) (radius : ℝ)
    (hcapacity : (SelectionBound.nonlinearSupport
      (BlockProducts.normalizedQuadratic slots reference law (radius / Real.sqrt (Fintype.card (Sigma slots))))
      (BlockProducts.normalizedCubic slots reference law (radius / Real.sqrt (Fintype.card (Sigma slots))))).card ≤ capacity)
    (hlinear : (∑ index, ∑ color, BlockProducts.normalizedLinear slots reference law
      (radius / Real.sqrt (Fintype.card (Sigma slots))) index color ^ 2) ≤ 1 / 8)
    (hnonlinear : (∑ index, (128 * SelectionBound.localPairNorm
      (BlockProducts.normalizedQuadratic slots reference law (radius / Real.sqrt (Fintype.card (Sigma slots)))) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (BlockProducts.normalizedCubic slots reference law (radius / Real.sqrt (Fintype.card (Sigma slots)))) index)) ≤ 1 / 2) :
    productFockEnergy slots reference law radius ≤
      16 * Real.exp (8 * ∑ color, (∑ index, BlockProducts.normalizedLinear slots reference law
        (radius / Real.sqrt (Fintype.card (Sigma slots))) index color) ^ 2) := by
  rw [productFockEnergy, ← TensorFock.normalized_fock_isometry _ _ _ (fun degree _ =>
    LocalTensors.degreeTensor_symmetric _ _ degree)]
  simp_rw [BlockProducts.complete_normalized_coefficients slots reference law hslots]
  exact SelectionBound.independent_cubic_block_fock_bound _ _ _ capacity hcapacity hlinear hnonlinear

theorem linearActivity_le (security : ℕ) (ar : Fin (Parameters.legCount security) → ℤ)
    (cr : Fin (centerCount security) → ℤ) (qr : Fin (Parameters.modulus security) → ℤ)
    (scale : ℝ) (queueInteger : ℤ) :
    (∑ index, ∑ color, BlockProducts.normalizedLinear (Slots security) (uniformReference security)
      (blockLawAt security ar cr qr queueInteger) scale index color ^ 2) ≤
      scale ^ 2 * ((Parameters.legCount security : ℝ) * firstConstant * (Parameters.base security : ℝ) ^ 31 +
        2 * (Parameters.bodySize security : ℝ) * UniformBodyProfiles.deviation security ^ 2) := by
  simp_rw [BlockProducts.normalized_linear_energy]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg scale)
  apply (Finset.sum_le_sum (fun index _ => block_first_energy security ar cr qr queueInteger index)).trans
  simp only [Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, Nat.cast_add, nsmul_eq_mul]
  have hcount : centerCount security + Parameters.modulus security ≤ Parameters.bodySize security := by
    have := population_room security
    unfold centerCount
    omega
  have hr : (centerCount security : ℝ) + Parameters.modulus security ≤ Parameters.bodySize security := by exact_mod_cast hcount
  nlinarith [sq_nonneg (UniformBodyProfiles.deviation security)]

theorem nonlinearActivity_le (security : ℕ) (ar : Fin (Parameters.legCount security) → ℤ)
    (cr : Fin (centerCount security) → ℤ) (qr : Fin (Parameters.modulus security) → ℤ)
    (queue : ℤ) (scale : ℝ) (hscale : 0 ≤ scale) (capacity : ℕ) :
    (∑ index, (128 * SelectionBound.localPairNorm
      (BlockProducts.normalizedQuadratic (Slots security) (uniformReference security)
        (blockLawAt security ar cr qr queue) scale) index +
      128 * Real.sqrt capacity * SelectionBound.localTripleNorm
        (BlockProducts.normalizedCubic (Slots security) (uniformReference security)
          (blockLawAt security ar cr qr queue) scale) index)) ≤
      128 * (Parameters.legCount security : ℝ) *
        (scale ^ 2 + Real.sqrt capacity * scale ^ 3) *
          (higherConstant * (Parameters.base security : ℝ) ^ 24) := by
  have hhigher : 0 ≤ higherConstant * (Parameters.base security : ℝ) ^ 24 := by
    have := higherConstant_one_le
    positivity
  have hpoint (index : BlockIndex security) :
      128 * SelectionBound.localPairNorm
        (BlockProducts.normalizedQuadratic (Slots security) (uniformReference security)
          (blockLawAt security ar cr qr queue) scale) index +
      128 * Real.sqrt capacity * SelectionBound.localTripleNorm
        (BlockProducts.normalizedCubic (Slots security) (uniformReference security)
          (blockLawAt security ar cr qr queue) scale) index ≤
      match index with
      | .inl _ => 128 * (scale ^ 2 + Real.sqrt capacity * scale ^ 3) *
          (higherConstant * (Parameters.base security : ℝ) ^ 24)
      | .inr _ => 0 := by
    cases index with
    | inl leg =>
      have hpair := BlockProducts.normalized_quadratic_norm_le (Slots security) (uniformReference security)
        (blockLawAt security ar cr qr queue) scale _ (.inl leg) hhigher
        (primary_higher_norm_budget security (ar leg) 2)
      have htriple := BlockProducts.normalized_cubic_norm_le (Slots security) (uniformReference security)
        (blockLawAt security ar cr qr queue) scale _ (.inl leg) hscale hhigher
        (primary_higher_norm_budget security (ar leg) 3)
      nlinarith [mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 128),
        mul_le_mul_of_nonneg_left htriple (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) (Real.sqrt_nonneg (capacity : ℝ)))]
    | inr body =>
      have hz (law : FiniteDist (Palette security)) :
          128 * Real.sqrt (BlockFock.tensorEnergy (fun word => scale ^ 2 *
            LocalTensors.degreeTensor (fun _ : Fin 1 => uniformReference security) (singletonLaw law).weight 2 word)) +
          128 * Real.sqrt capacity * Real.sqrt (BlockFock.tensorEnergy (fun word => scale ^ 3 *
            LocalTensors.degreeTensor (fun _ : Fin 1 => uniformReference security) (singletonLaw law).weight 3 word)) ≤ 0 := by
        rw [singleton_degree_zero _ _ _ (by omega : 1 < 2), singleton_degree_zero _ _ _ (by omega : 1 < 3)]
        simp only [Pi.zero_apply, mul_zero, BlockFock.tensorEnergy,
          zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero, Real.sqrt_zero, add_zero, le_refl]
      cases body with
      | inl point => exact hz ((centerLaw security).map (shiftEquiv security (cr point)))
      | inr point => exact hz ((safeLaw security).map (shiftEquiv security (qr point + queue)))
  apply (Finset.sum_le_sum (fun index _ => hpoint index)).trans_eq
  simp only [Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_zero, add_zero]
  ring

end

end CurrentAFT.ActualBlockFock

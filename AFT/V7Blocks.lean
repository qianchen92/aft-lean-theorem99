import AFT.FiniteBlockNumbering
import AFT.ActualTripleFirst
import AFT.BodyReferenceEnergy
import AFT.BlockProducts

/-! # The actual V7 independent blocks at a fixed root word and queue -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

namespace LocalTensors

/-- Degrees above the number of physical outputs vanish exactly. -/
theorem degreeTensor_zero_above {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (reference : Slot → FiniteDist Color) (mass : (Slot → Color) → ℝ) (degree : ℕ)
    (hdegree : Fintype.card Slot < degree) : degreeTensor reference mass degree = 0 := by
  have hz (selected : Finset Slot) : Fintype.card selected ≠ degree := by
    have hh := Finset.card_le_univ selected
    simp only [Fintype.card_coe]
    omega
  funext word
  simp only [degreeTensor, degreePiece, dif_neg (hz _), Finset.sum_const_zero,
    BlockFock.symmetrize, mul_zero, Pi.zero_apply]

end LocalTensors

namespace V7Calibration

open Filter GaussianSource
open scoped Topology

def singletonBlockLaw {Color : Type*} [Fintype Color] (law : FiniteDist Color) : FiniteDist (Fin 1 → Color) :=
  law.map (Equiv.funUnique (Fin 1) Color).symm

theorem singletonBlockLaw_marginal {Color : Type*} [Fintype Color] (law : FiniteDist Color) (slot : Fin 1) :
    (singletonBlockLaw law).map (fun word => word slot) = law := by
  rw [singletonBlockLaw, FiniteDist.map_map]
  have heq : (fun color : Color => (Equiv.funUnique (Fin 1) Color).symm color slot) = id := rfl
  rw [heq]
  apply FiniteDist.ext
  intro color
  change (law.map (Equiv.refl Color)).weight color = _
  exact FiniteDist.map_equiv_weight law (Equiv.refl Color) color

set_option backward.isDefEq.respectTransparency false in
theorem singletonBlock_first_energy {Color : Type*} [Fintype Color] (reference law : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 1 => reference) (singletonBlockLaw law).weight 1) ≤
      2 * profileSquareNorm reference.weight (fun color => law.weight color - reference.weight color) := by
  have hh := LocalTensors.first_degree_energy_le (fun _ : Fin 1 => reference) (fun _ => href) (singletonBlockLaw law)
  simp only [Fintype.card_fin, pow_one, Fin.sum_univ_one] at hh
  apply hh.trans_eq
  congr 1
  apply congrArg (profileSquareNorm reference.weight)
  funext color
  congr 1
  have he := singletonBlockLaw_marginal law (0 : Fin 1)
  exact congrArg (fun distribution => distribution.weight color) he

/-- Each leg owns one attached body and two endpoints; every other body is
its own single-output block. -/
abbrev blockIndex (parameter : ℕ) := Fin (Parameters.legs parameter) ⊕ Fin (Parameters.bodies parameter - Parameters.legs parameter)

instance blockIndexFintype (parameter : ℕ) : Fintype (blockIndex parameter) := inferInstanceAs (Fintype (_ ⊕ _))

abbrev blockSlots (parameter : ℕ) (index : blockIndex parameter) :=
  Fin (match index with | .inl _ => 3 | .inr _ => 1)

instance blockSlotsFintype (parameter : ℕ) (index : blockIndex parameter) : Fintype (blockSlots parameter index) := by
  exact inferInstanceAs (Fintype (Fin _))

theorem blockIndex_card (parameter : ℕ) : Fintype.card (blockIndex parameter) = Parameters.bodies parameter := by
  have hh := Parameters.legs_le_half_bodies parameter
  simp only [blockIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Explicit leg-first arithmetic numbering of the actual body roots. -/
def blockIndexNumbering (parameter : ℕ) : blockIndex parameter ≃ Fin (Parameters.bodies parameter) :=
  (blockNumbering (Parameters.legs parameter) (Parameters.bodies parameter-Parameters.legs parameter)).trans
    (finCongr (by have := Parameters.legs_le_half_bodies parameter;omega))

theorem blockSlots_card (parameter : ℕ) : Fintype.card (Sigma (blockSlots parameter)) = Parameters.dimension parameter := by
  have hh := Parameters.legs_le_half_bodies parameter
  have hp := Parameters.population_identity parameter
  rw [Fintype.card_sigma]
  change (∑ index : Fin (Parameters.legs parameter) ⊕ Fin (Parameters.bodies parameter - Parameters.legs parameter), _) = _
  rw [Fintype.sum_sum_type]
  simp only [blockSlots, Fintype.card_fin, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem blockSlots_le_three (parameter : ℕ) (index : blockIndex parameter) :
    Fintype.card (blockSlots parameter index) ≤ 3 := by cases index <;> norm_num [blockSlots]

/-- The actual conditional independent-block family, retaining the common
queue input and the individual fixed root coordinates. -/
def actualBlockFamily (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (root queue : blockIndex parameter → ℤ) :
    (index : blockIndex parameter) → FiniteDist (blockSlots parameter index → Fin (Parameters.modulus parameter))
  | .inl leg => actualFixedRootTripleLaw cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))
  | .inr body => singletonBlockLaw (actualShiftedBodyLaw cutoffScale parameter beta (root (.inr body) + queue (.inr body)))

def actualConditionalBlocks (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (root queue : blockIndex parameter → ℤ) :
    FiniteDist (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) :=
  BlockProducts.blockLaw (blockSlots parameter) (actualBlockFamily cutoffScale parameter beta root queue)

/-- All local coefficient estimates of the genuine family, with the small
single-body energy and the sharp first-order leg energy kept separately. -/
theorem actual_block_coefficient_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : blockIndex parameter → ℤ,
      (∀ index, |root index| ≤ (v7RootCutoff parameter : ℤ)) → (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) →
      let coefficient := BlockProducts.localCoefficient (blockSlots parameter)
        (actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualBlockFamily cutoffScale parameter (beta parameter) root queue)
      (∀ leg, BlockFock.tensorEnergy (coefficient (.inl leg) 1) ≤ 100000 * (parameter : ℝ) ^ 22) ∧
      (∀ leg degree, BlockFock.tensorEnergy (coefficient (.inl leg) degree) ≤ 1576960 * (parameter : ℝ) ^ 30) ∧
      (∀ body, BlockFock.tensorEnergy (coefficient (.inr body) 1) ≤ 10944 / (parameter : ℝ) ^ 38) ∧
      (∀ body degree, 1 < degree → coefficient (.inr body) degree = 0) := by
  filter_upwards [actual_fixed_root_triple_first_power_eventually cutoffScale hscale beta hbeta,
    actual_fixed_root_triple_degree_power_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_reference_energy_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter ht1 ht hb hs hl hr root queue hroot hqueue
  refine ⟨fun leg => ht1 _ _ (hroot _) (hqueue _), fun leg degree => ht _ _ (hroot _) (hqueue _) degree, ?_, ?_⟩
  · intro body
    have hshift : |root (.inr body) + queue (.inr body)| ≤ (maxBodyShift cutoffScale parameter : ℤ) := by
      simpa only [actualSourceShift, add_zero] using
        actualBodyBranch_shift_bound cutoffScale parameter (root (.inr body)) (queue (.inr body)) (hroot _) (hqueue _) (.inl ())
    have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
      rw [hl.2.2]
      exact (by positivity : 0 < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
    have hh := singletonBlock_first_energy (actualReferenceLaw cutoffScale parameter (beta parameter))
      (actualShiftedBodyLaw cutoffScale parameter (beta parameter) (root (.inr body) + queue (.inr body))) href
    rw [hl.2.2, (hs _ hshift).1] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hb _ hshift) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  · intro body degree hd
    apply LocalTensors.degreeTensor_zero_above
    simpa only [blockSlots, Fintype.card_fin] using hd

end V7Calibration
end
end AFT

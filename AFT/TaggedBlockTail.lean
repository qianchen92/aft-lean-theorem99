import AFT.PolynomialTaggedFock
import AFT.MixtureTail

/-! # The complete signed tail of actual marked blocks and their complement -/

namespace AFT.BlockProducts

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

variable {Index Color TaggedSlot : Type*} [Fintype Index] [Fintype Color] [Fintype TaggedSlot]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

local instance {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance : DecidableEq (Sigma Slots) := Classical.decEq _

/-- Actual signed mass: one arbitrary joint tagged output and every remaining
independent physical block. Dependence within the tagged outputs is retained. -/
def taggedBlockMass (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : (TaggedSlot ⊕ Sigma Slots) → Color) : ℝ :=
  tagged (word ∘ Sum.inl) * blockMass Slots law (word ∘ Sum.inr)

set_option backward.isDefEq.respectTransparency false in
theorem tagged_generating_factorization (reference : FiniteDist Color)
    (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : TaggedSlot ⊕ Sigma Slots => reference)
      (taggedBlockMass Slots tagged law) value =
      LocalTensors.localGenerating (fun _ : TaggedSlot => reference) tagged value *
        LocalTensors.localGenerating (fun _ : Sigma Slots => reference) (blockMass Slots law) value := by
  unfold LocalTensors.localGenerating taggedBlockMass
  simp only [Complex.ofReal_mul, Fintype.prod_sum_type]
  have he := (Equiv.sumArrowEquivProdArrow TaggedSlot (Sigma Slots) Color).sum_comp
    (fun point => (((tagged point.1 : ℝ) : ℂ) *
      ∏ slot, (1 + LocalTensors.atomLinear reference (point.1 slot) value)) *
      (((blockMass Slots law point.2 : ℝ) : ℂ) *
        ∏ slot, (1 + LocalTensors.atomLinear reference (point.2 slot) value)))
  calc
    _ = ∑ word : TaggedSlot ⊕ Sigma Slots → Color,
        (((tagged (word ∘ Sum.inl) : ℝ) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word (Sum.inl slot)) value)) *
        (((blockMass Slots law (word ∘ Sum.inr) : ℝ) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word (Sum.inr slot)) value)) := by
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ = ∑ point : (TaggedSlot → Color) × (Sigma Slots → Color),
        (((tagged point.1 : ℝ) : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (point.1 slot) value)) *
        (((blockMass Slots law point.2 : ℝ) : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (point.2 slot) value)) := he
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The finite marked-coefficient budget computed from the actual signed mass. -/
def taggedCoefficientEnergy (reference : FiniteDist Color) (tagged : (TaggedSlot → Color) → ℝ)
    (population : ℕ) (radius : ℝ) : ℝ :=
  (Fintype.card TaggedSlot + 1 : ℕ) * ∑ degree ∈ Finset.range (Fintype.card TaggedSlot + 1),
    (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy
      (TensorFock.normalizedTensor population radius
        (LocalTensors.degreeTensor (fun _ : TaggedSlot => reference) tagged) degree)

set_option backward.isDefEq.respectTransparency false in
/-- The full Gaussian Fock energy is bounded for the concrete signed joint
output law. Its tagged polynomial is derived from its actual mass in every
degree, and the independent complement retains all degrees as well. -/
theorem tagged_block_fock_energy_le [Nonempty Color]
    (reference : FiniteDist Color) (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (capacity : ℕ) (radius : ℝ)
    (hcapacity : (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index word)
      (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
        (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index word)).card ≤ capacity)
    (henergy : (∑ index, ∑ color, (Real.sqrt 2 * normalizedLinear Slots reference law
      (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index color) ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
            (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index word) index)) ≤ 1 / 2) :
    HistogramTail.fockEnergy (Fintype.card (TaggedSlot ⊕ Sigma Slots)) radius
      (fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : TaggedSlot ⊕ Sigma Slots => reference) (taggedBlockMass Slots tagged law) degree)) ≤
      taggedCoefficientEnergy reference tagged (Fintype.card (TaggedSlot ⊕ Sigma Slots)) radius *
        (16 * Real.exp (8 * ∑ color, (∑ index, Real.sqrt 2 * normalizedLinear Slots reference law
          (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index color) ^ 2)) := by
  let population := Fintype.card (TaggedSlot ⊕ Sigma Slots)
  let coefficient := LocalTensors.degreeTensor (fun _ : TaggedSlot ⊕ Sigma Slots => reference)
    (taggedBlockMass Slots tagged law)
  have hiso := TensorFock.normalized_fock_isometry population radius coefficient
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
  rw [← hiso]
  have hpoly (value : Color → ℂ) :
      TensorFock.seriesEvaluation (Finset.range (population + 1))
        (TensorFock.normalizedTensor population radius coefficient) value =
      TensorFock.seriesEvaluation (Finset.range (Fintype.card TaggedSlot + 1))
        (TensorFock.normalizedTensor population radius
          (LocalTensors.degreeTensor (fun _ : TaggedSlot => reference) tagged)) value *
        NonlinearFock.cubicBlockProduct
          (normalizedLinear Slots reference law (radius / Real.sqrt population))
          (normalizedQuadratic Slots reference law (radius / Real.sqrt population))
          (normalizedCubic Slots reference law (radius / Real.sqrt population)) value := by
    have htotal := LocalTensors.localGenerating_series
      (fun _ : TaggedSlot ⊕ Sigma Slots => reference) (taggedBlockMass Slots tagged law)
      (fun color => ((radius / Real.sqrt population : ℝ) : ℂ) * value color)
    have htag := LocalTensors.localGenerating_series (fun _ : TaggedSlot => reference) tagged
      (fun color => ((radius / Real.sqrt population : ℝ) : ℂ) * value color)
    simp only [TensorFock.seriesEvaluation, NonlinearFock.tensorEvaluation_dilate, Fintype.card_fin] at htotal htag
    have htotal' : TensorFock.seriesEvaluation (Finset.range (population + 1))
        (TensorFock.normalizedTensor population radius coefficient) value =
        LocalTensors.localGenerating (fun _ : TaggedSlot ⊕ Sigma Slots => reference)
          (taggedBlockMass Slots tagged law)
          (fun color => ((radius / Real.sqrt population : ℝ) : ℂ) * value color) := htotal.symm
    rw [htotal', tagged_generating_factorization, normalized_generating_factorization Slots reference law hslots]
    rw [htag]
    rfl
  simp_rw [hpoly]
  have h := TaggedFock.polynomial_cubic_block_energy_le
    (Finset.range (Fintype.card TaggedSlot + 1))
    (TensorFock.normalizedTensor population radius (LocalTensors.degreeTensor (fun _ : TaggedSlot => reference) tagged))
    (normalizedLinear Slots reference law (radius / Real.sqrt population))
    (normalizedQuadratic Slots reference law (radius / Real.sqrt population))
    (normalizedCubic Slots reference law (radius / Real.sqrt population)) capacity hcapacity henergy hsmall
  simpa only [Finset.card_range, taggedCoefficientEnergy] using h

/-- The three explicit local coefficient conditions of the independent-block
estimate, at its doubled radius. -/
def CubicBlockConditions (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (population capacity : ℕ) (radius : ℝ) : Prop :=
  (SelectionBound.nonlinearSupport
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word)
      (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
        (radius / Real.sqrt population) index word)).card ≤ capacity ∧
  (∑ index, ∑ color, (Real.sqrt 2 * normalizedLinear Slots reference law
      (radius / Real.sqrt population) index color) ^ 2) ≤ 1 / 8 ∧
  (∑ index, (128 * SelectionBound.localPairNorm
      (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
            (radius / Real.sqrt population) index word) index)) ≤ 1 / 2

set_option backward.isDefEq.respectTransparency false in
/-- Complete actual signed likelihood tail for arbitrary jointly tagged
outputs and the independent complement. The exact finite population is used
in every degree through the maximum possible output degree. -/
theorem tagged_block_complete_tail [Nonempty Color]
    (reference : FiniteDist Color) (hreference : ∀ color, 0 < reference.weight color)
    (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (cutoff capacity : ℕ) (radius : ℝ)
    (hpopulation : 0 < Fintype.card (TaggedSlot ⊕ Sigma Slots))
    (hradius : Real.exp 1 ≤ radius ^ 2)
    (hlocal : CubicBlockConditions Slots reference law (Fintype.card (TaggedSlot ⊕ Sigma Slots)) capacity radius) :
    (FiniteDist.independent (fun _ : TaggedSlot ⊕ Sigma Slots => reference)).l2Sq
      (HistogramNormalization.densityTail reference
        (HistogramNormalization.symmetrizedMass (taggedBlockMass Slots tagged law)) cutoff) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (taggedCoefficientEnergy reference tagged (Fintype.card (TaggedSlot ⊕ Sigma Slots)) radius *
          (16 * Real.exp (8 * ∑ color, (∑ index, Real.sqrt 2 * normalizedLinear Slots reference law
            (radius / Real.sqrt (Fintype.card (TaggedSlot ⊕ Sigma Slots))) index color) ^ 2))) := by
  rw [HistogramNormalization.symmetrized_densityTail_energy reference hreference (taggedBlockMass Slots tagged law) cutoff]
  apply (HistogramTail.complete_tail_energy_le _ cutoff radius _ hpopulation
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hradius).trans
  exact mul_le_mul_of_nonneg_left
    (tagged_block_fock_energy_le Slots reference tagged law hslots capacity radius hlocal.1 hlocal.2.1 hlocal.2.2)
    (by positivity)

end

end AFT.BlockProducts

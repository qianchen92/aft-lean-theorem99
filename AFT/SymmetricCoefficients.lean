import AFT.HistogramNormalization
import AFT.TensorCoefficientUnique

/-! # Symmetrization preserves the actual complete coefficient sequence -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual signed mass after an independently uniform permutation. -/
noncomputable def symmetrizedMass (mass : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  BlockFock.symmetrize mass

omit [Fintype Color] in
/-- Uniformly averaging actual position permutations gives exchangeability. -/
theorem symmetrizedMass_exchangeable (mass : (Slot → Color) → ℝ) :
    ExchangeableMass (symmetrizedMass mass) :=
  NonlinearFock.symmetrize_symmetric mass

set_option backward.isDefEq.respectTransparency false in
/-- Symmetrizing the physical law leaves its complete centered-color
generating polynomial unchanged. -/
theorem generating_symmetrizedMass (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : Slot => reference) (symmetrizedMass mass) value =
      LocalTensors.localGenerating (fun _ : Slot => reference) mass value := by
  have hperm (permutation : Equiv.Perm Slot) :
      (∑ word, (mass (word ∘ permutation) : ℂ) *
        ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value)) =
      LocalTensors.localGenerating (fun _ : Slot => reference) mass value := by
    have hprod (word : Slot → Color) :
        (∏ slot, (1 + LocalTensors.atomLinear reference ((word ∘ permutation) slot) value)) =
          ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value) :=
      Equiv.prod_comp permutation (fun slot => 1 + LocalTensors.atomLinear reference (word slot) value)
    have h := (precomposeEquiv (Color := Color) permutation).sum_comp
      (fun word => (mass word : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value))
    change (∑ word, (mass (word ∘ permutation) : ℂ) *
      ∏ slot, (1 + LocalTensors.atomLinear reference ((word ∘ permutation) slot) value)) = _ at h
    simpa only [hprod] using h
  unfold LocalTensors.localGenerating symmetrizedMass BlockFock.symmetrize
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  simp_rw [hperm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, FiniteDist.sum_one]
  simp only [Complex.ofReal_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every actual symmetric homogeneous coefficient is unchanged by
symmetrizing the source law. -/
theorem degreeTensor_symmetrizedMass (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (hdegree : degree ≤ Fintype.card Slot) :
    LocalTensors.degreeTensor (fun _ : Slot => reference) (symmetrizedMass mass) degree =
      LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree := by
  apply TensorFock.series_coefficients_unique (Finset.range (Fintype.card Slot + 1))
    (LocalTensors.degreeTensor (fun _ : Slot => reference) (symmetrizedMass mass))
    (LocalTensors.degreeTensor (fun _ : Slot => reference) mass)
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
    _ degree (Finset.mem_range.mpr (Nat.lt_succ_of_le hdegree))
  intro value
  rw [← LocalTensors.localGenerating_series, ← LocalTensors.localGenerating_series]
  exact generating_symmetrizedMass reference mass value

set_option backward.isDefEq.respectTransparency false in
/-- Exact actual symmetrized-likelihood tail identity for an arbitrary
signed original law. The right-hand side uses its original constructed
coefficients, not coefficients of an assumed surrogate experiment. -/
theorem symmetrized_densityTail_energy (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color) (mass : (Slot → Color) → ℝ) (cutoff : ℕ) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityTail reference (symmetrizedMass mass) cutoff) =
      HistogramTail.likelihoodTailEnergy (Fintype.card Slot) cutoff
        (fun degree => BlockFock.tensorEnergy
          (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree)) := by
  rw [densityTail_energy reference hreference _ (symmetrizedMass_exchangeable mass)]
  unfold HistogramTail.likelihoodTailEnergy
  apply Finset.sum_congr rfl
  intro degree hdegree
  dsimp only
  rw [degreeTensor_symmetrizedMass reference mass degree
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hdegree).1))]

set_option backward.isDefEq.respectTransparency false in
/-- A position permutation transports the actual Hoeffding subset. -/
theorem densityComponent_relabel (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (hexchangeable : ExchangeableMass mass)
    (selected : Finset Slot) (word : Slot → Color) (permutation : Equiv.Perm Slot) :
    Hoeffding.densityComponent (fun _ : Slot => reference) mass selected (word ∘ permutation) =
      Hoeffding.densityComponent (fun _ : Slot => reference) mass
        (selected.map permutation.toEmbedding) word := by
  unfold Hoeffding.densityComponent
  have h := (precomposeEquiv (Color := Color) permutation).sum_comp
    (fun input => mass input * ∏ slot ∈ selected,
      Hoeffding.centeredAtom reference (input slot) ((word ∘ permutation) slot))
  calc
    _ = ∑ input : Slot → Color, mass (input ∘ permutation) * ∏ slot ∈ selected,
        Hoeffding.centeredAtom reference ((input ∘ permutation) slot) ((word ∘ permutation) slot) := h.symm
    _ = _ := by
      apply Finset.sum_congr (by ext; simp)
      intro input _
      rw [hexchangeable input permutation, Finset.prod_map]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every actual full-degree cutoff preserves exchangeability. -/
theorem densityTail_exchangeable (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (hexchangeable : ExchangeableMass mass) (cutoff : ℕ) :
    ExchangeableMass (densityTail reference mass cutoff) := by
  intro word permutation
  unfold densityTail
  simp_rw [densityComponent_relabel reference mass hexchangeable]
  apply Finset.sum_equiv (Equiv.finsetCongr permutation)
  · intro selected
    simp [Equiv.finsetCongr]
  · intro selected _
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual independent uniform permutation sampler has the explicit
symmetrized mass used by the full-degree identities. -/
theorem sampler_symmetrize_weight {population : ℕ}
    (law : FiniteDist (Fin population → Color)) (word : Fin population → Color) :
    (AFT.symmetrize law).weight word = symmetrizedMass law.weight word := by
  rw [AFT.symmetrize_eq_permutation_mix]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight, symmetrizedMass,
    BlockFock.symmetrize, FiniteDist.uniform_weight]
  simp only [Fintype.card_perm, Fintype.card_fin]
  apply Finset.sum_equiv (Equiv.inv (Equiv.Perm (Fin population)))
  · intro permutation
    simp
  · intro permutation _
    rfl

omit [Fintype Slot] in
set_option backward.isDefEq.respectTransparency false in
/-- Complete finite histogram isometry for the actual tail of an arbitrary
law after its actual uniform relabeling. The coefficient sequence is that of
the original law, and the denominator remains the finite falling factorial. -/
theorem actual_histogram_tail_identity {population : ℕ}
    (reference : FiniteDist Color) (hreference : ∀ color, 0 < reference.weight color)
    (law : FiniteDist (Fin population → Color)) (cutoff : ℕ) :
    ∃ histogramTail : Histogram population Color → ℝ,
      densityTail reference (AFT.symmetrize law).weight cutoff = histogramTail ∘ histogram ∧
      ((FiniteDist.independent (fun _ : Fin population => reference)).map histogram).l2Sq histogramTail =
        HistogramTail.likelihoodTailEnergy population cutoff
          (fun degree => BlockFock.tensorEnergy
            (LocalTensors.degreeTensor (fun _ : Fin population => reference) law.weight degree)) := by
  have hmass : (AFT.symmetrize law).weight = symmetrizedMass law.weight :=
    funext (sampler_symmetrize_weight law)
  have hexchangeable := densityTail_exchangeable reference (symmetrizedMass law.weight)
    (symmetrizedMass_exchangeable law.weight) cutoff
  obtain ⟨tail, htail, hnorm⟩ := exchangeable_histogram_l2Sq
    (FiniteDist.independent (fun _ : Fin population => reference))
    (densityTail reference (symmetrizedMass law.weight) cutoff) hexchangeable
  refine ⟨tail, ?_, ?_⟩
  · simpa only [hmass] using htail
  · rw [hnorm]
    have h := symmetrized_densityTail_energy reference hreference law.weight cutoff
    simp only [Fintype.card_fin] at h
    apply Eq.trans ?_ h
    unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

end HistogramNormalization
end AFT

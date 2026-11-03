import AFT.LocalTensors
import AFT.TaggedFock

/-! # Full coefficient and tail bounds for actual independent finite output blocks -/

namespace AFT
namespace BlockProducts

open scoped BigOperators Classical

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The exact product mass on all physical output positions, with one
independent finite law per block and arbitrary dependence within each block. -/
noncomputable def blockMass (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : Sigma Slots → Color) : ℝ :=
  ∏ index, (law index).weight (fun slot => word ⟨index, slot⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual independent block mass sums to one. -/
theorem blockMass_sum (law : (index : Index) → FiniteDist (Slots index → Color)) :
    (∑ word, blockMass Slots law word) = 1 := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, (law index).weight (word index))
  have hmass : (∑ word : (index : Index) → Slots index → Color,
      ∏ index, (law index).weight (word index)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [FiniteDist.sum_one, Finset.prod_const_one]
  apply Eq.trans ?_ (hequiv.trans hmass)
  unfold blockMass
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- The complete finite output law of independent physical blocks. -/
noncomputable def blockLaw (law : (index : Index) → FiniteDist (Slots index → Color)) :
    FiniteDist (Sigma Slots → Color) where
  weight := blockMass Slots law
  nonneg _ := Finset.prod_nonneg fun index _ => (law index).nonneg _
  sum_one := blockMass_sum Slots law

set_option backward.isDefEq.respectTransparency false in
/-- Exact generating-polynomial factorization for actual independent block
laws; no Fock or asymptotic statement is assumed. -/
theorem generating_factorization (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : Sigma Slots => reference) (blockMass Slots law) value =
      ∏ index, LocalTensors.localGenerating (fun _ : Slots index => reference) (law index).weight value := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, ((law index).weight (word index) : ℂ) *
      ∏ slot, (1 + LocalTensors.atomLinear reference (word index slot) value))
  unfold LocalTensors.localGenerating blockMass
  simp only [Complex.ofReal_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma Slots → Color,
        ∏ index, (((law index).weight (fun slot => word ⟨index, slot⟩) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word ⟨index, slot⟩) value)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → Slots index → Color,
        ∏ index, (((law index).weight (word index) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word index slot) value)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : Slots index → Color) =>
      ((law index).weight word : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value))).symm

/-- The actual homogeneous tensor of one physical block. -/
noncomputable def localCoefficient (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (index : Index) (degree : ℕ) :=
  LocalTensors.degreeTensor (fun _ : Slots index => reference) (law index).weight degree

/-- Actual normalized first coefficient for each block. -/
noncomputable def normalizedLinear (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) : ℝ :=
  scale * localCoefficient Slots reference law index 1 (fun _ => color)

/-- Actual normalized second coefficient for each block. -/
noncomputable def normalizedQuadratic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 2 → Color) : ℝ :=
  scale ^ 2 * localCoefficient Slots reference law index 2 word

/-- Actual normalized third coefficient for each block. -/
noncomputable def normalizedCubic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 3 → Color) : ℝ :=
  scale ^ 3 * localCoefficient Slots reference law index 3 word

set_option backward.isDefEq.respectTransparency false in
/-- The actual block product, after normalization, is exactly a cubic product
with the constructed physical coefficients. -/
theorem normalized_generating_factorization (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (scale : ℝ) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : Sigma Slots => reference) (blockMass Slots law)
        (fun color => (scale : ℂ) * value color) =
      NonlinearFock.cubicBlockProduct (normalizedLinear Slots reference law scale)
        (normalizedQuadratic Slots reference law scale) (normalizedCubic Slots reference law scale) value := by
  rw [generating_factorization]
  simp_rw [LocalTensors.localGenerating_cubic _ _ (hslots _)]
  change NonlinearFock.cubicBlockProduct
    (fun index color => localCoefficient Slots reference law index 1 (fun _ => color))
      (fun index => localCoefficient Slots reference law index 2)
      (fun index => localCoefficient Slots reference law index 3)
        (fun color => (scale : ℂ) * value color) = _
  exact TaggedFock.cubicBlockProduct_dilate _ _ _ scale value

set_option backward.isDefEq.respectTransparency false in
/-- The complete global coefficient identity is proved for the physical
product law, up through its actual full population size. -/
theorem complete_normalized_coefficients (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (radius : ℝ) (value : Color → ℂ) :
    TensorFock.seriesEvaluation (Finset.range (Fintype.card (Sigma Slots) + 1))
      (TensorFock.normalizedTensor (Fintype.card (Sigma Slots)) radius
        (LocalTensors.degreeTensor (fun _ : Sigma Slots => reference) (blockMass Slots law))) value =
      NonlinearFock.cubicBlockProduct
        (normalizedLinear Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))
        (normalizedQuadratic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))
        (normalizedCubic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots)))) value := by
  rw [← normalized_generating_factorization Slots reference law hslots]
  rw [LocalTensors.localGenerating_series]
  simp only [TensorFock.seriesEvaluation, NonlinearFock.tensorEvaluation_dilate, Fintype.card_fin]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full finite histogram coefficient tail for actual independent probability
blocks of size at most three. Every coefficient and the exact global product
identity are constructed here; the premises are only the local smallness
conditions and population/radius conditions of the analytic estimate. -/
theorem actual_block_complete_tail [Nonempty Color]
    (reference : FiniteDist Color) (law : (index : Index) → FiniteDist (Slots index → Color))
    (hslots : ∀ index, Fintype.card (Slots index) ≤ 3) (cutoff capacity : ℕ) (radius : ℝ)
    (hpopulation : 0 < Fintype.card (Sigma Slots)) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hcapacity : (SelectionBound.nonlinearSupport
      (normalizedQuadratic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))
      (normalizedCubic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))))).card ≤ capacity)
    (henergy : (∑ index, ∑ color,
      normalizedLinear Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color ^ 2) ≤ 1 / 8)
    (hsmall : (∑ index, (128 * SelectionBound.localPairNorm
      (normalizedQuadratic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots)))) index +
        128 * Real.sqrt capacity * SelectionBound.localTripleNorm
          (normalizedCubic Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots)))) index)) ≤ 1 / 2) :
    HistogramTail.likelihoodTailEnergy (Fintype.card (Sigma Slots)) cutoff
      (fun degree => BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Sigma Slots => reference) (blockMass Slots law) degree)) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (16 * Real.exp (8 * ∑ color, (∑ index,
          normalizedLinear Slots reference law (radius / Real.sqrt (Fintype.card (Sigma Slots))) index color) ^ 2)) := by
  exact SelectionBound.complete_cubic_histogram_tail_uniform
    (Fintype.card (Sigma Slots)) cutoff capacity radius _ _ _ _ hpopulation hradius
    (fun degree _ word permutation => LocalTensors.degreeTensor_symmetric _ _ degree word permutation)
    (complete_normalized_coefficients Slots reference law hslots radius) hcapacity henergy hsmall

end BlockProducts
end AFT

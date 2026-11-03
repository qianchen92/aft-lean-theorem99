import CurrentAFT.CycleKernel
import CurrentAFT.CycleSelections

/-!
# Complete selected-cycle likelihood from its actual transfer matrices

Unselected edges use the rank-one boundary matrix and cost energy one.
Selected edges use their true one-difference response. The finite cyclic
Cauchy--Schwarz bound is applied to the whole cycle before any averaging.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Extend selected scalar factors by one off their actual embedding. -/
def embeddedFactor {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (point : Pool) : ℝ :=
  if h : ∃ slot, embedding slot = point then factor (Classical.choose h) else 1

theorem embeddedFactor_at {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (slot : Selected) :
    embeddedFactor embedding factor (embedding slot) = factor slot := by
  unfold embeddedFactor
  split_ifs with h
  · apply congrArg factor
    exact embedding.injective (Classical.choose_spec h)
  · exact False.elim (h ⟨slot, rfl⟩)

theorem embeddedFactor_absent {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (point : Pool) (habsent : ¬∃ slot, embedding slot = point) :
    embeddedFactor embedding factor point = 1 := by
  unfold embeddedFactor
  rw [dif_neg habsent]

/-- Products through an embedding keep every selected factor exactly once. -/
theorem embeddedFactor_product {Selected Pool : Type*} [Fintype Selected] [Fintype Pool]
    (embedding : Selected ↪ Pool) (factor : Pool → Selected → ℝ) :
    (∏ point, embeddedFactor embedding (factor point) point) =
      ∏ slot, factor (embedding slot) slot := by
  have houtside (point : Pool) (_ : point ∈ (Finset.univ : Finset Pool))
      (hnot : point ∉ Finset.univ.map embedding) : embeddedFactor embedding (factor point) point = 1 := by
    apply embeddedFactor_absent
    intro hexists
    obtain ⟨slot, hslot⟩ := hexists
    exact hnot (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, hslot⟩)
  have hproduct := Finset.prod_subset (Finset.subset_univ (Finset.univ.map embedding)) houtside
  rw [← hproduct, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro slot _
  exact embeddedFactor_at embedding (factor (embedding slot)) slot

variable {Scalar Difference : Type*} [Fintype Scalar] [Fintype Difference]

/-- Exact cyclic feature law. For integer subtraction this is the protected
cycle, with the same latent scalar used at both adjacent roots. -/
def selectedFeatureLaw (body order : ℕ) (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order) :
    FiniteDist (Fin order → Difference) :=
  (FiniteDist.independent (fun _ : Fin body => source)).map (fun latent slot =>
    difference (latent ((finRotate body).symm (sites slot))) (latent (sites slot)))

/-- An unconstrained edge keeps the rank-one boundary matrix. -/
def constraintMatrix {body order : ℕ} (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) (vertex : Fin body) : Matrix Scalar Scalar ℝ :=
  fun first second => PathLikelihood.boundary source first * PathLikelihood.boundary source second *
    embeddedFactor sites (fun slot => if difference first second = output slot then 1 else 0) vertex

/-- Every matrix has its actual marginal energy, or one for an unselected edge. -/
theorem constraintMatrix_energy {body order : ℕ} (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) (vertex : Fin body) :
    CycleKernel.energy (constraintMatrix source difference sites output vertex) =
      embeddedFactor sites (fun slot => (PathLikelihood.marginal source difference).weight (output slot)) vertex := by
  by_cases hexists : ∃ slot, sites slot = vertex
  · obtain ⟨slot, rfl⟩ := hexists
    rw [embeddedFactor_at]
    have hmatrix : constraintMatrix source difference sites output (sites slot) =
        PathLikelihood.transfer source difference (output slot) := by
      ext first second
      unfold constraintMatrix PathLikelihood.transfer
      rw [embeddedFactor_at]
      split_ifs <;> ring
    rw [hmatrix]
    exact PathLikelihood.transfer_square_sum source difference (output slot)
  · have hfactor (factor : Fin order → ℝ) : embeddedFactor sites factor vertex = 1 :=
      embeddedFactor_absent sites factor vertex hexists
    unfold CycleKernel.energy constraintMatrix
    simp_rw [hfactor, mul_one, mul_pow, PathLikelihood.boundary_sq]
    simp only [← Finset.mul_sum, source.sum_one, mul_one]

/-- The exact selected joint mass is the full cyclic matrix partition sum. -/
theorem selectedFeatureLaw_partition (body order : ℕ) (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) :
    (selectedFeatureLaw body order source difference sites).weight output =
      ∑ latent : Fin body → Scalar, ∏ index : Fin body,
        constraintMatrix source difference sites output (finRotate body index)
          (latent index) (latent (finRotate body index)) := by
  unfold selectedFeatureLaw
  simp only [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro latent _
  have hboundary :
      (∏ index : Fin body, PathLikelihood.boundary source (latent index) *
        PathLikelihood.boundary source (latent (finRotate body index))) =
      ∏ index : Fin body, source.weight (latent index) := by
    rw [Finset.prod_mul_distrib]
    rw [Equiv.prod_comp (finRotate body) (fun index => PathLikelihood.boundary source (latent index))]
    rw [← pow_two, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro index _
    exact PathLikelihood.boundary_sq source _
  have hconstraints :
      (∏ index : Fin body, embeddedFactor sites
        (fun slot => if difference (latent index) (latent (finRotate body index)) = output slot then (1 : ℝ) else 0)
        (finRotate body index)) =
      if (fun slot => difference (latent ((finRotate body).symm (sites slot))) (latent (sites slot))) = output
        then 1 else 0 := by
    have hreindex := Equiv.prod_comp (finRotate body) (fun vertex => embeddedFactor sites
      (fun slot => if difference (latent ((finRotate body).symm vertex)) (latent vertex) = output slot then (1 : ℝ) else 0) vertex)
    apply Eq.trans (by simpa only [Equiv.symm_apply_apply] using hreindex)
    rw [embeddedFactor_product, Fintype.prod_ite_zero, Finset.prod_const_one]
    simp only [funext_iff]
    congr 1
  symm
  change (∏ index, (PathLikelihood.boundary source (latent index) *
    PathLikelihood.boundary source (latent (finRotate body index))) * _) = _
  rw [Finset.prod_mul_distrib]
  rw [hboundary, hconstraints]
  split_ifs <;> simp [FiniteDist.independent]

/-- Genuine complete joint-mass bound for every fixed selection. Independence
is used only for the latent scalar table, never for the roots themselves. -/
theorem selectedFeatureLaw_weight_sq_le (body order : ℕ) (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (sites : Selection body order) (output : Fin order → Difference) :
    (selectedFeatureLaw body order source difference sites).weight output ^ 2 ≤
      ∏ slot, (PathLikelihood.marginal source difference).weight (output slot) := by
  have henergy :
      (∏ index : Fin body, CycleKernel.energy
        (constraintMatrix source difference sites output (finRotate body index))) =
      ∏ slot, (PathLikelihood.marginal source difference).weight (output slot) := by
    simp_rw [constraintMatrix_energy]
    rw [Equiv.prod_comp (finRotate body)]
    exact embeddedFactor_product sites (fun _ slot => (PathLikelihood.marginal source difference).weight (output slot))
  rw [selectedFeatureLaw_partition]
  rw [← henergy]
  cases body with
  | zero => omega
  | succ body =>
    cases body with
    | zero => omega
    | succ length =>
      exact CycleKernel.cycle_partition_sq_le length
        (fun index => constraintMatrix source difference sites output (finRotate (length + 2) index))

end

end CurrentAFT.CycleSelections

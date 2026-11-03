import AFT.LocalTensors

/-! # Actual shared-source output laws and all their local homogeneous energies -/

namespace AFT
namespace PhysicalBlockTensors

open scoped BigOperators Classical

variable {Color Source : Type*} [Fintype Color] [Fintype Source]
noncomputable section

local instance (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

/-- Enumerate exactly the two endpoints and their attached body. -/
def tripleEquiv : (Fin 3 → Color) ≃ ((Color × Color) × Color) where
  toFun word := ((word 0, word 1), word 2)
  invFun point := ![point.1.1, point.1.2, point.2]
  left_inv word := by ext index; fin_cases index <;> rfl
  right_inv point := by rcases point with ⟨⟨first, second⟩, third⟩; rfl

/-- Actual joint mass, indexed by its three output positions. -/
noncomputable def tripleMass (mass : Color → Color → Color → ℝ) (word : Fin 3 → Color) : ℝ :=
  mass (word 0) (word 1) (word 2)

omit [Fintype Source] in
set_option backward.isDefEq.respectTransparency false in
/-- The full signed three-output density energy is exactly the concrete
endpoint/attachment weighted square sum. -/
theorem triple_density_energy (reference : FiniteDist Color) (mass : Color → Color → Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 3 => reference)).l2Sq
      (fun word => tripleMass mass word /
        (FiniteDist.independent (fun _ : Fin 3 => reference)).weight word) =
      BlockDensity.tripleEnergy reference.weight reference.weight reference.weight mass := by
  change densitySquareNorm (FiniteDist.independent (fun _ : Fin 3 => reference)).weight
    (fun word => tripleMass mass word /
      (FiniteDist.independent (fun _ : Fin 3 => reference)).weight word) = _
  rw [densityScore_square]
  unfold profileSquareNorm
  rw [← tripleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold BlockDensity.tripleEnergy
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  simp [FiniteDist.independent, tripleEquiv, tripleMass, Fin.prod_univ_succ]
  ring

omit [Fintype Source] in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual local degree of a three-output signed law costs at most
an absolute factor times its full joint energy. -/
theorem triple_degree_energy_le (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color)
    (mass : Color → Color → Color → ℝ) (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => reference)
      (tripleMass mass) degree) ≤
      8 * BlockDensity.tripleEnergy reference.weight reference.weight reference.weight mass := by
  have h := LocalTensors.degreeTensor_energy_le (fun _ : Fin 3 => reference)
    (fun _ color => hreference color) (tripleMass mass) degree
  rw [triple_density_energy] at h
  norm_num at h ⊢
  exact h

/-- The genuine three-output sampler, with no duplicated source variables. -/
noncomputable def sharedSourceTriple (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) : FiniteDist (Fin 3 → Color) :=
  (BlockDensity.attachedLaw source pair body).map tripleEquiv.symm

/-- Exact mass of the concrete shared-source sampler. -/
theorem sharedSourceTriple_weight (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (word : Fin 3 → Color) :
    (sharedSourceTriple source pair body).weight word =
      tripleMass (BlockDensity.attachedMass source pair body) word := by
  rw [sharedSourceTriple, FiniteDist.map_equiv_weight]
  exact BlockDensity.attachedLaw_weight source pair body (word 0) (word 1) (word 2)

/-- Complete physical local coefficient bound: the full shared-source triple
and every one of its homogeneous degrees are bounded by the actual averaged
endpoint energy and the fresh body's pointwise density ratio. -/
theorem shared_source_degree_energy_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color)
    (reference : FiniteDist Color) (bodyLower bodyUpper : ℝ)
    (hlower : 0 < bodyLower) (hupper : 0 ≤ bodyUpper)
    (href : ∀ color, bodyLower ≤ reference.weight color)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ bodyUpper)
    (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => reference)
      (sharedSourceTriple source pair body).weight degree) ≤
      8 * (bodyUpper / bodyLower) * BlockDensity.pairEnergy reference.weight reference.weight
        (fun first second => (source.mix pair).weight (first, second)) := by
  have hmass : (sharedSourceTriple source pair body).weight =
      tripleMass (BlockDensity.attachedMass source pair body) := funext (sharedSourceTriple_weight source pair body)
  rw [hmass]
  apply (triple_degree_energy_le reference (fun color => hlower.trans_le (href color)) _ degree).trans
  have h := BlockDensity.attached_triple_energy_le source pair body reference.weight reference.weight
    reference.weight bodyLower bodyUpper hlower hupper (fun color => hlower.trans_le (href color))
      (fun color => hlower.trans_le (href color)) href hbody
  nlinarith

/-- Enumerate the compensator together with the genuine attached triple. -/
def quadrupleEquiv : (Fin 4 → Color) ≃ (Color × ((Color × Color) × Color)) where
  toFun word := (word 0, ((word 1, word 2), word 3))
  invFun point := ![point.1, point.2.1.1, point.2.1.2, point.2.2]
  left_inv word := by ext index; fin_cases index <;> rfl
  right_inv point := by rcases point with ⟨compensator, ⟨⟨first, second⟩, third⟩⟩; rfl

/-- The actual signed four-output mass of a fresh compensator and one triple. -/
def compensatedTripleMass (compensator : Color → ℝ)
    (mass : Color → Color → Color → ℝ) (word : Fin 4 → Color) : ℝ :=
  compensator (word 0) * mass (word 1) (word 2) (word 3)

omit [Fintype Source] in
set_option backward.isDefEq.respectTransparency false in
/-- The full signed compensator-times-triple density energy factors exactly;
the attached triple itself retains its genuine shared source. -/
theorem compensated_triple_density_energy (reference : FiniteDist Color)
    (compensator : Color → ℝ) (mass : Color → Color → Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 4 => reference)).l2Sq
      (fun word => compensatedTripleMass compensator mass word /
        (FiniteDist.independent (fun _ : Fin 4 => reference)).weight word) =
      profileSquareNorm reference.weight compensator *
        BlockDensity.tripleEnergy reference.weight reference.weight reference.weight mass := by
  change densitySquareNorm (FiniteDist.independent (fun _ : Fin 4 => reference)).weight
    (fun word => compensatedTripleMass compensator mass word /
      (FiniteDist.independent (fun _ : Fin 4 => reference)).weight word) = _
  rw [densityScore_square]
  unfold profileSquareNorm
  rw [← quadrupleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold BlockDensity.tripleEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro color _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro attached _
  simp [FiniteDist.independent, quadrupleEquiv, compensatedTripleMass, Fin.prod_univ_succ]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- All local degrees, including the marked fourth degree, for the actual
independent compensator and actual shared-source triple. -/
theorem compensated_shared_source_degree_energy_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (compensator : Color → ℝ)
    (reference : FiniteDist Color) (bodyLower bodyUpper : ℝ)
    (hlower : 0 < bodyLower) (hupper : 0 ≤ bodyUpper)
    (href : ∀ color, bodyLower ≤ reference.weight color)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ bodyUpper)
    (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => reference)
      (compensatedTripleMass compensator (BlockDensity.attachedMass source pair body)) degree) ≤
      16 * profileSquareNorm reference.weight compensator * (bodyUpper / bodyLower) *
        BlockDensity.pairEnergy reference.weight reference.weight
          (fun first second => (source.mix pair).weight (first, second)) := by
  have hrefpos (color : Color) : 0 < reference.weight color := hlower.trans_le (href color)
  have h := LocalTensors.degreeTensor_energy_le (fun _ : Fin 4 => reference)
    (fun _ color => hrefpos color)
    (compensatedTripleMass compensator (BlockDensity.attachedMass source pair body)) degree
  rw [compensated_triple_density_energy] at h
  norm_num only [Fintype.card_fin, Nat.reducePow] at h
  have ht := BlockDensity.attached_triple_energy_le source pair body reference.weight reference.weight
    reference.weight bodyLower bodyUpper hlower hupper hrefpos hrefpos href hbody
  have hnonneg : 0 ≤ profileSquareNorm reference.weight compensator :=
    Finset.sum_nonneg fun color _ => div_nonneg (sq_nonneg _) (reference.nonneg _)
  have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hnonneg)
  nlinarith only [h, hh]

end
end PhysicalBlockTensors
end AFT

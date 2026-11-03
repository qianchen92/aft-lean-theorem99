import AFT.FirstCoefficient
import AFT.PhysicalBlockTensors
import AFT.MarkedSafePair

/-! # Exact physical triple marginals and their first coefficient energy -/

namespace AFT.PhysicalBlockTensors

open scoped BigOperators Classical

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Source Color : Type*} [Fintype Source] [Fintype Color]

theorem sharedSourceTriple_first_marginal (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (color : Color) :
    ((sharedSourceTriple source pair body).map (fun word => word 0)).weight color =
      ∑ second, (source.mix pair).weight (color, second) := by
  rw [sharedSourceTriple, FiniteDist.map_map, FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue, Matrix.cons_val_zero]
  change (∑ first, ∑ second, ∑ attached, if first = color then
    BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, BlockDensity.attachedMass_marginal,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sharedSourceTriple_second_marginal (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (color : Color) :
    ((sharedSourceTriple source pair body).map (fun word => word 1)).weight color =
      ∑ first, (source.mix pair).weight (first, color) := by
  rw [sharedSourceTriple, FiniteDist.map_map, FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  change (∑ first, ∑ second, ∑ attached, if second = color then
    BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, BlockDensity.attachedMass_marginal,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sharedSourceTriple_body_marginal (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (color : Color) :
    ((sharedSourceTriple source pair body).map (fun word => word 2)).weight color =
      ∑ first, ∑ second, BlockDensity.attachedMass source pair body first second color := by
  rw [sharedSourceTriple, FiniteDist.map_map, FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_two, BlockDensity.attachedLaw]
  change (∑ first, ∑ second, ∑ attached, if attached = color then
    BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sharedSourceTriple_body_marginal_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (upper : ℝ)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ upper)
    (color : Color) :
    ((sharedSourceTriple source pair body).map (fun word => word 2)).weight color ≤ upper := by
  rw [sharedSourceTriple_body_marginal]
  calc
    _ ≤ ∑ first, ∑ second, upper * (source.mix pair).weight (first, second) :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        BlockDensity.attachedMass_upper source pair body upper hbody first second color
    _ = _ := by
      simp only [← Finset.mul_sum]
      have hm : (∑ first, ∑ second, (source.mix pair).weight (first, second)) = 1 := by
        simpa only [Fintype.sum_prod_type] using (source.mix pair).sum_one
      rw [hm, mul_one]

omit [Fintype Source] in
/-- Centering an actual marginal by its probability reference costs at most
twice its full profile energy plus two. -/
theorem centered_probability_energy_le (reference marginal : FiniteDist Color)
    (href : ∀ color, 0 < reference.weight color) :
    profileSquareNorm reference.weight (fun color => marginal.weight color - reference.weight color) ≤
      2 * profileSquareNorm reference.weight marginal.weight + 2 := by
  have hh := profileSquareNorm_sub_le_two reference.weight marginal.weight reference.weight reference.nonneg
  have hr : profileSquareNorm reference.weight reference.weight = 1 := by
    unfold profileSquareNorm
    have heq (color) : reference.weight color ^ 2 / reference.weight color = reference.weight color := by
      field_simp [(href color).ne']
    simp only [heq, reference.sum_one]
  rwa [hr, mul_one] at hh

omit [Fintype Source] in
/-- A true diffuse marginal pays only its height divided by the positive
reference floor, independently of the palette size. -/
theorem probability_energy_le_height (reference marginal : FiniteDist Color)
    (lower upper : ℝ) (hl : 0 < lower) (hu : 0 ≤ upper)
    (href : ∀ color, lower ≤ reference.weight color) (hm : ∀ color, marginal.weight color ≤ upper) :
    profileSquareNorm reference.weight marginal.weight ≤ upper / lower := by
  have h := BlockDensity.profile_energy_le_ratio reference.weight marginal.weight (upper / lower)
    (fun color => hl.trans_le (href color)) marginal.nonneg (fun color => (hm color).trans (by
      have hh := mul_le_mul_of_nonneg_left (href color) (div_nonneg hu hl.le)
      have he : (upper / lower) * lower = upper := by field_simp
      rwa [he] at hh))
  rwa [marginal.sum_one, mul_one] at h

omit [Fintype Source] in
/-- A sharp primary-square estimate survives an added diffuse marginal.
The primary height is never substituted for its counting square. -/
theorem probability_energy_le_primary_square (reference marginal : FiniteDist Color)
    (primary : Color → ℝ) (scale constant lower : ℝ)
    (hs : 0 ≤ scale) (hc : 0 ≤ constant) (hl : 0 < lower)
    (hp : ∀ color, 0 ≤ primary color) (href : ∀ color, lower ≤ reference.weight color)
    (hm : ∀ color, marginal.weight color ≤ scale * primary color + constant) :
    profileSquareNorm reference.weight marginal.weight ≤
      (2 / lower) * (scale ^ 2 * (∑ color, primary color ^ 2) + Fintype.card Color * constant ^ 2) := by
  calc
    _ ≤ ∑ color, (2 * (scale * primary color) ^ 2 + 2 * constant ^ 2) / lower := by
      apply Finset.sum_le_sum
      intro color _
      have hbound : marginal.weight color ^ 2 ≤ 2 * (scale * primary color) ^ 2 + 2 * constant ^ 2 := by
        have hsq := (sq_le_sq₀ (marginal.nonneg color) (add_nonneg (mul_nonneg hs (hp color)) hc)).mpr (hm color)
        nlinarith [sq_nonneg (scale * primary color - constant)]
      exact (div_le_div_of_nonneg_left (sq_nonneg _) hl (href color)).trans
        (div_le_div_of_nonneg_right hbound hl.le)
    _ = _ := by
      simp only [mul_pow, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

end

end AFT.PhysicalBlockTensors

import CurrentAFT.ActualCalibrationIteration

/-! # Polynomial coordinate bounds in the actual calibrated norm

The coordinate condition number is derived from the genuine reference atoms
and population weights. No inverse-atom or coordinate-norm oracle is assumed.
-/
namespace CurrentAFT.ActualCoordinateBounds
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundRates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem point_l2_bound {State : Type*} [Fintype State] (reference : FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (hbound : 1 ≤ bound)
    (point : State) (hatom : 1 ≤ bound * reference.weight point) :
    |test point| ≤ bound * Real.sqrt (reference.l2Sq test) := by
  have he : 0 ≤ reference.l2Sq test := FiniteDist.l2Sq_nonneg _ _
  have hp : reference.weight point * test point ^ 2 ≤ reference.l2Sq test :=
    Finset.single_le_sum (fun value _ => mul_nonneg (reference.nonneg value) (sq_nonneg _))
      (Finset.mem_univ point)
  have hs : test point ^ 2 ≤ bound * reference.l2Sq test := by
    have hfirst := mul_le_mul_of_nonneg_right hatom (sq_nonneg (test point))
    have hsecond := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ bound)
    nlinarith only [hfirst, hsecond]
  have hbb : bound ≤ bound ^ 2 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_right hbb he
  have hsqrt := Real.sq_sqrt he
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hsqrt]
  exact hs.trans hlarge

theorem block_point_bound {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (bound : ℝ) (hbound : 1 ≤ bound)
    (hp : ∀ color, 1 ≤ bound * primary.weight color) (hb : ∀ color, 1 ≤ bound * body.weight color)
    {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    |kernel colors centers| ≤ bound ^ (r + s) * blockL2 primary body kernel := by
  let reference := (FiniteDist.independent (fun _ : Fin r => primary)).prod
    (FiniteDist.independent (fun _ : Fin s => body))
  have hatom : 1 ≤ bound ^ (r + s) * reference.weight (colors, centers) := by
    have hfirst : (1 : ℝ) ≤ ∏ index : Fin r, bound * primary.weight (colors index) :=
      Finset.one_le_prod _ (fun index => hp (colors index))
    have hsecond : (1 : ℝ) ≤ ∏ index : Fin s, bound * body.weight (centers index) :=
      Finset.one_le_prod _ (fun index => hb (centers index))
    have hprod := one_le_mul_of_one_le_of_one_le hfirst hsecond
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    change 1 ≤ bound ^ (r + s) * ((∏ index, primary.weight (colors index)) *
      ∏ index, body.weight (centers index))
    convert hprod using 1
    rw [pow_add]
    ring
  exact point_l2_bound reference (fun pair => kernel pair.1 pair.2) _
    (one_le_pow₀ hbound) (colors, centers) hatom

theorem current_block_point (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualControls.Palette security) (Body := SafePalette security) r s)
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    |kernel colors centers| ≤ (2 * (Parameters.modulus security : ℝ)) ^ (r + s) *
      blockL2 (primaryLaw security) (bodyReference security) kernel := by
  have hq := FirstResponse.modulus_pos security
  have hq1 : (1 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  apply block_point_bound _ _ _ (by linarith)
  · intro color
    have h := primaryProfile_atom_lower security color
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm
  · intro color
    have hm := mul_le_mul_of_nonneg_left (bodyReference_lower security color)
      (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ))
    simpa only [mul_one_div_cancel (by positivity : (2 * (Parameters.modulus security : ℝ)) ≠ 0)] using hm

theorem dimension_ge_one (security : ℕ) : (1 : ℝ) ≤ Parameters.dimension security := by
  have h := (Parameters.dimension_bounds security).1
  have hp := pow_pos (Parameters.base_pos security) 160
  exact_mod_cast (show 1 ≤ Parameters.dimension security by omega)

theorem dimension_primaryFactor (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * primaryFactor security := by
  have hd := dimension_ge_one security
  have hl : (Parameters.legCount security : ℝ) ≤ Parameters.dimension security := by
    exact_mod_cast (show Parameters.legCount security ≤ Parameters.dimension security by
      unfold Parameters.dimension; omega)
  have hlpos : (0 : ℝ) < Parameters.legCount security := by
    have h : 0 < Parameters.legCount security := by
      unfold Parameters.legCount Parameters.scale
      exact pow_pos (pow_pos (Parameters.base_pos security) _) _
    exact_mod_cast h
  have hsqrt : Real.sqrt (Parameters.legCount security : ℝ) ≤ Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold primaryFactor
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hlpos), one_mul]
  exact hsqrt

theorem dimension_bodyFactor (security : ℕ) :
    1 ≤ (Parameters.dimension security : ℝ) * bodyFactor security := by
  have hd := dimension_ge_one security
  have hp : (0 : ℝ) < ordinaryPool security := by exact_mod_cast ordinaryPool_pos security
  have hpool : (ordinaryPool security : ℝ) ≤ Parameters.dimension security := by
    exact_mod_cast (show ordinaryPool security ≤ Parameters.dimension security by
      unfold ordinaryPool Parameters.dimension; omega)
  have hr : (1 : ℝ) ≤ radius security := by
    apply Real.one_le_rpow
    · exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
    · norm_num
  have hsqrt : Real.sqrt (ordinaryPool security : ℝ) ≤ Parameters.dimension security := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  unfold bodyFactor
  rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hp), one_mul]
  exact hsqrt.trans (le_mul_of_one_le_right (by linarith) hr)

theorem family_point_bound (security order : ℕ) (family : Family security order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(family arity).val colors centers| ≤
      (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order *
        LocalRaisingBounds.coefficientNorm security order family := by
  have hd := dimension_ge_one security
  have hp := (RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (RaisingPatternBudget.bodyFactor_pos security).le
  have hn := familyNorm_nonneg (primaryLaw security) (bodyReference security) order _ _ hp hb family
  have hweight : 1 ≤ (Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
      gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val := by
    have h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (dimension_primaryFactor security) (n := arity.val.1.val))
      (one_le_pow₀ (dimension_bodyFactor security) (n := arity.val.2.val))
    simpa only [gradeWeight, mul_pow, pow_add, mul_mul_mul_comm] using h
  have hsingle : gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
      blockL2 (primaryLaw security) (bodyReference security) (family arity).val ≤
        LocalRaisingBounds.coefficientNorm security order family := by
    unfold LocalRaisingBounds.coefficientNorm familyNorm
    exact Finset.single_le_sum (fun index _ => mul_nonneg
      (gradeWeight_nonneg _ _ hp hb index.val.1.val index.val.2.val)
      (blockL2_nonneg (primaryLaw security) (bodyReference security) (family index).val))
      (Finset.mem_univ arity)
  have hblock : blockL2 (primaryLaw security) (bodyReference security) (family arity).val ≤
      (Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
        LocalRaisingBounds.coefficientNorm security order family := by
    have hfirst := mul_le_mul_of_nonneg_right hweight (blockL2_nonneg (primaryLaw security) (bodyReference security) (family arity).val)
    have hsecond := mul_le_mul_of_nonneg_left hsingle
      (pow_nonneg (by linarith : (0 : ℝ) ≤ Parameters.dimension security) (arity.val.1.val + arity.val.2.val))
    nlinarith only [hfirst, hsecond]
  have hq : (1 : ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  have hlarge : (1 : ℝ) ≤ 2 * (Parameters.modulus security : ℝ) * Parameters.dimension security := by nlinarith
  calc
    _ ≤ (2 * (Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        blockL2 (primaryLaw security) (bodyReference security) (family arity).val := current_block_point security _ _ _ _ _
    _ ≤ (2 * (Parameters.modulus security : ℝ))^(arity.val.1.val + arity.val.2.val) *
        ((Parameters.dimension security : ℝ)^(arity.val.1.val + arity.val.2.val) *
          LocalRaisingBounds.coefficientNorm security order family) := mul_le_mul_of_nonneg_left hblock (by positivity)
    _ = (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^(arity.val.1.val + arity.val.2.val) *
        LocalRaisingBounds.coefficientNorm security order family := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlarge arity.property) hn

theorem coordinate_factor_polynomial (security order : ℕ) :
    (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order ≤
      (2 * 131072 * 131074 : ℝ)^order * (Parameters.base security : ℝ)^(224 * order) := by
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hd : (Parameters.dimension security : ℝ) ≤ 131074 * (Parameters.base security : ℝ)^160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  have hprod := mul_le_mul hq hd (Nat.cast_nonneg _) (by positivity :
    (0 : ℝ) ≤ 131072 * (Parameters.base security : ℝ)^64)
  have hbound : 2 * (Parameters.modulus security : ℝ) * Parameters.dimension security ≤
      (2 * 131072 * 131074 : ℝ) * (Parameters.base security : ℝ)^224 := by
    have h := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    2 * (Parameters.modulus security : ℝ) * Parameters.dimension security) hbound order
  simpa only [mul_pow, ← pow_mul] using h

theorem iteration_point_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualCompleteStability.threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (count : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → ActualControls.Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |((ActualCalibrationIteration.iterate security order horder hsecurity layout count) arity).val colors centers -
      ((ActualCompleteStability.solution security order horder hsecurity layout) arity).val colors centers| ≤
        2 * (2 * 131072 * 131074 : ℝ)^order * (Parameters.base security : ℝ)^(224 * order) * (1 / 2 : ℝ)^count := by
  have hpoint := family_point_bound security order
    (ActualCalibrationIteration.iterate security order horder hsecurity layout count -
      ActualCompleteStability.solution security order horder hsecurity layout) arity colors centers
  apply hpoint.trans
  have hnorm := ActualCalibrationIteration.iterate_error security order horder hsecurity layout count
  have hf := coordinate_factor_polynomial security order
  exact (mul_le_mul hf hnorm
    (familyNorm_nonneg _ _ _ _ _ (RaisingPatternBudget.primaryFactor_pos security).le
      (RaisingPatternBudget.bodyFactor_pos security).le _) (by positivity)).trans_eq (by ring)

end
end CurrentAFT.ActualCoordinateBounds

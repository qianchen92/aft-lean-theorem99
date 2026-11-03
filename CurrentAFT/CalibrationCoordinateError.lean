import CurrentAFT.CalibrationPointCoordinates

/-! # Error propagation for finite calibration tables

Uniform errors in the complete point table are converted to the actual
graded coefficient norm using the proved reference atom bounds. No coordinate
condition number is supplied as an assumption for the current construction.
-/
namespace CurrentAFT.CalibrationCoordinateError
open AFT ControlCoordinates ControlProduct ControlNorm CanonicalReconstruction
  GradedControlAlgebra GradedControlNorm CalibrationPointCoordinates
  ActualControls ProposalPrimary BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem expectation_abs_bound {State : Type*} [Fintype State]
    (law : FiniteDist State) (value : State → ℝ) (bound : ℝ)
    (hbound : ∀ state, |value state| ≤ bound) : |law.expectation value| ≤ bound := by
  unfold FiniteDist.expectation
  calc
    _ ≤ ∑ state, |law.weight state * value state| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, law.weight state * bound := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (law.nonneg state)]
      exact mul_le_mul_of_nonneg_left (hbound state) (law.nonneg state)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem centeredAtom_bound {State : Type*} [Fintype State] (law : FiniteDist State)
    (bound : ℝ) (hbound : 0 ≤ bound) (hinverse : ∀ state, (law.weight state)⁻¹ ≤ bound)
    (source output : State) : |Hoeffding.centeredAtom law source output| ≤ bound + 1 := by
  unfold Hoeffding.centeredAtom
  split_ifs
  · exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (inv_nonneg.mpr (law.nonneg output)), abs_one]
      linarith [hinverse output])
  · simpa using hbound

theorem pointTensor_bound (primary : FiniteDist Primary) (body : FiniteDist Body)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hp : ∀ color, (primary.weight color)⁻¹ ≤ bound)
    (hb : ∀ color, (body.weight color)⁻¹ ≤ bound)
    {r s : ℕ} (sourcePrimary colors : Fin r → Primary) (sourceBody centers : Fin s → Body) :
    |pointTensor primary body sourcePrimary sourceBody colors centers| ≤ (bound + 1)^(r + s) := by
  simp only [pointTensor, abs_mul, Finset.abs_prod]
  rw [pow_add]
  apply mul_le_mul
  · simpa using (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun index (_ : index ∈ (Finset.univ : Finset (Fin r))) =>
        centeredAtom_bound primary bound hbound hp (sourcePrimary index) (colors index)))
  · simpa using (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun index (_ : index ∈ (Finset.univ : Finset (Fin s))) =>
        centeredAtom_bound body bound hbound hb (sourceBody index) (centers index)))
  · exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  · positivity

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_bound {r s : ℕ}
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s) (bound : ℝ)
    (hbound : ∀ colors centers, |kernel colors centers| ≤ bound)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    |symmetrize kernel colors centers| ≤ bound := by
  have haverage : |(FiniteDist.uniform (Equiv.Perm (Fin r))).expectation (fun first =>
    (FiniteDist.uniform (Equiv.Perm (Fin s))).expectation (fun second =>
      kernel (colors ∘ first) (centers ∘ second)))| ≤ bound := by
    apply expectation_abs_bound
    intro first
    apply expectation_abs_bound
    intro second
    exact hbound _ _
  simpa only [FiniteDist.expectation, ControlProduct.symmetrize, reindexKernel, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using haverage

theorem pointKernel_bound (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hip : ∀ color, (primary.weight color)⁻¹ ≤ bound)
    (hib : ∀ color, (body.weight color)⁻¹ ≤ bound)
    {r s : ℕ} (sourcePrimary colors : Fin r → Primary) (sourceBody centers : Fin s → Body) :
    |(pointKernel primary body hp hb sourcePrimary sourceBody).val colors centers| ≤ (bound + 1)^(r + s) :=
  symmetrize_bound _ _ (fun _ _ => pointTensor_bound primary body bound hbound hip hib _ _ _ _) colors centers

theorem decode_point_bound (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hip : ∀ color, (primary.weight color)⁻¹ ≤ bound)
    (hib : ∀ color, (body.weight color)⁻¹ ≤ bound)
    (order : ℕ) (table : PointTable Primary Body order) (error : ℝ)
    (herror : 0 ≤ error) (htable : ∀ point, |table point| ≤ error)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary)
    (centers : Fin arity.val.2.val → Body) :
    |(decode primary body hp hb order table arity).val colors centers| ≤ (bound + 1)^order * error := by
  let source := (FiniteDist.independent (fun _ : Fin arity.val.1.val => primary)).prod
    (FiniteDist.independent (fun _ : Fin arity.val.2.val => body))
  have he : (decode primary body hp hb order table arity).val colors centers =
      source.expectation (fun point => table ⟨arity, point⟩ *
        (pointKernel primary body hp hb point.1 point.2).val colors centers) := by
    simp only [decode, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FiniteDist.expectation,
      Fintype.sum_prod_type, source, FiniteDist.prod_weight, FiniteDist.independent]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [he]
  apply expectation_abs_bound
  intro point
  rw [abs_mul]
  calc
    _ ≤ error * (bound + 1)^(arity.val.1.val + arity.val.2.val) :=
      mul_le_mul (htable ⟨arity, point⟩)
        (pointKernel_bound primary body hp hb bound hbound hip hib _ _ _ _) (abs_nonneg _) herror
    _ ≤ error * (bound + 1)^order :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) arity.property) herror
    _ = _ := mul_comm _ _

theorem blockL2_of_point_bound {r s : ℕ} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (bound : ℝ) (hbound : 0 ≤ bound) (hkernel : ∀ colors centers, |kernel colors centers| ≤ bound) :
    blockL2 primary body kernel ≤ bound := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hbound, ?_⟩
  let reference := (FiniteDist.independent (fun _ : Fin r => primary)).prod
    (FiniteDist.independent (fun _ : Fin s => body))
  change (∑ point, reference.weight point * kernel point.1 point.2 ^ 2) ≤ bound^2
  calc
    _ ≤ ∑ point, reference.weight point * bound^2 := by
      apply Finset.sum_le_sum
      intro point _
      apply mul_le_mul_of_nonneg_left _ (reference.nonneg point)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hbound).mpr (hkernel point.1 point.2)
    _ = _ := by rw [← Finset.sum_mul, reference.sum_one, one_mul]

theorem decode_norm_bound (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hip : ∀ color, (primary.weight color)⁻¹ ≤ bound)
    (hib : ∀ color, (body.weight color)⁻¹ ≤ bound)
    (primaryFactor bodyFactor : ℝ) (hpf : 0 ≤ primaryFactor) (hbf : 0 ≤ bodyFactor)
    (hpf1 : primaryFactor ≤ 1) (hbf1 : bodyFactor ≤ 1)
    (order : ℕ) (table : PointTable Primary Body order) (error : ℝ)
    (herror : 0 ≤ error) (htable : ∀ point, |table point| ≤ error) :
    familyNorm primary body order primaryFactor bodyFactor (decode primary body hp hb order table) ≤
      (order + 1 : ℕ)^2 * ((bound + 1)^order * error) := by
  let value := (bound + 1)^order * error
  have hv : 0 ≤ value := mul_nonneg (pow_nonneg (by linarith) _) herror
  have hl2 (arity : TruncatedArity order) :
      blockL2 primary body (decode primary body hp hb order table arity).val ≤ value :=
    blockL2_of_point_bound primary body _ value hv
      (decode_point_bound primary body hp hb bound hbound hip hib order table error herror htable arity)
  have hcard : Fintype.card (TruncatedArity order) ≤ (order + 1)^2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      (Fintype.card_subtype_le (fun arity : Fin (order + 1) × Fin (order + 1) =>
        arity.1.val + arity.2.val ≤ order))
  unfold familyNorm
  calc
    _ ≤ ∑ _arity : TruncatedArity order, value := by
      apply Finset.sum_le_sum
      intro arity _
      have hw : gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val ≤ 1 :=
        mul_le_one₀ (pow_le_one₀ hpf hpf1) (pow_nonneg hbf _) (pow_le_one₀ hbf hbf1)
      exact (mul_le_mul hw (hl2 arity) (blockL2_nonneg _ _ _)
        (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul value)
    _ = (Fintype.card (TruncatedArity order) : ℝ) * value := by simp
    _ ≤ (order + 1 : ℕ)^2 * value := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hv

theorem current_inverse_atom (security : ℕ) :
    (∀ color, ((primaryLaw security).weight color)⁻¹ ≤ 2 * (Parameters.modulus security : ℝ)) ∧
    (∀ color, ((bodyReference security).weight color)⁻¹ ≤ 2 * (Parameters.modulus security : ℝ)) := by
  have hq : (0 : ℝ) < 2 * Parameters.modulus security := by
    have := FirstResponse.modulus_pos security
    positivity
  constructor
  · intro color
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (primaryReference_positive security color)).mpr
    have h := mul_le_mul_of_nonneg_left (primaryProfile_atom_lower security color) hq.le
    rw [mul_one_div_cancel hq.ne'] at h
    simpa only [primaryLaw, mul_comm] using h
  · intro color
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (bodyReference_positive security color)).mpr
    have h := mul_le_mul_of_nonneg_left (bodyReference_lower security color) hq.le
    rw [mul_one_div_cancel hq.ne'] at h
    simpa only [mul_comm] using h

theorem current_decode_error (security order : ℕ)
    (table : PointTable (ActualControls.Palette security) (SafePalette security) order)
    (error : ℝ) (herror : 0 ≤ error) (htable : ∀ point, |table point| ≤ error) :
    LocalRaisingBounds.coefficientNorm security order
      (decode (primaryLaw security) (bodyReference security) (primaryReference_positive security)
        (bodyReference_positive security) order table) ≤
      (order + 1 : ℕ)^2 * ((2 * (Parameters.modulus security : ℝ) + 1)^order * error) := by
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast
    (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpf : primaryFactor security ≤ 1 := by
    rw [primaryFactor_eq]
    exact (div_le_one (pow_pos (FirstResponse.base_pos security) _)).mpr (one_le_pow₀ hb1)
  have hbf : bodyFactor security ≤ 1 := (bodyFactor_le security).trans
    ((div_le_one (pow_pos (FirstResponse.base_pos security) _)).mpr (one_le_pow₀ hb1))
  exact decode_norm_bound _ _ (primaryReference_positive security) (bodyReference_positive security)
    _ (by positivity) (current_inverse_atom security).1 (current_inverse_atom security).2
    _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le hpf hbf order table error herror htable

theorem current_decode_polynomial_error (security order : ℕ)
    (table : PointTable (ActualControls.Palette security) (SafePalette security) order)
    (error : ℝ) (herror : 0 ≤ error) (htable : ∀ point, |table point| ≤ error) :
    LocalRaisingBounds.coefficientNorm security order
      (decode (primaryLaw security) (bodyReference security) (primaryReference_positive security)
        (bodyReference_positive security) order table) ≤
      (((order + 1 : ℕ)^2 : ℝ) * (3 * 131072)^order) *
        (Parameters.base security : ℝ)^(64 * order) * error := by
  have hq1 : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.one_le
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  apply (current_decode_error security order table error herror htable).trans
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ) + 1)
    (by linarith : 2 * (Parameters.modulus security : ℝ) + 1 ≤ 3 * 131072 * (Parameters.base security : ℝ)^64) order
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h herror)
    (show (0 : ℝ) ≤ (order + 1 : ℕ)^2 by positivity)
  convert hh using 1
  simp only [mul_pow, ← pow_mul]
  ring

end
end CurrentAFT.CalibrationCoordinateError

import CurrentAFT.RationalDensityInverseProgram

/-! # Explicit rational primary tensor inverse on full joint arrays

The program enumerates the current palette in each retained coordinate.
It applies the actual normalized first inverse in every coordinate, without
factoring the input tensor or querying a real inverse.
-/
namespace CurrentAFT.RationalTensorInverseProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def entry (security bits source output : ℕ) : ℚ :=
  RationalDensityInverseProgram.current security bits (fun color => if color = source then 1 else 0) output

def current (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ) (output : Fin degree → ℕ) : ℚ :=
  ∑ source : Fin degree → Fin (PublicParameterProgram.modulus security).count,
    input (fun index => (source index).val) *
      ∏ index, entry security bits (source index).val (output index)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def actualBound (security : ℕ) : ℝ :=
  8 * (Parameters.base security : ℝ) * Parameters.modulus security *
    RationalDensityInverseProgram.inverseBound security

theorem actualBound_nonneg (security : ℕ) : 0 ≤ actualBound security := by
  unfold actualBound RationalDensityInverseProgram.inverseBound
  positivity

theorem errorConstant_nonneg (security : ℕ) : 0 ≤ RationalDensityInverseProgram.errorConstant security := by
  unfold RationalDensityInverseProgram.errorConstant RationalDensityInverseProgram.inverseBound
    RationalFirstResponseProgram.inverseErrorConstant
  positivity

theorem actual_inverse_bound (security : ℕ) (input : Palette security → ℝ) (bound : ℝ)
    (hb : 0 ≤ bound) (hinput : ∀ color, |input color| ≤ bound) (output : Palette security) :
    |PrimaryTensorInverse.densityInverse security input output| ≤ actualBound security * bound := by
  let profile := fun color : Palette security => (primaryLaw security).weight color * input color
  have hprofile (color : Palette security) : |profile color| ≤ bound := by
    dsimp only [profile]
    rw [abs_mul, abs_of_nonneg ((primaryLaw security).nonneg color)]
    exact (mul_le_mul ((primaryLaw security).atom_le_one color) (hinput color) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnum := RationalDensityInverseProgram.actual_inverse_bound security profile bound hb hprofile output
  have hb0 := FirstResponse.base_pos security
  have hq0 := FirstResponse.modulus_pos security
  have hp : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight output := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security output
  have hden : 1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security) ≤
      activation security * (primaryLaw security).weight output := by
    calc
      _ = (1 / (4 * (Parameters.base security : ℝ))) * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
      _ ≤ _ := mul_le_mul (FirstResponse.activation_lower_simple security) hp (by positivity) (activation_pos security).le
  have hdenpos : 0 < activation security * (primaryLaw security).weight output :=
    mul_pos (activation_pos security) (primaryReference_positive security output)
  have hformula : PrimaryTensorInverse.densityInverse security input output =
      (FirstResponse.responseEquiv security).symm profile output /
        (activation security * (primaryLaw security).weight output) := by
    rw [PrimaryTensorInverse.densityInverse_apply]
    dsimp only [profile]
    ring
  rw [hformula, abs_div, abs_of_pos hdenpos]
  calc
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
        (activation security * (primaryLaw security).weight output) :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (RationalDensityInverseProgram.inverseBound security * bound) /
        (1 / (8 * (Parameters.base security : ℝ) * Parameters.modulus security)) :=
      div_le_div_of_nonneg_left (by unfold RationalDensityInverseProgram.inverseBound; positivity)
        (by positivity) hden
    _ = _ := by unfold actualBound; ring_nf; simp only [inv_inv]

theorem entry_error (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ) -
      PrimaryTensorInverse.densityInverse security (Pi.single source 1) output| ≤
        RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits) := by
  have hsingle : (fun color : Palette security =>
      ((if color.val = source.val then 1 else 0 : ℚ) : ℝ)) = Pi.single source 1 := by
    funext color
    by_cases hequal : color = source
    · subst color; simp
    · have hne : color.val ≠ source.val := fun h => hequal (Fin.ext h)
      simp [hne, hequal]
  have h := RationalDensityInverseProgram.current_error security bits
    (fun color => if color = source.val then 1 else 0) output 1 (by norm_num)
    (fun color => by dsimp only; split_ifs <;> norm_num) hfirst hprecision hbudget
  dsimp only at h
  rw [hsingle] at h
  simpa only [entry, mul_one, div_eq_mul_inv, one_div, one_mul] using h

def factorBound (security : ℕ) : ℝ :=
  1 + actualBound security + RationalDensityInverseProgram.errorConstant security

theorem factorBound_one_le (security : ℕ) : 1 ≤ factorBound security := by
  unfold factorBound
  linarith [actualBound_nonneg security, errorConstant_nonneg security]

theorem entry_bounds (security bits : ℕ) (source output : Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(entry security bits source.val output.val : ℝ)| ≤ factorBound security ∧
    |PrimaryTensorInverse.densityInverse security (Pi.single source 1) output| ≤ factorBound security := by
  have he := entry_error security bits source output hfirst hprecision hbudget
  have ht := actual_inverse_bound security (Pi.single source 1) 1 (by norm_num)
    (fun color => by simp only [Pi.single_apply]; split_ifs <;> norm_num) output
  simp only [mul_one] at ht
  have heps : 1 / (2 : ℝ)^bits ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^bits)).mpr
    simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^bits)
  have htri := abs_add_le
    ((entry security bits source.val output.val : ℝ) - PrimaryTensorInverse.densityInverse security (Pi.single source 1) output)
    (PrimaryTensorInverse.densityInverse security (Pi.single source 1) output)
  rw [sub_add_cancel] at htri
  have hsmall := mul_le_mul_of_nonneg_left heps (errorConstant_nonneg security)
  unfold factorBound
  constructor <;> linarith [actualBound_nonneg security, errorConstant_nonneg security]

theorem product_difference_bound {Index : Type*} [DecidableEq Index]
    (set : Finset Index) (first second : Index → ℝ) (bound error : ℝ)
    (hb : 1 ≤ bound) (he : 0 ≤ error)
    (hfirst : ∀ index ∈ set, |first index| ≤ bound)
    (hsecond : ∀ index ∈ set, |second index| ≤ bound)
    (hdiff : ∀ index ∈ set, |first index - second index| ≤ error) :
    |(∏ index ∈ set, first index) - ∏ index ∈ set, second index| ≤
      (set.card : ℝ) * error * bound^set.card := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hnot ih =>
    have hfirst' := fun other hmem => hfirst other (Finset.mem_insert_of_mem hmem)
    have hsecond' := fun other hmem => hsecond other (Finset.mem_insert_of_mem hmem)
    have hdiff' := fun other hmem => hdiff other (Finset.mem_insert_of_mem hmem)
    have hprod : |∏ other ∈ set, second other| ≤ bound^set.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _other ∈ set, bound := Finset.prod_le_prod (fun other _ => abs_nonneg _) hsecond'
        _ = _ := by rw [Finset.prod_const]
    have hi := ih hfirst' hsecond' hdiff'
    simp only [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
    calc
      _ = |first index * ((∏ other ∈ set, first other) - ∏ other ∈ set, second other) +
        (first index - second index) * ∏ other ∈ set, second other| := by congr 1; ring
      _ ≤ |first index| * |(∏ other ∈ set, first other) - ∏ other ∈ set, second other| +
          |first index - second index| * |∏ other ∈ set, second other| := by
        simpa only [abs_mul] using abs_add_le
          (first index * ((∏ other ∈ set, first other) - ∏ other ∈ set, second other))
          ((first index - second index) * ∏ other ∈ set, second other)
      _ ≤ bound * ((set.card : ℝ) * error * bound^set.card) + error * bound^set.card :=
        add_le_add (mul_le_mul (hfirst index (Finset.mem_insert_self ..)) hi (abs_nonneg _) (by positivity))
          (mul_le_mul (hdiff index (Finset.mem_insert_self ..)) hprod (abs_nonneg _) he)
      _ ≤ _ := by
        rw [pow_succ]
        have hpow : 0 ≤ bound^set.card := pow_nonneg (by linarith) _
        nlinarith [mul_nonneg he hpow, mul_nonneg (mul_nonneg he hpow) (sub_nonneg.mpr hb)]

theorem current_cast (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ)
    (output : Fin degree → Palette security) :
    (current security bits degree input (fun index => (output index).val) : ℝ) =
      ∑ source : Fin degree → Palette security, (input (fun index => (source index).val) : ℝ) *
        ∏ index, (entry security bits (source index).val (output index).val : ℝ) := by
  unfold current
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod]
  apply Finset.sum_congr (by ext; simp)
  intro source _
  rfl

def tensorErrorConstant (security degree : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ)^degree * degree * RationalDensityInverseProgram.errorConstant security *
    (factorBound security)^degree

/-- The bound applies to every joint input array, including root-retained
arrays. No decomposition into tensor products is assumed. -/
theorem current_error (security bits degree : ℕ) (input : (Fin degree → ℕ) → ℚ)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hinput : ∀ source : Fin degree → Palette security, |(input (fun index => (source index).val) : ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin degree → Palette security) :
    |(current security bits degree input (fun index => (output index).val) : ℝ) -
      PrimaryTensorInverse.tensorInverse security degree
        (fun source => (input (fun index => (source index).val) : ℝ)) output| ≤
          tensorErrorConstant security degree * bound * (1 / (2 : ℝ)^bits) := by
  rw [current_cast]
  change |(∑ source : Fin degree → Palette security, _) -
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security)
      (fun source => (input (fun index => (source index).val) : ℝ)) output| ≤ _
  rw [TensorChannel.apply_formula_instance, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin degree → Palette security,
        bound * ((degree : ℝ) * (RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits)) *
          (factorBound security)^degree) := by
      apply Finset.sum_le_sum
      intro source _
      rw [← mul_sub, abs_mul]
      have hprod := product_difference_bound Finset.univ
        (fun index : Fin degree => (entry security bits (source index).val (output index).val : ℝ))
        (fun index => PrimaryTensorInverse.densityInverse security (Pi.single (source index) 1) (output index))
        (factorBound security) (RationalDensityInverseProgram.errorConstant security * (1 / (2 : ℝ)^bits))
        (factorBound_one_le security) (by positivity [errorConstant_nonneg security])
        (fun index _ => (entry_bounds security bits _ _ hfirst hprecision hbudget).1)
        (fun index _ => (entry_bounds security bits _ _ hfirst hprecision hbudget).2)
        (fun index _ => entry_error security bits _ _ hfirst hprecision hbudget)
      simp only [Finset.card_univ, Fintype.card_fin] at hprod
      exact mul_le_mul (hinput source) hprod (abs_nonneg _) hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      unfold tensorErrorConstant
      push_cast
      ring

theorem actual_tensor_difference (security degree : ℕ)
    (first second : (Fin degree → Palette security) → ℝ) (error : ℝ)
    (he : 0 ≤ error) (hdiff : ∀ source, |first source - second source| ≤ error)
    (output : Fin degree → Palette security) :
    |PrimaryTensorInverse.tensorInverse security degree first output -
      PrimaryTensorInverse.tensorInverse security degree second output| ≤
        (Parameters.modulus security : ℝ)^degree * (actualBound security)^degree * error := by
  change |TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) first output -
    TensorChannel.apply degree (fun _ => PrimaryTensorInverse.densityInverse security) second output| ≤ _
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _source : Fin degree → Palette security, error * (actualBound security)^degree := by
      apply Finset.sum_le_sum
      intro source _
      rw [← sub_mul, abs_mul]
      apply mul_le_mul (hdiff source) _ (abs_nonneg _) he
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _index : Fin degree, actualBound security :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ => by
            simpa only [mul_one] using actual_inverse_bound security (Pi.single (source index) 1) 1
              (by norm_num) (fun color => by simp only [Pi.single_apply]; split_ifs <;> norm_num) (output index))
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

end
end CurrentAFT.RationalTensorInverseProgram

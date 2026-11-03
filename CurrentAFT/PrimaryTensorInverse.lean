import CurrentAFT.PrimaryPairInverse
import AFT.TensorChannelFormula
import AFT.TensorMatrixCanonical

/-!
# Actual normalized primary inverse on arbitrary joint finite tensors

The local channel is the constructed first inverse conjugated by the actual
positive primary reference. Tensorization acts on the full joint array.
-/

namespace CurrentAFT.PrimaryTensorInverse

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryPairInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw FirstResponse.responseEquiv

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def diagonal {Color : Type*} (weight : Color → ℝ) : (Color → ℝ) →ₗ[ℝ] (Color → ℝ) where
  toFun kernel := fun color => weight color * kernel color
  map_add' first second := by funext color; simp only [Pi.add_apply]; ring
  map_smul' scalar kernel := by funext color; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def densityInverse (security : ℕ) : (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    (((activation security)⁻¹ • (responseEquiv security).symm.toLinearMap).comp
      (diagonal (primaryLaw security).weight))

def densityResponse (security : ℕ) : (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    ((activation security • response security).comp (diagonal (primaryLaw security).weight))

theorem densityInverse_apply (security : ℕ) (kernel : ActualControls.Palette security → ℝ)
    (output : ActualControls.Palette security) :
    densityInverse security kernel output =
      (activation security)⁻¹ * (responseEquiv security).symm
        (fun input => (primaryLaw security).weight input * kernel input) output /
        (primaryLaw security).weight output := by
  simp only [densityInverse, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    diagonal, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  ring

theorem densityResponse_apply (security : ℕ) (kernel : ActualControls.Palette security → ℝ)
    (output : ActualControls.Palette security) :
    densityResponse security kernel output =
      activation security * response security
        (fun input => (primaryLaw security).weight input * kernel input) output /
        (primaryLaw security).weight output := by
  simp only [densityResponse, LinearMap.comp_apply, LinearMap.smul_apply,
    diagonal, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  ring

theorem densityResponse_inverse (security : ℕ) (kernel : ActualControls.Palette security → ℝ) :
    densityResponse security (densityInverse security kernel) = kernel := by
  have ha := (activation_pos security).ne'
  have hprofile : (fun input => (primaryLaw security).weight input * densityInverse security kernel input) =
      (activation security)⁻¹ • (responseEquiv security).symm
        (fun input => (primaryLaw security).weight input * kernel input) := by
    funext input
    rw [densityInverse_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(primaryReference_positive security input).ne']
  funext output
  rw [densityResponse_apply, hprofile, map_smul]
  have hinverse : response security ((responseEquiv security).symm
      (fun input => (primaryLaw security).weight input * kernel input)) =
        fun input => (primaryLaw security).weight input * kernel input := by
    rw [← responseEquiv_forward]
    exact (responseEquiv security).apply_symm_apply _
  rw [hinverse]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(primaryReference_positive security output).ne']

theorem densityInverse_mean (security : ℕ) (kernel : ActualControls.Palette security → ℝ) :
    (primaryLaw security).expectation (densityInverse security kernel) =
      (activation security)⁻¹ * (primaryLaw security).expectation kernel := by
  have hpoint (color : ActualControls.Palette security) :
      (primaryLaw security).weight color * densityInverse security kernel color =
        (activation security)⁻¹ * (responseEquiv security).symm
          (fun input => (primaryLaw security).weight input * kernel input) color := by
    rw [densityInverse_apply]
    field_simp [(primaryReference_positive security color).ne']
  simp only [FiniteDist.expectation, hpoint, ← Finset.mul_sum, response_inverse_preserves_mass]

theorem densityInverse_energy (security : ℕ) (kernel : ActualControls.Palette security → ℝ) :
    (primaryLaw security).l2Sq (densityInverse security kernel) ≤
      (2 / activation security) ^ 2 * (primaryLaw security).l2Sq kernel := by
  have hpoint (color : ActualControls.Palette security) :
      (primaryLaw security).weight color * densityInverse security kernel color ^ 2 =
        (activation security)⁻¹ ^ 2 *
          ((responseEquiv security).symm (fun input => (primaryLaw security).weight input * kernel input) color ^ 2 /
            (primaryLaw security).weight color) := by
    rw [densityInverse_apply]
    field_simp [(primaryReference_positive security color).ne']
  have hinput : profileSquareNorm (primaryLaw security).weight
      (fun input => (primaryLaw security).weight input * kernel input) = (primaryLaw security).l2Sq kernel := by
    unfold profileSquareNorm FiniteDist.l2Sq FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro color _
    field_simp [(primaryReference_positive security color).ne']
  change (∑ color, (primaryLaw security).weight color * densityInverse security kernel color ^ 2) ≤ _
  simp only [hpoint, ← Finset.mul_sum]
  calc
    _ ≤ (activation security)⁻¹ ^ 2 * (4 * profileSquareNorm (primaryLaw security).weight
        (fun input => (primaryLaw security).weight input * kernel input)) :=
      mul_le_mul_of_nonneg_left (inverse_square_le security _) (sq_nonneg _)
    _ = _ := by rw [hinput]; ring

section Composition

variable {Input Middle Output : Type*} [Fintype Input] [Fintype Middle] [Fintype Output]

omit [Fintype Output] in
theorem tensor_apply_comp (degree : ℕ)
    (first : Fin degree → (Input → ℝ) →ₗ[ℝ] (Middle → ℝ))
    (second : Fin degree → (Middle → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin degree → Input) → ℝ) (output : Fin degree → Output) :
    TensorChannel.apply degree second (TensorChannel.apply degree first kernel) output =
      TensorChannel.apply degree (fun index => (second index).comp (first index)) kernel output := by
  simp only [TensorChannel.apply_formula_instance, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [LinearMap.comp_apply]
  have hmatrix (index : Fin degree) :
      second index (first index (Pi.single (input index) 1)) (output index) =
        ∑ middle : Middle, first index (Pi.single (input index) 1) middle *
          second index (Pi.single middle 1) (output index) :=
    TensorChannel.channel_sum_single (second index) (first index (Pi.single (input index) 1)) (output index)
  simp only [hmatrix]
  have hfactor :
      (∑ middle : Fin degree → Middle,
        (∏ index, first index (Pi.single (input index) 1) (middle index)) *
          (∏ index, second index (Pi.single (middle index) 1) (output index))) =
        ∏ index, ∑ middle : Middle,
          first index (Pi.single (input index) 1) middle * second index (Pi.single middle 1) (output index) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro middle _
    rw [Finset.prod_mul_distrib]
  rw [← hfactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro middle _
  ring

omit [Fintype Input] in
theorem tensor_apply_id (degree : ℕ) (kernel : (Fin degree → Input) → ℝ) (output : Fin degree → Input) :
    TensorChannel.apply degree (fun _ => LinearMap.id : Fin degree → (Input → ℝ) →ₗ[ℝ] (Input → ℝ)) kernel output =
      kernel output := by
  induction degree with
  | zero =>
    have hword : output = Fin.elim0 := Subsingleton.elim _ _
    simp only [TensorChannel.apply, hword]
  | succ degree ih =>
    change TensorChannel.apply degree (fun _ => LinearMap.id)
      (fun tail => kernel (Fin.cons (output 0) tail)) (fun index => output index.succ) = _
    rw [ih]
    congr 1
    exact Fin.cons_self_tail output

end Composition

def tensorInverse (security degree : ℕ) :=
  TensorChannel.applyLinear degree (fun _ => densityInverse security)

def tensorResponse (security degree : ℕ) :=
  TensorChannel.applyLinear degree (fun _ => densityResponse security)

theorem tensorResponse_inverse (security degree : ℕ) (kernel : (Fin degree → ActualControls.Palette security) → ℝ) :
    tensorResponse security degree (tensorInverse security degree kernel) = kernel := by
  have hcomp : (densityResponse security).comp (densityInverse security) = LinearMap.id := by
    apply LinearMap.ext
    intro kernel
    funext color
    exact congrFun (densityResponse_inverse security kernel) color
  funext output
  change TensorChannel.apply degree (fun _ => densityResponse security)
    (TensorChannel.apply degree (fun _ => densityInverse security) kernel) output = _
  rw [tensor_apply_comp]
  simp only [hcomp]
  exact tensor_apply_id degree kernel output

theorem tensor_energy_any {Input Output : Type*} [Fintype Input] [Fintype Output]
    (degree : ℕ) [decision : DecidableEq (Fin degree)]
    (input : Fin degree → FiniteDist Input) (output : Fin degree → FiniteDist Output)
    (channel : Fin degree → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin degree → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin degree → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (TensorChannel.apply degree channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  cases Subsingleton.elim decision (instDecidableEqFin degree)
  exact TensorChannel.energy_le degree input output channel bound hchannel kernel

theorem tensorInverse_energy (security degree : ℕ) (kernel : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (tensorInverse security degree kernel) ≤
      ((2 / activation security) ^ degree) ^ 2 *
        (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq kernel := by
  have h := tensor_energy_any degree (fun _ => primaryLaw security) (fun _ => primaryLaw security)
    (fun _ => densityInverse security) (fun _ => 2 / activation security)
    (fun _ => densityInverse_energy security) kernel
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

def MassCentered {Color : Type*} [Fintype Color] (degree : ℕ)
    (profile : (Fin degree → Color) → ℝ) : Prop :=
  ∀ index word, ∑ color, profile (Function.update word index color) = 0

def referenceWeight (security degree : ℕ) (word : Fin degree → ActualControls.Palette security) : ℝ :=
  ∏ index, (primaryLaw security).weight (word index)

theorem referenceWeight_pos (security degree : ℕ) (word : Fin degree → ActualControls.Palette security) :
    0 < referenceWeight security degree word :=
  Finset.prod_pos fun index _ => primaryReference_positive security (word index)

def massDensity (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun word => profile word / referenceWeight security degree word

def massLift (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  tensorInverse security degree (massDensity security degree profile)

def massLeading (security degree : ℕ) (density : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun word => referenceWeight security degree word * tensorResponse security degree density word

theorem massLift_leading (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    massLeading security degree (massLift security degree profile) = profile := by
  funext word
  rw [massLeading, massLift, tensorResponse_inverse, massDensity]
  exact mul_div_cancel₀ _ (referenceWeight_pos security degree word).ne'

def massEnergy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) : ℝ :=
  ∑ word, profile word ^ 2 / referenceWeight security degree word

theorem massDensity_energy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massDensity security degree profile) = massEnergy security degree profile := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro word _
  change referenceWeight security degree word * (profile word / referenceWeight security degree word) ^ 2 = _
  field_simp [(referenceWeight_pos security degree word).ne']

theorem massLift_energy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massLift security degree profile) ≤
        ((2 / activation security) ^ degree) ^ 2 * massEnergy security degree profile := by
  exact (tensorInverse_energy security degree (massDensity security degree profile)).trans_eq
    (congrArg (fun value => ((2 / activation security) ^ degree) ^ 2 * value)
      (massDensity_energy security degree profile))

theorem massLift_norm (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massLift security degree profile)) ≤
        (2 / activation security) ^ degree * Real.sqrt (massEnergy security degree profile) := by
  have henergy : 0 ≤ massEnergy security degree profile := by
    apply Finset.sum_nonneg
    intro word _
    exact div_nonneg (sq_nonneg _) (referenceWeight_pos security degree word).le
  have ha := activation_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt henergy]
  exact massLift_energy security degree profile

theorem massDensity_canonical (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (massDensity security degree profile) := by
  constructor
  · intro first second hequal
    have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
    rw [hword]
  · intro index _ word
    let remaining := ∏ other ∈ Finset.univ.erase index, (primaryLaw security).weight (word other)
    have hremaining : remaining ≠ 0 := by
      apply ne_of_gt
      exact Finset.prod_pos fun other _ => primaryReference_positive security (word other)
    have hweight (color : ActualControls.Palette security) :
        referenceWeight security degree (Function.update word index color) =
          (primaryLaw security).weight color * remaining := by
      unfold referenceWeight
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ index), Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro other hother
      rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
    have hpoint (color : ActualControls.Palette security) :
        (primaryLaw security).weight color * massDensity security degree profile (Function.update word index color) =
          profile (Function.update word index color) / remaining := by
      rw [massDensity, hweight]
      field_simp [(primaryReference_positive security color).ne', hremaining]
    change (∑ color, (primaryLaw security).weight color *
      massDensity security degree profile (Function.update word index color)) = 0
    simp only [hpoint, ← Finset.sum_div, hcentered index word, zero_div]

theorem tensorInverse_canonical (security degree : ℕ) (kernel : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ kernel) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (tensorInverse security degree kernel) := by
  let matrix : Fin degree → ActualControls.Palette security → ActualControls.Palette security → ℝ :=
    fun _ input output => densityInverse security (Pi.single input 1) output
  have hmean (index : Fin degree) (point : ActualControls.Palette security) :
      (primaryLaw security).expectation (matrix index point) =
        (activation security)⁻¹ * (primaryLaw security).weight point := by
    rw [show matrix index point = densityInverse security (Pi.single point 1) from rfl, densityInverse_mean]
    simp only [FiniteDist.expectation, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h := MixedKernel.matrixApply_canonical (fun _ : Fin degree => primaryLaw security)
    (fun _ : Fin degree => primaryLaw security) matrix (fun _ => (activation security)⁻¹) hmean kernel hcanonical
  have heq : MixedKernel.matrixApply matrix kernel = tensorInverse security degree kernel := by
    funext output
    exact (TensorChannel.apply_formula_instance degree (fun _ => densityInverse security) kernel output).symm
  rw [heq] at h
  exact h

theorem massLift_canonical (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (massLift security degree profile) :=
  tensorInverse_canonical security degree _ (massDensity_canonical security degree profile hcentered)

section Permutations

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

def wordPermutation (degree : ℕ) (permutation : Equiv.Perm (Fin degree)) :
    (Fin degree → Input) ≃ (Fin degree → Input) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by funext index; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv word := by funext index; simp only [Function.comp_apply, Equiv.symm_apply_apply]

omit [Fintype Output] in
theorem tensor_apply_symmetric (degree : ℕ) (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin degree → Input) → ℝ)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, kernel (word ∘ permutation) = kernel word)
    (permutation : Equiv.Perm (Fin degree)) (output : Fin degree → Output) :
    TensorChannel.apply degree (fun _ => channel) kernel (output ∘ permutation) =
      TensorChannel.apply degree (fun _ => channel) kernel output := by
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance]
  rw [← (wordPermutation (Input := Input) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  change kernel (input ∘ permutation) *
    (∏ index, channel (Pi.single (input (permutation index)) 1) (output (permutation index))) = _
  rw [hsymmetric permutation input]
  congr 1
  exact Equiv.prod_comp permutation (fun index => channel (Pi.single (input index) 1) (output index))

end Permutations

theorem massLift_symmetric (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word)
    (permutation : Equiv.Perm (Fin degree)) (word : Fin degree → ActualControls.Palette security) :
    massLift security degree profile (word ∘ permutation) = massLift security degree profile word := by
  have hinput : ∀ (order : Equiv.Perm (Fin degree)) word,
      massDensity security degree profile (word ∘ order) = massDensity security degree profile word := by
    intro order word
    rw [massDensity, massDensity, hsymmetric]
    congr 1
    exact Equiv.prod_comp order (fun index => (primaryLaw security).weight (word index))
  exact tensor_apply_symmetric degree (densityInverse security) _ hinput permutation word

end

end CurrentAFT.PrimaryTensorInverse

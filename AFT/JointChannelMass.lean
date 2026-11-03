import AFT.JointPhysicalChannel

/-! # Exact normalization of arbitrary canonical joint signed channels -/
namespace AFT.JointPhysicalChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

/-- Summing an actual finite signed output is a linear functional. -/
def totalLinear (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) : (Input → ℝ) →ₗ[ℝ] ℝ where
  toFun kernel := ∑ output, channel kernel output
  map_add' first second := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' scalar kernel := by simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

omit [Fintype Output] in
/-- A finite linear functional vanishing on all mean-zero inputs is
exactly a scalar multiple of the actual input expectation. -/
theorem linear_of_centered_zero (reference : FiniteDist Input)
    (response : (Input → ℝ) →ₗ[ℝ] ℝ)
    (hz : ∀ kernel, reference.expectation kernel = 0 → response kernel = 0)
    (kernel : Input → ℝ) :
    response kernel = reference.expectation kernel * response (fun _ => 1) := by
  have hd : kernel = TensorChannel.center reference kernel + reference.expectation kernel • (fun _ : Input => (1 : ℝ)) := by
    funext point
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, TensorChannel.center_apply, mul_one]
    ring
  calc
    response kernel = response (TensorChannel.center reference kernel + reference.expectation kernel • (fun _ : Input => (1 : ℝ))) := congrArg response hd
    _ = _ := by
      rw [map_add, map_smul, hz _ (TensorChannel.center_mean reference kernel)]
      simp

omit [Fintype Output] in
theorem expectation_single (reference : FiniteDist Input) (point : Input) :
    reference.expectation (Pi.single point 1) = reference.weight point := by
  simp [FiniteDist.expectation, Pi.single_apply]

section Joint
variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance jointChannelMassSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

omit [Fintype Input] [Fintype Output] in
/-- A product of finite signed local measures has the product of its exact
total masses, even when individual local measures have negative values. -/
theorem product_total (localMass : (index : Index) → (Slots index → Color) → ℝ) :
    (∑ word : Sigma Slots → Color, ∏ index, localMass index (fun slot => word ⟨index, slot⟩)) =
      ∏ index, ∑ word, localMass index word := by
  have he := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, localMass index (word index))
  exact he.trans (Fintype.prod_sum (fun index word => localMass index word)).symm

omit [Fintype Output] in
theorem mass_total
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) :
    (∑ output, mass Slots channel kernel output) =
      ∑ input, kernel input * ∏ index, totalLinear (channel index) (Pi.single (input index) 1) := by
  unfold mass totalLinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.mul_sum, product_total]
  rfl

omit [Fintype Output] in
/-- A fully coupled canonical input has exactly zero output mass under
any local signed channels preserving mean-zero inputs. -/
theorem canonical_mass_zero [Nonempty Index]
    (reference : Index → FiniteDist Input)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (hchannel : ∀ index density, (reference index).expectation density = 0 →
      (∑ output, channel index density output) = 0)
    (kernel : (Index → Input) → ℝ)
    (hc : Hoeffding.Canonical reference Finset.univ kernel) :
    (∑ output, mass Slots channel kernel output) = 0 := by
  have hrow (index : Index) (input : Input) :
      totalLinear (channel index) (Pi.single input 1) =
        (reference index).weight input * totalLinear (channel index) (fun _ => 1) := by
    rw [linear_of_centered_zero (reference index) (totalLinear (channel index)) (hchannel index), expectation_single]
  have hm : (FiniteDist.independent reference).expectation kernel = 0 := by
    let index : Index := Classical.arbitrary Index
    have hh := Hoeffding.orthogonal_of_centered reference ∅ index (by simp) kernel (fun _ => 1)
      (hc.2 index (Finset.mem_univ _)) (by intro first second he; rfl)
    simpa only [mul_one] using hh
  rw [mass_total]
  simp only [hrow, Finset.prod_mul_distrib]
  have he : (∑ input, kernel input * ((∏ index, (reference index).weight (input index)) *
      ∏ index, totalLinear (channel index) (fun _ => 1))) =
      (FiniteDist.independent reference).expectation kernel *
        ∏ index, totalLinear (channel index) (fun _ => 1) := by
    unfold FiniteDist.expectation FiniteDist.independent
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro input _
    ring
  rw [he, hm, zero_mul]

end Joint
end
end AFT.JointPhysicalChannel

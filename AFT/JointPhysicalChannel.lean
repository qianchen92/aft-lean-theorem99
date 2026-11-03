import AFT.TensorChannelFormula
import AFT.LocalCoefficientLinear
import AFT.JointFock

/-! # Exact joint signed mass and its physical generating polynomial -/

namespace AFT.JointPhysicalChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance jointPhysicalChannelSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

/-- The literal signed output of arbitrary local finite channels fed by one
joint input kernel. The joint kernel is retained inside the single input sum. -/
def mass (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (output : Sigma Slots → Color) : ℝ :=
  ∑ input, kernel input * ∏ index, channel index (Pi.single (input index) 1) (fun slot => output ⟨index, slot⟩)

/-- Signed local product measures satisfy the same exact polynomial identity
as probability blocks; no positivity or normalization is required. -/
theorem product_generating (reference : FiniteDist Color)
    (localMass : (index : Index) → (Slots index → Color) → ℝ) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : Sigma Slots => reference)
      (fun word => ∏ index, localMass index (fun slot => word ⟨index, slot⟩)) value =
      ∏ index, LocalTensors.localGenerating (fun _ : Slots index => reference) (localMass index) value := by
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, (localMass index (word index) : ℂ) *
      ∏ slot, (1 + LocalTensors.atomLinear reference (word index slot) value))
  unfold LocalTensors.localGenerating
  simp only [Complex.ofReal_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma Slots → Color,
        ∏ index, ((localMass index (fun slot => word ⟨index, slot⟩) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word ⟨index, slot⟩) value)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → Slots index → Color,
        ∏ index, ((localMass index (word index) : ℂ) *
          ∏ slot, (1 + LocalTensors.atomLinear reference (word index slot) value)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : Slots index → Color) =>
      (localMass index word : ℂ) * ∏ slot, (1 + LocalTensors.atomLinear reference (word slot) value))).symm

/-- The physical joint output polynomial is the exact joint input sum of
products of local response polynomials, even when the kernel is nonseparable. -/
theorem generating (reference : FiniteDist Color)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (value : Color → ℂ) :
    LocalTensors.localGenerating (fun _ : Sigma Slots => reference) (mass Slots channel kernel) value =
      ∑ input, (kernel input : ℂ) * ∏ index,
        LocalTensors.localGenerating (fun _ : Slots index => reference)
          (channel index (Pi.single (input index) 1)) value := by
  simp_rw [← product_generating Slots reference]
  unfold LocalTensors.localGenerating mass
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  apply Finset.sum_congr rfl
  intro output _
  ring

omit [Fintype Color] in
/-- With equally typed local outputs the literal joint mass is exactly the
recursive tensor operator for which the Hilbert bound has been proved. -/
theorem mass_eq_tensor (count : ℕ)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Color → ℝ))
    (kernel : (Fin count → Input) → ℝ) (output : Fin count → Color) :
    (∑ input, kernel input * ∏ index, channel index (Pi.single (input index) 1) (output index)) =
      TensorChannel.apply count channel kernel output :=
  (TensorChannel.apply_formula count channel kernel output).symm

end
end AFT.JointPhysicalChannel

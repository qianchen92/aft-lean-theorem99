import AFT.JointPhysicalChannel
import AFT.PackedFockEvaluation

/-! # Arbitrary joint physical responses through their exact finite Fock channels -/
namespace AFT.JointPhysicalChannel
open MeasureTheory LocalTensors TensorFock
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Input Color : Type*} [Fintype Index] [Fintype Input] [Fintype Color]
local instance jointPhysicalFockSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _
local instance jointPhysicalFockFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- A factorial decoder only contracts the complete joint coefficient array. -/
def decodedCoefficient (maximum : ℕ) (coefficient : (Index → PackedCoordinate maximum Color) → ℝ)
    (point : Index → PackedCoordinate maximum Color) : ℝ :=
  coefficient point * ∏ index, fockDecoder maximum (point index)

theorem decodedCoefficient_energy_le (maximum : ℕ)
    (coefficient : (Index → PackedCoordinate maximum Color) → ℝ) :
    (∑ point, decodedCoefficient maximum coefficient point ^ 2) ≤ ∑ point, coefficient point ^ 2 := by
  apply Finset.sum_le_sum
  intro point _
  have hp0 : 0 ≤ ∏ index, fockDecoder maximum (point index) :=
    Finset.prod_nonneg fun index _ => fockDecoder_nonneg maximum (point index)
  have hp1 : (∏ index, fockDecoder maximum (point index)) ≤ 1 :=
    Finset.prod_le_one (fun index _ => fockDecoder_nonneg maximum (point index))
      (fun index _ => fockDecoder_le_one maximum (point index))
  dsimp only [decodedCoefficient]
  rw [mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)

/-- A joint array built from local polynomial coefficients evaluates to the
joint sum of the products of the corresponding local polynomials. -/
theorem evaluation_product_sum (maximum : ℕ)
    (localCoefficient : Index → Input → PackedCoordinate maximum Color → ℝ)
    (kernel : (Index → Input) → ℝ) (value : Color → ℂ) :
    JointFock.evaluation (fun _ : Index => Fin (maximum + 1))
      (fun _ degree => Fin degree.val)
      (fun point => ∑ input, kernel input * ∏ index, localCoefficient index (input index) (point index)) value =
      ∑ input, (kernel input : ℂ) * ∏ index,
        ∑ coordinate : PackedCoordinate maximum Color,
          (localCoefficient index (input index) coordinate : ℂ) * wordMonomial coordinate.2 value := by
  unfold JointFock.evaluation
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [Finset.prod_mul_distrib]
  ring

variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The actual packed response array, still containing the full joint input
kernel inside one finite sum. -/
def coefficient (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (point : Index → PackedCoordinate maximum Color) : ℝ :=
  ∑ input, kernel input * ∏ index,
    packedFockChannel reference maximum population radius
      (channel index (Pi.single (input index) 1)) (point index)

/-- Exact physical generating-polynomial identity for arbitrary joint
canonical or noncanonical input. Every response coefficient is constructed
from the literal local signed channel. -/
theorem coefficient_evaluation (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : ∀ index, Fintype.card (Slots index) ≤ maximum)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) (value : Color → ℂ) :
    JointFock.evaluation (fun _ : Index => Fin (maximum + 1)) (fun _ degree => Fin degree.val)
      (decodedCoefficient maximum (coefficient Slots reference maximum population radius channel kernel)) value =
    localGenerating (fun _ : Sigma Slots => reference) (mass Slots channel kernel)
      (fun color => ((Real.sqrt 2 * (radius / Real.sqrt population) : ℝ) : ℂ) * value color) := by
  have harray : decodedCoefficient maximum (coefficient Slots reference maximum population radius channel kernel) =
      fun point => ∑ input, kernel input * ∏ index,
        (fockDecoder maximum (point index) * packedFockChannel reference maximum population radius
          (channel index (Pi.single (input index) 1)) (point index)) := by
    funext point
    unfold decodedCoefficient coefficient
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro input _
    rw [Finset.prod_mul_distrib]
    ring
  rw [harray, evaluation_product_sum maximum (fun index input coordinate =>
    fockDecoder maximum coordinate * packedFockChannel reference maximum population radius
      (channel index (Pi.single input 1)) coordinate) kernel value, generating]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact packedFockChannel_evaluation reference maximum population radius (hmaximum index) _ value

/-- Complete marked Fock energy of the actual arbitrary-joint physical
output, controlled by its exact packed Hilbert coefficient array. The
constant depends only on local degree and input order, never on the palette. -/
theorem joint_mass_fock_energy_le (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : ∀ index, Fintype.card (Slots index) ≤ maximum)
    (channel : (index : Index) → (Input → ℝ) →ₗ[ℝ] ((Slots index → Color) → ℝ))
    (kernel : (Index → Input) → ℝ) :
    BlockProducts.taggedCoefficientEnergy reference (mass Slots channel kernel) population radius ≤
      ((Fintype.card (Sigma Slots) + 1 : ℕ) *
        ((maximum + 1 : ℕ) ^ Fintype.card Index : ℕ) * ((Fintype.card Index * maximum).factorial : ℝ)) *
          ∑ point, coefficient Slots reference maximum population radius channel kernel point ^ 2 := by
  rw [taggedCoefficientEnergy_gaussian]
  have hdegree (choice : Index → Fin (maximum + 1)) :
      Fintype.card (Sigma (fun index : Index => Fin (choice index).val)) ≤ Fintype.card Index * maximum := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : Index, maximum := Finset.sum_le_sum fun index _ => by simpa using Nat.le_of_lt_succ (choice index).isLt
      _ = _ := by simp
  have he := JointFock.evaluation_energy_le (fun _ : Index => Fin (maximum + 1)) (fun _ degree => Fin degree.val)
    (decodedCoefficient maximum (coefficient Slots reference maximum population radius channel kernel))
    (Fintype.card Index * maximum) hdegree
  simp_rw [coefficient_evaluation Slots reference maximum population radius hmaximum channel kernel] at he
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans
  simp only [Fintype.card_fun, Fintype.card_fin] at *
  have hd := decodedCoefficient_energy_le maximum (coefficient Slots reference maximum population radius channel kernel)
  convert mul_le_mul_of_nonneg_left hd
    (show (0 : ℝ) ≤ (Fintype.card (Sigma Slots) + 1 : ℕ) *
      ((maximum + 1 : ℕ) ^ Fintype.card Index : ℕ) * ((Fintype.card Index * maximum).factorial : ℝ) by positivity) using 1
  ring

/-- The whole actual joint marked response is bounded by the product of the
mean-zero local Fock operator bounds and the Hilbert energy of the original
joint kernel. No factorization or nuclear-norm bound on the input is used. -/
theorem joint_mass_canonical_energy_le [Nonempty Input] (count : ℕ)
    (physicalSlots : Fin count → Type*) [∀ index, Fintype (physicalSlots index)]
    (reference : FiniteDist Color) (maximum population : ℕ) (radius : ℝ)
    (hmaximum : ∀ index, Fintype.card (physicalSlots index) ≤ maximum)
    (input : Fin count → FiniteDist Input)
    (channel : (index : Fin count) → (Input → ℝ) →ₗ[ℝ] ((physicalSlots index → Color) → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index density, (input index).expectation density = 0 →
      BlockProducts.taggedCoefficientEnergy reference (channel index density) population radius ≤
        bound index ^ 2 * (input index).l2Sq density)
    (kernel : (Fin count → Input) → ℝ) (hcanonical : Hoeffding.Canonical input Finset.univ kernel) :
    BlockProducts.taggedCoefficientEnergy reference (mass physicalSlots channel kernel) population radius ≤
      ((Fintype.card (Sigma physicalSlots) + 1 : ℕ) * ((maximum + 1 : ℕ) ^ count : ℕ) *
        ((count * maximum).factorial : ℝ)) *
          ((∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel) := by
  let channels := fun index : Fin count =>
    (packedFockChannel reference maximum population radius).comp (channel index)
  have he := TensorChannel.canonical_energy_counting_le_instance count input channels bound
    (fun index density hd => (packedFockChannel_energy_le reference maximum population radius
      (hmaximum index) (channel index density)).trans (hchannel index density hd)) kernel hcanonical
  have hid (point : Fin count → PackedCoordinate maximum Color) :
      coefficient physicalSlots reference maximum population radius channel kernel point =
        TensorChannel.apply count channels kernel point := by
    unfold coefficient
    exact (TensorChannel.apply_formula_instance count channels kernel point).symm
  simp_rw [← hid] at he
  have hg := joint_mass_fock_energy_le physicalSlots reference maximum population radius hmaximum channel kernel
  simp only [Fintype.card_fin] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left he (by positivity))

end
end AFT.JointPhysicalChannel

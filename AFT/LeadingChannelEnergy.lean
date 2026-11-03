import AFT.ActualResponseEnergy
import AFT.ActualLeadingOutput
import AFT.JointSignedChannel
import AFT.TensorChannel
import AFT.TensorFock

/-! # True leading coefficients as joint Hilbert tensor channels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]

def normalizedLeadingChannel (input : FiniteDist Input) (reference : Output → ℝ)
    (channel : Input → Output → ℝ) : (Input → ℝ) →ₗ[ℝ] (Output → ℝ) :=
  TensorChannel.ofKernel input (fun point output => channel point output/Real.sqrt (reference output))

theorem normalizedLeadingChannel_energy (input : FiniteDist Input) (reference : Output → ℝ)
    (channel : Input → Output → ℝ) (href : ∀ output,0 ≤ reference output) (kernel : Input → ℝ) :
    (∑ output,normalizedLeadingChannel input reference channel kernel output^2)=
      profileSquareNorm reference (fun output => ∑ point,input.weight point*kernel point*channel point output) := by
  apply Finset.sum_congr rfl
  intro output _
  change (∑ point,input.weight point*(channel point output/Real.sqrt (reference output)*kernel point))^2=_
  have he : (∑ point,input.weight point*(channel point output/Real.sqrt (reference output)*kernel point))=
      (∑ point,input.weight point*kernel point*channel point output)/Real.sqrt (reference output) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro point _
    ring
  rw [he,div_pow,Real.sq_sqrt (href output)]

def leadingSeedTensor {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (reference : Output → ℝ)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    BlockFock.Tensor (Fin (seed.primaryOrder+seed.bodyOrder)) Output :=
  TensorChannel.apply (seed.primaryOrder+seed.bodyOrder)
    (fun slot => normalizedLeadingChannel (inputReference primary body seed slot) reference
      (seedChannel primaryChannel bodyChannel seed slot)) seed.kernel

theorem leadingSeedTensor_energy {Color : Type*} [Fintype Color]
    (primary body : FiniteDist Color) (reference : Output → ℝ)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color)
    (primaryBound bodyBound : ℝ) (href : ∀ output,0 ≤ reference output)
    (hp : ∀ kernel,profileSquareNorm reference (fun output => ∑ point,
      primary.weight point*kernel point*primaryChannel point output) ≤primaryBound^2*primary.l2Sq kernel)
    (hb : ∀ kernel,profileSquareNorm reference (fun output => ∑ point,
      body.weight point*kernel point*bodyChannel point output) ≤bodyBound^2*body.l2Sq kernel) :
    BlockFock.tensorEnergy (leadingSeedTensor primary body reference primaryChannel bodyChannel seed) ≤
      (primaryBound^2)^seed.primaryOrder*(bodyBound^2)^seed.bodyOrder*
        (FiniteDist.independent (inputReference primary body seed)).l2Sq seed.kernel := by
  have hlocal (slot) (kernel) : (∑ output,
      normalizedLeadingChannel (inputReference primary body seed slot) reference
        (seedChannel primaryChannel bodyChannel seed slot) kernel output^2) ≤
      (Fin.addCases (fun _ => primaryBound) (fun _ => bodyBound) slot)^2*
        (inputReference primary body seed slot).l2Sq kernel := by
    rw [normalizedLeadingChannel_energy _ _ _ href]
    cases slot using Fin.addCases
    · simpa only [inputReference,seedChannel,Fin.addCases_left] using hp kernel
    · simpa only [inputReference,seedChannel,Fin.addCases_right] using hb kernel
  have hh := TensorChannel.energy_counting_le (seed.primaryOrder+seed.bodyOrder)
    (inputReference primary body seed)
    (fun slot => normalizedLeadingChannel (inputReference primary body seed slot) reference
      (seedChannel primaryChannel bodyChannel seed slot))
    (Fin.addCases (fun _ => primaryBound) (fun _ => bodyBound)) hlocal seed.kernel
  simp only [BlockFock.tensorEnergy,leadingSeedTensor]
  rw [show (fun a b : Fin (seed.primaryOrder+seed.bodyOrder) => Classical.propDecidable (a=b))=instDecidableEqFin (seed.primaryOrder+seed.bodyOrder) from Subsingleton.elim _ _]
  simpa only [Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero

/-- The actual primary and body channels, with the reference square root
normalization required by the Gaussian coefficients. -/
theorem actual_leading_channels_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    (∀ kernel,profileSquareNorm (actualReferenceLaw C n (beta n)).weight
      (fun output => ∑ point,(actualPrimaryLaw C n (beta n)).weight point*kernel point*actualPrimaryChannel C n point output) ≤
      responseEnergyConstant*(n : ℝ)^26*(actualPrimaryLaw C n (beta n)).l2Sq kernel) ∧
    (∀ kernel,profileSquareNorm (actualReferenceLaw C n (beta n)).weight
      (fun output => ∑ point,(actualBodyLaw C n (beta n)).weight point*kernel point*actualBodyChannel n point output) ≤
      (2*Parameters.modulus n : ℝ)*(actualBodyLaw C n (beta n)).l2Sq kernel) := by
  filter_upwards [actual_response_energy_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_reference_lower_eventually C hC beta hbeta] with n he hl hr
  have hq : (0 : ℝ)<Parameters.modulus n := by exact_mod_cast (Parameters.modulus_prime n).pos
  have href color : 0<(actualReferenceLaw C n (beta n)).weight color := by
    rw [hl.2.2]
    exact lt_of_lt_of_le (by positivity : (0 : ℝ)<1/(2*Parameters.modulus n)) (hr color)
  constructor
  · intro kernel
    have hformula : (fun output => ∑ point,(actualPrimaryLaw C n (beta n)).weight point*kernel point*actualPrimaryChannel C n point output)=
        v7Activation C n • actualResponse C n (fun point => (actualPrimaryLaw C n (beta n)).weight point*kernel point) := by
      funext output
      exact actualPrimaryChannel_profile C n _ output
    rw [hformula,hl.2.2]
    have hh := he (fun point => (actualPrimaryLaw C n (beta n)).weight point*kernel point)
    rw [← hl.1,profileSquareNorm_weight_mul] at hh
    exact hh
  · intro kernel
    apply signedChannel_profile_energy_le _ _ _ _ href (by positivity)
      (actualBodyChannel_nonneg n) (fun point => (actualBodyChannel_mass n point).le) ?_ kernel
    intro output
    calc
      (∑ point,(actualBodyLaw C n (beta n)).weight point*actualBodyChannel n point output) ≤
          ∑ point,(actualBodyLaw C n (beta n)).weight point*1 := by
        apply Finset.sum_le_sum
        intro point _
        have hroot : (actualRootLaw n).weight (output-point) ≤ 1 := by
          have hh := Finset.single_le_sum (fun color (_ : color∈Finset.univ) => (actualRootLaw n).nonneg color) (Finset.mem_univ (output-point))
          simpa only [FiniteDist.sum_one] using hh
        exact mul_le_mul_of_nonneg_left hroot (FiniteDist.nonneg _ _)
      _ = 1 := by simp only [mul_one,FiniteDist.sum_one]
      _ ≤ (2*Parameters.modulus n : ℝ)*(actualReferenceLaw C n (beta n)).weight output := by
        rw [hl.2.2]
        have hh := mul_le_mul_of_nonneg_left (hr output) (by positivity : (0 : ℝ)≤2*Parameters.modulus n)
        simpa only [mul_one_div_cancel (by positivity : (2*Parameters.modulus n : ℝ)≠0)] using hh

 theorem actual_leading_seed_tensor_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ seed : InputSeed (Fin (Parameters.modulus n)),
    BlockFock.tensorEnergy (leadingSeedTensor (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (actualReferenceLaw C n (beta n)).weight (actualPrimaryChannel C n) (actualBodyChannel n) seed) ≤
      (responseEnergyConstant*(n : ℝ)^26)^seed.primaryOrder*(2*Parameters.modulus n : ℝ)^seed.bodyOrder*
        (FiniteDist.independent (inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) seed)).l2Sq seed.kernel := by
  filter_upwards [actual_leading_channels_energy_eventually C hC beta hbeta] with n h seed
  have hp : 0 ≤ responseEnergyConstant*(n : ℝ)^26 := by unfold responseEnergyConstant; positivity
  have hb : 0 ≤ (2*Parameters.modulus n : ℝ) := by positivity
  have hh := leadingSeedTensor_energy (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualReferenceLaw C n (beta n)).weight (actualPrimaryChannel C n) (actualBodyChannel n) seed
    (Real.sqrt (responseEnergyConstant*(n : ℝ)^26)) (Real.sqrt (2*Parameters.modulus n : ℝ))
    (FiniteDist.nonneg _) (by simpa only [Real.sq_sqrt hp] using h.1)
    (by simpa only [Real.sq_sqrt hb] using h.2)
  simpa only [Real.sq_sqrt hp,Real.sq_sqrt hb] using hh

end
end AFT.V7Calibration

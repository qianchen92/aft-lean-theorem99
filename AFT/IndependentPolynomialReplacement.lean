import AFT.IndependentJointImage
import AFT.IndependentPairedChartIdentity
import AFT.PolynomialRemainingOutput

/-! # Exact independent replacement with arbitrary polynomial old channels -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial PhysicalBlockTensors MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPolynomialReplacementFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPolynomialReplacementSubtypeDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
local instance independentPolynomialReplacementUnitDecEq : DecidableEq Unit := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

theorem actualPrimaryChannel_matrix (C : ℝ) (n : ℕ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) :
    actualPrimaryChannel C n=fun input output => v7Activation C n*LinearMap.toMatrix' operator.toLinearMap output input := by
  rw [hop]
  funext input output
  simp only [actualPrimaryChannel,LinearMap.toMatrix'_apply]
  congr 2
  apply congrArg (fun profile : Fin (Parameters.modulus n) → ℝ => actualResponse C n profile output)
  funext color
  by_cases h : color=input <;> simp [Pi.single_apply,h]

theorem independentJointInverse_polynomial_output (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
    (forms : Rest → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ)
    (selected : Finset (Fin 4)) :
    jointChannelPolynomial (Sum.elim (fun _ : selected => actualPrimaryLaw C n beta) other)
      (Sum.elim (fun _ : selected => channelForm (actualPrimaryChannel C n)) forms)
      (independentJointInverse C n beta operator charts other selected kernel) =
      polynomialRemainingOutput other forms (fun rest => referenceCoefficientForm
        (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
        (independentPairedNumerator C n beta charts (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest)) selected) := by
  unfold independentJointInverse
  rw [actualPrimaryChannel_matrix C n operator hop]
  rw [jointChannelPolynomial_new_inverse _ _ _ _ hrho operator (fun _ => hp)]
  unfold polynomialRemainingOutput
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro rest _
  congr 2

theorem independentOriginal_polynomial_output (C : ℝ) (n : ℕ) (beta : ℝ)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
    (forms : Rest → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ) :
    jointChannelPolynomial (Sum.elim (fun _ : Unit => actualPrimaryLaw C n beta) other)
      (Sum.elim (fun _ : Unit => channelForm (actualPrimaryChannel C n)) forms) (singletonJoin kernel)=
      polynomialRemainingOutput other forms (fun rest => profileForm
        (fun output => v7Activation C n*actualResponse C n
          (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest) output)) := by
  rw [jointChannelPolynomial_sum]
  unfold polynomialRemainingOutput
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro rest _
  congr 2
  have hs : (fun word : Unit → Fin (Parameters.modulus n) => singletonJoin kernel (Sum.elim word rest))=
      fun word => kernel (word ()) rest := by funext word; rfl
  rw [hs,← indexedOutput_joint]
  have hu := indexedOutput_unit_profile (actualPrimaryLaw C n beta) (actualPrimaryChannel C n) (fun color => kernel color rest)
  rw [hu,profileForm_apply]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  exact actualPrimaryChannel_profile C n _ output

/-- All polynomial channels at the other old coordinates are arbitrary.
This is the exact local identity used by the tagged original-coordinate recursion. -/
theorem independentPolynomialReplacement_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ (Rest : Type) [Fintype Rest] [DecidableEq Rest],
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) →
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
      (forms : Rest → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)))
      (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ),
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    jointChannelPolynomial (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other)
        (Sum.elim (fun _ : Unit => channelForm (actualPrimaryChannel C n)) forms) (singletonJoin kernel) +
      (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        jointChannelPolynomial (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
          (Sum.elim (fun _ : selected => channelForm (actualPrimaryChannel C n)) forms)
          (independentJointInverse C n (beta n) operator charts other selected kernel)) =
      polynomialRemainingOutput other forms (fun rest => centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (independentPairedNumerator C n (beta n) charts
          (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest))) := by
  filter_upwards [independentPaired_first_with_charts_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,actual_primary_probability_eventually C hC beta hbeta,
    eventually_ge_atTop 2] with n hf hl hp hn Rest _ _ operator hop charts hcharts other forms kernel hkernel
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  rw [independentOriginal_polynomial_output]
  simp_rw [independentJointInverse_polynomial_output C n (beta n) operator hop hrho (fun color => (hp0 color).ne')]
  rw [← map_sum,← map_add]
  congr 1
  funext rest
  simp only [Pi.add_apply,Finset.sum_apply]
  let mass := independentPairedNumerator C n (beta n) charts
    (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest)
  have hfirst := hf charts hcharts _ (hkernel rest)
  have he := referenceHigherForm_sum (actualPrimaryLaw C n (beta n)) (actualReferenceLaw C n (beta n)) hp0 mass hfirst.1
  rw [he]
  have hc : profileForm (fun output => v7Activation C n*actualResponse C n
      (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest) output)=
      profileForm (physicalFirstProfile mass) := by
    congr 1
    funext output
    have hcount : physicalFirstProfile mass output=fourOutputCount mass output := by
      unfold physicalFirstProfile fourOutputCount
      congr 1
      ext word
      simp
    rw [hcount]
    exact (hfirst.2 output).symm
  rw [hc]
  ring

end
end AFT.V7Calibration

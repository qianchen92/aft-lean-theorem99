import AFT.IndependentJointUpper
import AFT.IndependentPairedFirst
import AFT.CoordinateSliceOutput
import AFT.RemainingOutput
import AFT.ReferenceHigherForm

/-! # Exact physical quotient images for arbitrary joint primary/body inputs -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial PhysicalBlockTensors MixedKernel Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
local instance independentJointImageFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentJointImageSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Primary Body : Type} [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body]

def independentRemainingOutput (C : ℝ) (n : ℕ) (beta : ℝ) :
    ((Primary ⊕ Body → Fin (Parameters.modulus n)) → MvPolynomial (Fin (Parameters.modulus n)) ℝ) →ₗ[ℝ]
      MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  remainingOutput (Sum.elim (fun _ : Primary => actualPrimaryLaw C n beta) (fun _ : Body => actualBodyLaw C n beta))
    (Sum.elim (fun _ : Primary => actualPrimaryChannel C n) (fun _ : Body => actualBodyChannel n))

/-- The actual four-output numerator is contracted with every unchanged
old channel, without splitting the old joint input into product kernels. -/
def independentJointPhysicalNumerator (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ) :
    MvPolynomial (Fin (Parameters.modulus n)) ℝ :=
  independentRemainingOutput C n beta (fun rest => centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (independentPairedNumerator C n beta charts (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest)))

theorem independentJointHigherSeed_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (hop : operator.toLinearMap=actualResponse C n) (hrho : v7Activation C n ≠ 0)
    (hp : ∀ color,(actualPrimaryLaw C n beta).weight color ≠ 0)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ)
    (selected : Finset (Fin 4)) :
    actualLeadingOutput C n beta (MvPolynomial.X (independentJointHigherSeed C n beta operator charts kernel selected)) =
      independentRemainingOutput C n beta (fun rest => referenceCoefficientForm
        (actualPrimaryLaw C n beta) (actualReferenceLaw C n beta)
        (independentPairedNumerator C n beta charts (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest)) selected) := by
  rw [actualLeadingOutput,outputHom_X,independentJointHigherSeed,groupedFiniteSeed_output]
  unfold independentJointInverse
  have hchannel : actualPrimaryChannel C n =
      fun input output => v7Activation C n*LinearMap.toMatrix' operator.toLinearMap output input := by
    rw [hop]
    funext input output
    simp only [actualPrimaryChannel,LinearMap.toMatrix'_apply]
    congr 2
    apply congrArg (fun profile : Fin (Parameters.modulus n) → ℝ => actualResponse C n profile output)
    funext color
    by_cases h : color=input <;> simp [Pi.single_apply,h]
  rw [hchannel]
  rw [indexedOutput_new_inverse _ _ _ _ hrho operator (fun _ => hp)]
  unfold independentRemainingOutput remainingOutput
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [← hchannel]
  apply Finset.sum_congr (by ext word; simp)
  intro rest _
  congr 2

omit [DecidableEq Primary] [DecidableEq Body] in
theorem independentOriginalJointSeed_image (C : ℝ) (n : ℕ) (beta : ℝ)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ) :
    actualLeadingOutput C n beta (MvPolynomial.X (independentOriginalJointSeed kernel)) =
      independentRemainingOutput C n beta (fun rest => profileForm
        (fun output => v7Activation C n*actualResponse C n
          (fun color => (actualPrimaryLaw C n beta).weight color*kernel color rest) output)) := by
  rw [actualLeadingOutput,outputHom_X,independentOriginalJointSeed,groupedFiniteSeed_output,indexedOutput_sum]
  unfold independentRemainingOutput remainingOutput
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro rest _
  congr 2
  have hs : (fun word : Unit → Fin (Parameters.modulus n) => singletonJoin kernel (Sum.elim word rest)) =
      fun word => kernel (word ()) rest := by
    funext word
    rfl
  rw [hs]
  have hu := indexedOutput_unit_profile (actualPrimaryLaw C n beta) (actualPrimaryChannel C n)
    (fun color => kernel color rest)
  rw [hu,profileForm_apply]
  apply Finset.sum_congr rfl
  intro output _
  congr 2
  exact actualPrimaryChannel_profile C n _ output

/-- A single actual chart family realizes the whole joint quotient. The
right-hand side still contains all original body convolution channels. -/
theorem independentJointUpper_image_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∃ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second =
      conditionalJointOutput C n mark attached first second) ∧
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) → ∀ depth : ℕ,
    actualLeadingOutput C n (beta n)
      (MvPolynomial.X (independentOriginalJointSeed kernel)+independentJointUpper C n (beta n) operator charts kernel depth) =
      independentJointPhysicalNumerator C n (beta n) charts kernel*
        finiteCorrection (centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
          (independentPairedPositiveMass C n (beta n) charts)-1) depth := by
  filter_upwards [independentPaired_first_eventually C hC beta hbeta,
    independentPairedPositiveMass_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,actual_primary_probability_eventually C hC beta hbeta,
    eventually_ge_atTop 2] with n hf hm hl hp hn
  obtain ⟨charts,hcharts,hfirst⟩ := hf
  refine ⟨charts,hcharts,?_⟩
  intro operator hop kernel hkernel depth
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).ne'
  let p := actualPrimaryLaw C n (beta n)
  let r := actualReferenceLaw C n (beta n)
  let mass := fun rest => independentPairedNumerator C n (beta n) charts (fun color => p.weight color*kernel color rest)
  have hfirstform (rest) : profileForm (physicalFirstProfile (mass rest)) =
      profileForm (fun output => v7Activation C n*actualResponse C n (fun color => p.weight color*kernel color rest) output) := by
    congr 1
    funext output
    have hcount : physicalFirstProfile (mass rest) output=fourOutputCount (mass rest) output := by
      unfold physicalFirstProfile fourOutputCount
      congr 1
      ext word
      simp
    rw [hcount]
    exact (hfirst _ (hkernel rest)).2 output
  have hcomponent (rest) :
      (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        referenceCoefficientForm p r (mass rest) selected) =
        centeredGeneratingLinear r.weight (mass rest)-profileForm (physicalFirstProfile (mass rest)) := by
    exact referenceHigherForm_sum p r hp0 (mass rest) (hfirst _ (hkernel rest)).1
  have hhigh : actualLeadingOutput C n (beta n) (independentJointHigherTable C n (beta n) operator charts kernel) =
      independentJointPhysicalNumerator C n (beta n) charts kernel-
        actualLeadingOutput C n (beta n) (MvPolynomial.X (independentOriginalJointSeed kernel)) := by
    unfold independentJointHigherTable
    simp only [map_sum,independentJointHigherSeed_image C n (beta n) operator hop hrho (fun color => (hp0 color).ne')]
    rw [← map_sum]
    have he : (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        fun rest => referenceCoefficientForm p r (mass rest) selected) =
        fun rest => centeredGeneratingLinear r.weight (mass rest)-profileForm (physicalFirstProfile (mass rest)) := by
      funext rest
      simpa only [Finset.sum_apply] using hcomponent rest
    change independentRemainingOutput C n (beta n)
      (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        fun rest => referenceCoefficientForm p r (mass rest) selected) = _
    rw [he]
    change independentRemainingOutput C n (beta n)
      ((fun rest => centeredGeneratingLinear r.weight (mass rest))-
        (fun rest => profileForm (physicalFirstProfile (mass rest)))) = _
    rw [map_sub]
    congr 1
    rw [independentOriginalJointSeed_image]
    congr 1
    funext rest
    exact hfirstform rest
  have hd := actual_referenceCoefficientTable_inverse_image C n (beta n) operator hop hrho hp0
    (independentPairedPositiveMass C n (beta n) charts)
  rw [(hm charts).2,map_one] at hd
  unfold independentJointUpper localUpperTable
  have hcancel (a b : Table (InputSeed (Fin (Parameters.modulus n)))) : a+(b-a)=b := by ring
  rw [hcancel,map_mul,map_add,hhigh,add_sub_cancel]
  congr 1
  unfold independentPositiveInputTable referenceInverseTable
  simp only [finiteCorrection,map_sum,map_pow,map_neg,hd]

end
end AFT.V7Calibration

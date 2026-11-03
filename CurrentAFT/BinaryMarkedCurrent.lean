import CurrentAFT.BinaryMarkedKernel
import CurrentAFT.BinaryGaussianAverage
import CurrentAFT.BinaryDiffuseCurrent

/-! # Self-generated current binary marked-pair entries -/
namespace CurrentAFT.BinaryMarkedCurrent
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata

def evaluate (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) : RationalResult :=
  BinaryGaussianAverage.evaluate security cutoff bits (fun left right =>
    BinaryMarkedKernel.average colors width primary left.val right.val sourceSign source first second)

theorem evaluate_value (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) :
    (evaluate security colors width cutoff bits primary sourceSign source first second).data.decode =
      LocalMarkedProgram.evaluate security colors width cutoff bits primary (signedValue sourceSign source)
        (value first) (value second) := by
  simp only [evaluate, BinaryGaussianAverage.evaluate_value, BinaryMarkedKernel.average_value,
    windowGaussianWeights, LocalMarkedProgram.evaluate]
  rw [← (windowIndexEquiv cutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro left _
  rw [← (windowIndexEquiv cutoff).sum_comp]
  apply Finset.sum_congr rfl
  intro right _
  simp only [windowIndexEquiv, Equiv.coe_fn_mk]
  congr 2
  omega

theorem evaluate_bounds (security colors width cutoff bits primary : ℕ) (sourceSign : Bool)
    (source first second : List Bool) (hcutoff : cutoff ≤ (security+2)^2) :
    HeightBound (evaluate security colors width cutoff bits primary sourceSign source first second).data.decode
      (BinaryGaussianAverage.sumHeight (2*cutoff+1) (BinaryGaussianAverage.gaussianHeight security bits)
        (BinaryMarkedKernel.averageHeight width)) ∧
    (evaluate security colors width cutoff bits primary sourceSign source first second).work ≤
      BinaryGaussianAverage.evaluateWork security cutoff bits (BinaryMarkedKernel.averageHeight width)
        (BinaryMarkedKernel.averageWork width (BinaryDiffuseProgram.inputBound colors width primary cutoff source first second)) := by
  let bound := BinaryDiffuseProgram.inputBound colors width primary cutoff source first second
  have hkernel (left right : Fin (2*cutoff+1)) := BinaryMarkedKernel.average_bounds
    colors width primary left.val right.val sourceSign source first second bound
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by have := left.isLt; unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by have := right.isLt; unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
    (by unfold bound BinaryDiffuseProgram.inputBound; omega)
  exact BinaryGaussianAverage.evaluate_bounds security cutoff bits _ _ _ hcutoff
    (fun left right => (hkernel left right).1) (fun left right => (hkernel left right).2)

def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let result := evaluate security parameters.colors parameters.width parameters.cutoff bits primary sourceSign source first second
  ⟨result.data, parameters.work + result.work + 2⟩

theorem current_value (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) :
    (current security bits primary sourceSign source first second).data.decode =
      LocalMarkedProgram.current security bits primary (signedValue sourceSign source) (value first) (value second) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  unfold current
  rw [evaluate_value, hq, hw, hc]
  unfold LocalMarkedProgram.current
  rw [PublicParameterProgram.modulus_value]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (sourceSign : Bool) (sourceCode firstCode secondCode : List Bool)
    (hs : signedValue sourceSign sourceCode = source.val)
    (hf : value firstCode = first.val) (ht : value secondCode = second.val) :
    |((current security bits primary.val sourceSign sourceCode firstCode secondCode).data.decode : ℝ) -
      (LocalReferenceEnergy.markedPairAt security primary source).weight (first, second)| ≤ 2/(2:ℝ)^bits := by
  rw [current_value, hs, hf, ht]
  exact LocalMarkedProgram.current_error security bits primary first second source

def currentHeight (security bits : ℕ) : ℕ :=
  BinaryGaussianAverage.sumHeight (2*(security+2)^2+1) (BinaryGaussianAverage.gaussianHeight security bits)
    (BinaryMarkedKernel.averageHeight ((security+2)^48))

theorem current_height (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) :
    HeightBound (current security bits primary sourceSign source first second).data.decode (currentHeight security bits) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  have hcut : (BinaryDiffuseCurrent.metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have hh := (evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryDiffuseCurrent.metadata security).cutoff bits primary
    sourceSign source first second hcut).1
  conv_rhs at hh => rw [hw, hc]
  apply hh.mono
  have hn : 2*(((security+2)^2-1)/2)+1 ≤ 2*(security+2)^2+1 := by omega
  unfold currentHeight BinaryGaussianAverage.sumHeight
  gcongr

theorem averageWork_mono {width width' bound bound' : ℕ} (hw : width ≤ width') (hb : bound ≤ bound') :
    BinaryMarkedKernel.averageWork width bound ≤ BinaryMarkedKernel.averageWork width' bound' := by
  unfold BinaryMarkedKernel.averageWork BinaryMarkedKernel.coinWork BinaryMarkedKernel.pointWork
    BinaryMarkedKernel.companionWork primitiveWorkBound
  gcongr

noncomputable def averageHeightPolynomial (width : Polynomial ℕ) : Polynomial ℕ := 4*width+3
noncomputable def companionWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  1000*(3*bound+2)^2 + 5*(50*(bound+1)^2) + 300*(bound+10)
noncomputable def pointWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  50*(bound+1)^2 + companionWorkPolynomial bound + (48*bound+39) + (48*(2*bound+7)+39) + 6
noncomputable def coinWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  width*(pointWorkPolynomial bound+primitiveWorkPolynomial (width+1)+2)+2 +
    60*(width+1)^2+(2*primitiveWorkPolynomial width+2)+3
noncomputable def averageWorkPolynomial (width bound : Polynomial ℕ) : Polynomial ℕ :=
  2*coinWorkPolynomial width bound+primitiveWorkPolynomial (2*width)+primitiveWorkPolynomial (4*width+2)+4

theorem averageWorkPolynomial_eval (width bound : Polynomial ℕ) (security : ℕ) :
    (averageWorkPolynomial width bound).eval security =
      BinaryMarkedKernel.averageWork (width.eval security) (bound.eval security) := by
  simp only [averageWorkPolynomial, coinWorkPolynomial, pointWorkPolynomial, companionWorkPolynomial,
    BinaryMarkedKernel.averageWork, BinaryMarkedKernel.coinWork, BinaryMarkedKernel.pointWork,
    BinaryMarkedKernel.companionWork, primitiveWorkPolynomial_eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryGaussianAverage.evaluateWorkPolynomial ((Polynomial.X+2)^2)
    precision (averageHeightPolynomial ((Polynomial.X+2)^48))
    (averageWorkPolynomial ((Polynomial.X+2)^48) (BinaryDiffuseCurrent.parameterPolynomial inputBits)) + 2

theorem current_polynomial_work (security : ℕ) (primary : FirstHistogram.Palette security)
    (sourceSign : Bool) (source first second : List Bool) (precision inputBits : Polynomial ℕ)
    (hs : source.length ≤ inputBits.eval security) (hf : first.length ≤ inputBits.eval security)
    (ht : second.length ≤ inputBits.eval security) :
    (current security (precision.eval security) primary.val sourceSign source first second).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, hw, hc⟩
  have hcut : (BinaryDiffuseCurrent.metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have we := (evaluate_bounds security (BinaryDiffuseCurrent.metadata security).colors
    (BinaryDiffuseCurrent.metadata security).width (BinaryDiffuseCurrent.metadata security).cutoff
    (precision.eval security) primary.val sourceSign source first second hcut).2
  conv_rhs at we => rw [hq, hw, hc]
  have hbound := BinaryDiffuseCurrent.input_bound security primary source first second (inputBits.eval security) hs hf ht
  have hsum := BinaryGaussianAverage.sumWork_mono
    (gh := BinaryGaussianAverage.gaussianHeight security (precision.eval security))
    (kh := BinaryMarkedKernel.averageHeight ((security+2)^48))
    (show 2*(((security+2)^2-1)/2)+1 ≤ 2*(security+2)^2+1 by omega) le_rfl le_rfl
    (averageWork_mono (width := (security+2)^48) le_rfl hbound)
  have hfinal := Nat.add_le_add_right
    (Nat.add_le_add (show CurrentGaussianBits.tableWork security (precision.eval security) ≤
      CurrentGaussianBits.tableWork security (precision.eval security) from le_rfl) hsum) 2
  have htotal := Nat.add_le_add_right (Nat.add_le_add (BinaryDiffuseCurrent.metadata_work security) (we.trans hfinal)) 2
  change (current security (precision.eval security) primary.val sourceSign source first second).work ≤ _ at htotal
  convert htotal using 1
  simp only [currentWorkPolynomial, BinaryGaussianAverage.evaluateWorkPolynomial_eval,
    BinaryDiffuseCurrent.metadataWorkPolynomial_eval, averageWorkPolynomial_eval,
    BinaryDiffuseCurrent.parameterPolynomial_eval, averageHeightPolynomial, BinaryMarkedKernel.averageHeight,
    BinaryGaussianAverage.evaluateWork, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]

end
end CurrentAFT.BinaryMarkedCurrent

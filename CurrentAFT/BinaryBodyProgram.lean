import CurrentAFT.BinaryBodyKernel
import CurrentAFT.BinarySeedAverage

/-! # The two actual body reference tables produced by binary arithmetic -/
namespace CurrentAFT.BinaryBodyProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signedAdd addCounter multiplyCounter BinaryDiffuseCurrent.metadata BinaryActivationProgram.cutoff

def shift (edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : SignedResult :=
  let edge := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  let result := signedAdd edge.negative (if includeScalar then source.negative else false)
    edge.digits (if includeScalar then source.digits else [])
  ⟨result.negative, result.digits, edge.work + source.work + result.work + 3⟩

theorem shift_value (edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :
    signedValue (shift edgeCutoff scalarCutoff includeScalar left right scalar).negative
      (shift edgeCutoff scalarCutoff includeScalar left right scalar).digits =
      (left.val:ℤ)-right.val + if includeScalar then (scalar.val:ℤ)-scalarCutoff else 0 := by
  unfold shift
  rw [signedAdd_value, BinaryAnchorProgram.coordinate_value]
  cases includeScalar with
  | false => rfl
  | true =>
    simp only [if_true]
    rw [BinaryAnchorProgram.coordinate_value]

def shiftWork (bound : ℕ) : ℕ := BinaryAnchorProgram.coordinateWork (2*bound)+
  BinaryAnchorProgram.coordinateWork bound+(20*(4*bound+1)+8)+3

theorem shift_bounds (edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (bound : ℕ)
    (he : edgeCutoff ≤ bound) (hs : scalarCutoff ≤ bound) :
    (shift edgeCutoff scalarCutoff includeScalar left right scalar).digits.length ≤ 4*bound+2 ∧
      (shift edgeCutoff scalarCutoff includeScalar left right scalar).work ≤ shiftWork bound := by
  let edge := BinaryAnchorProgram.coordinate right.val left.val
  let source := BinaryAnchorProgram.coordinate scalarCutoff scalar.val
  have hl : left.val ≤ 2*bound := by have := left.isLt; omega
  have hr : right.val ≤ 2*bound := by have := right.isLt; omega
  have hi : scalar.val ≤ 2*bound := by have := scalar.isLt; omega
  have hed := BinaryAnchorProgram.coordinate_bounds right.val left.val (2*bound) hr (by omega)
  have hsc := BinaryAnchorProgram.coordinate_bounds scalarCutoff scalar.val bound hs hi
  have el : edge.digits.length ≤ 4*bound+1 := hed.1.trans (by omega)
  have sl : source.digits.length ≤ 2*bound+1 := hsc.1
  have sp : (if includeScalar then source.digits else []).length ≤ 2*bound+1 := by split <;> simp_all
  have bl := signedAdd_length edge.negative (if includeScalar then source.negative else false)
    edge.digits (if includeScalar then source.digits else [])
  have bw := signedAdd_work edge.negative (if includeScalar then source.negative else false)
    edge.digits (if includeScalar then source.digits else [])
  have ew : edge.work ≤ BinaryAnchorProgram.coordinateWork (2*bound) := hed.2
  have sw : source.work ≤ BinaryAnchorProgram.coordinateWork bound := hsc.2
  constructor
  · exact bl.trans (by omega)
  · change edge.work + source.work +
      (signedAdd edge.negative (if includeScalar then source.negative else false)
        edge.digits (if includeScalar then source.digits else [])).work + 3 ≤ _
    unfold shiftWork
    omega

def kernel (colors margin edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) : RationalResult :=
  let translated := shift edgeCutoff scalarCutoff includeScalar left right scalar
  let result := BinaryBodyKernel.translated colors margin translated.negative translated.digits output
  ⟨result.data, translated.work + result.work + 2⟩

theorem kernel_value (colors margin edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (hq : 0 < colors) :
    (kernel colors margin edgeCutoff scalarCutoff includeScalar output left right scalar).data.decode =
      RationalProposalProgram.bodyKernel colors margin
        ((left.val:ℤ)-right.val+if includeScalar then (scalar.val:ℤ)-scalarCutoff else 0) (value output) := by
  unfold kernel
  rw [BinaryBodyKernel.translated_value _ _ _ _ _ hq, shift_value]

def integerBound (bound : ℕ) : ℕ := 8*bound+20
def kernelHeight (bound : ℕ) : ℕ := integerBound bound*(integerBound bound+4)
def kernelWork (bound : ℕ) : ℕ := shiftWork bound+BinaryBodyKernel.translatedWork (integerBound bound)+2

theorem kernel_bounds (colors margin edgeCutoff scalarCutoff : ℕ) (includeScalar : Bool) (output : List Bool)
    (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) (bound : ℕ)
    (hq : colors ≤ bound) (hm : margin ≤ bound) (he : edgeCutoff ≤ bound) (hs : scalarCutoff ≤ bound)
    (ho : output.length ≤ bound) :
    HeightBound (kernel colors margin edgeCutoff scalarCutoff includeScalar output left right scalar).data.decode (kernelHeight bound) ∧
      (kernel colors margin edgeCutoff scalarCutoff includeScalar output left right scalar).work ≤ kernelWork bound := by
  let translated := shift edgeCutoff scalarCutoff includeScalar left right scalar
  have hshift := shift_bounds edgeCutoff scalarCutoff includeScalar left right scalar bound he hs
  have hl : translated.digits.length ≤ 4*bound+2 := hshift.1
  have ht := BinaryBodyKernel.translated_bounds colors margin translated.negative translated.digits output (integerBound bound)
    (by unfold integerBound; omega) (by unfold integerBound; omega) (by unfold integerBound; omega) (by unfold integerBound; omega)
  constructor
  · exact ht.1
  · have sw : translated.work ≤ shiftWork bound := hshift.2
    change translated.work + (BinaryBodyKernel.translated colors margin translated.negative translated.digits output).work + 2 ≤ _
    unfold kernelWork
    omega

def evaluate (security colors margin edgeCutoff scalarCutoff bits : ℕ) (includeScalar : Bool) (output : List Bool) : RationalResult :=
  BinarySeedAverage.evaluate security edgeCutoff scalarCutoff bits (kernel colors margin edgeCutoff scalarCutoff includeScalar output)

theorem evaluate_value (security colors margin edgeCutoff scalarCutoff bits : ℕ) (includeScalar : Bool) (output : List Bool)
    (hq : 0 < colors) :
    (evaluate security colors margin edgeCutoff scalarCutoff bits includeScalar output).data.decode =
      ∑ seed : (Window edgeCutoff × Window edgeCutoff) × Window scalarCutoff,
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.1 *
        RationalProposalProgram.gaussianWeight security edgeCutoff bits seed.1.2 *
        RationalProposalProgram.gaussianWeight security scalarCutoff bits seed.2 *
        RationalProposalProgram.bodyKernel colors margin
          (seed.1.1.val-seed.1.2.val+if includeScalar then seed.2.val else 0) (value output) := by
  rw [evaluate, BinarySeedAverage.evaluate_window_value]
  simp only [RationalProposalProgram.gaussianWeight_eq]
  apply Finset.sum_congr rfl
  intro seed _
  rw [kernel_value _ _ _ _ _ _ _ _ _ hq]
  have hl : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-edgeCutoff = seed.1.1.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.1)
  have hr : (((windowIndexEquiv edgeCutoff).symm seed.1.2).val:ℤ)-edgeCutoff = seed.1.2.val :=
    congrArg Subtype.val ((windowIndexEquiv edgeCutoff).apply_symm_apply seed.1.2)
  have hs : (((windowIndexEquiv scalarCutoff).symm seed.2).val:ℤ)-scalarCutoff = seed.2.val :=
    congrArg Subtype.val ((windowIndexEquiv scalarCutoff).apply_symm_apply seed.2)
  have hblur : (((windowIndexEquiv edgeCutoff).symm seed.1.1).val:ℤ)-
      ((windowIndexEquiv edgeCutoff).symm seed.1.2).val = seed.1.1.val-seed.1.2.val := by omega
  rw [hblur, hs]

theorem evaluate_bounds (security colors margin edgeCutoff scalarCutoff bits : ℕ) (includeScalar : Bool) (output : List Bool)
    (bound : ℕ) (hq : colors ≤ bound) (hm : margin ≤ bound) (he : edgeCutoff ≤ bound) (hs : scalarCutoff ≤ bound)
    (ho : output.length ≤ bound) (hec : edgeCutoff ≤ (security+2)^2) (hsc : scalarCutoff ≤ (security+2)^2) :
    HeightBound (evaluate security colors margin edgeCutoff scalarCutoff bits includeScalar output).data.decode
      (BinarySeedAverage.outputHeight security edgeCutoff scalarCutoff bits (kernelHeight bound)) ∧
      (evaluate security colors margin edgeCutoff scalarCutoff bits includeScalar output).work ≤
        BinarySeedAverage.workBound security edgeCutoff scalarCutoff bits (kernelHeight bound) (kernelWork bound) := by
  have hk (left right : Fin (2*edgeCutoff+1)) (scalar : Fin (2*scalarCutoff+1)) :=
    kernel_bounds colors margin edgeCutoff scalarCutoff includeScalar output left right scalar bound hq hm he hs ho
  exact BinarySeedAverage.evaluate_bounds security edgeCutoff scalarCutoff bits _ _ _ hec hsc
    (fun left right scalar => (hk left right scalar).1) (fun left right scalar => (hk left right scalar).2)

def current (security bits : ℕ) (includeScalar : Bool) (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let result := evaluate security parameters.colors margin.count parameters.cutoff window.count bits includeScalar output
  ⟨result.data, parameters.work + window.work + square.work + margin.work + result.work + 5⟩

theorem margin_value (security : ℕ) :
    (multiplyCounter 3 (addCounter (BinaryActivationProgram.cutoff security).count 1).count).count = 3*(security+2)^2 := by
  rw [multiplyCounter_value, addCounter_value, BinaryActivationProgram.cutoff_value, Nat.sub_add_cancel]
  have hb : 0 < (security+2)^2 := by positivity
  omega

theorem current_value (security bits : ℕ) (includeScalar : Bool) (output : List Bool) :
    (current security bits includeScalar output).data.decode = RationalProposalProgram.body security bits includeScalar (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq, _, hc⟩
  have hp : 0 < (BinaryDiffuseCurrent.metadata security).colors := by rw [hq]; exact (Parameters.modulus_spec security).2.pos
  unfold current
  rw [evaluate_value _ _ _ _ _ _ _ _ hp, hq, hc, margin_value, BinaryActivationProgram.cutoff_value]
  unfold RationalProposalProgram.body RationalProposalProgram.seedEvaluate RationalProposalProgram.seedWeight
  rw [PublicParameterProgram.modulus_value]
  have he : ((security+2)^2-1)/2 = DiffuseProfiles.edgeCutoff security := by
    simp only [DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  have hs : (security+2)^2-1 = Parameters.sourceCutoff security-1 := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [he, hs]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security)
    (outputCode : List Bool) (ho : value outputCode = output.val) :
    |((current security bits includeScalar outputCode).data.decode:ℝ)-
      (ProposalPrimary.bodyLaw security includeScalar).weight output| ≤ 3/(2:ℝ)^bits := by
  rw [current_value, ho]
  exact RationalProposalProgram.body_error security bits includeScalar output

noncomputable def integerPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := 8*bound+20
noncomputable def kernelHeightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := integerPolynomial bound*(integerPolynomial bound+4)
noncomputable def shiftWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  BinaryAnchorProgram.coordinateWorkPolynomial (2*bound)+BinaryAnchorProgram.coordinateWorkPolynomial bound+(20*(4*bound+1)+8)+3
noncomputable def kernelWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  shiftWorkPolynomial bound+BinaryBodyKernel.translatedWorkPolynomial (integerPolynomial bound)+2

theorem kernelHeightPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (kernelHeightPolynomial bound).eval security = kernelHeight (bound.eval security) := by
  simp only [kernelHeightPolynomial, integerPolynomial, kernelHeight, integerBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]

theorem kernelWorkPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (kernelWorkPolynomial bound).eval security = kernelWork (bound.eval security) := by
  simp only [kernelWorkPolynomial, shiftWorkPolynomial, integerPolynomial, kernelWork, shiftWork,
    BinaryBodyKernel.translatedWorkPolynomial_eval, BinaryAnchorProgram.coordinateWorkPolynomial,
    BinaryAnchorProgram.coordinateWork, integerBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.parameterPolynomial inputBits+2*(Polynomial.X+2)^2

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial + BinaryActivationProgram.cutoffWorkPolynomial + (2*(Polynomial.X+2)^2+1) +
    (3*(2*(Polynomial.X+2)^2+3)+1) + BinarySeedAverage.workPolynomial ((Polynomial.X+2)^2) ((Polynomial.X+2)^2)
      precision (kernelHeightPolynomial (parameterPolynomial inputBits)) (kernelWorkPolynomial (parameterPolynomial inputBits)) + 5

noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  let gaussian := 500000000*((Polynomial.X+2)^2+precision+2)^6
  count*(gaussian+count*(count*(2*gaussian+kernelHeightPolynomial (parameterPolynomial inputBits)+1)+1)+1)

theorem current_height (security : ℕ) (includeScalar : Bool) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) includeScalar output).data.decode
      ((currentHeightPolynomial precision inputBits).eval security) := by
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let margin := multiplyCounter 3 (addCounter window.count 1).count
  let bound := BinaryDiffuseCurrent.parameterBound security (inputBits.eval security)+2*(security+2)^2
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hcolors, _, hedge⟩
  have hq : parameters.colors = Parameters.modulus security := hcolors
  have he : parameters.cutoff = ((security+2)^2-1)/2 := hedge
  have hs : window.count = (security+2)^2-1 := BinaryActivationProgram.cutoff_value security
  have hm : margin.count = 3*(security+2)^2 := margin_value security
  have hqBound : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hqb : parameters.colors ≤ bound := by rw [hq]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hmb : margin.count ≤ bound := by rw [hm]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hec : parameters.cutoff ≤ (security+2)^2 := by rw [he]; omega
  have hsc : window.count ≤ (security+2)^2 := by rw [hs]; omega
  have heb : parameters.cutoff ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hsb : window.count ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hob : output.length ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hh := (evaluate_bounds security parameters.colors margin.count parameters.cutoff window.count
    (precision.eval security) includeScalar output bound hqb hmb heb hsb hob hec hsc).1
  apply hh.mono
  simp only [currentHeightPolynomial, kernelHeightPolynomial_eval, parameterPolynomial,
    BinaryDiffuseCurrent.parameterPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  change BinarySeedAverage.outputHeight security parameters.cutoff window.count (precision.eval security) (kernelHeight bound) ≤
    BinarySeedAverage.outputHeight security ((security+2)^2) ((security+2)^2) (precision.eval security) (kernelHeight bound)
  unfold BinarySeedAverage.outputHeight BinaryWindowAverage.sumHeight BinarySeedAverage.innerHeight
    BinaryGaussianAverage.sumHeight BinaryGaussianAverage.termHeight
  gcongr

theorem current_polynomial_work (security : ℕ) (includeScalar : Bool) (output : List Bool)
    (precision inputBits : Polynomial ℕ) (ho : output.length ≤ inputBits.eval security) :
    (current security (precision.eval security) includeScalar output).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  let parameters := BinaryDiffuseCurrent.metadata security
  let window := BinaryActivationProgram.cutoff security
  let square := addCounter window.count 1
  let margin := multiplyCounter 3 square.count
  let bound := BinaryDiffuseCurrent.parameterBound security (inputBits.eval security)+2*(security+2)^2
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hcolors, _, hedge⟩
  have hq : parameters.colors = Parameters.modulus security := hcolors
  have he : parameters.cutoff = ((security+2)^2-1)/2 := hedge
  have hs : window.count = (security+2)^2-1 := BinaryActivationProgram.cutoff_value security
  have hsq : square.count = (security+2)^2 := by
    have hpositive : 1 ≤ (security+2)^2 := Nat.succ_le_of_lt (pow_pos (Nat.zero_lt_succ (security+1)) 2)
    exact (addCounter_value window.count 1).trans
      ((congrArg (fun count => count+1) hs).trans (Nat.sub_add_cancel hpositive))
  have hm : margin.count = 3*(security+2)^2 := margin_value security
  have hqBound : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hqb : parameters.colors ≤ bound := by rw [hq]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hmb : margin.count ≤ bound := by rw [hm]; unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hec : parameters.cutoff ≤ (security+2)^2 := by rw [he]; omega
  have hsc : window.count ≤ (security+2)^2 := by rw [hs]; omega
  have heb : parameters.cutoff ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hsb : window.count ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have hob : output.length ≤ bound := by unfold bound BinaryDiffuseCurrent.parameterBound; omega
  have we := (evaluate_bounds security parameters.colors margin.count parameters.cutoff window.count
    (precision.eval security) includeScalar output bound hqb hmb heb hsb hob hec hsc).2
  have hfinal := BinarySeedAverage.workBound_mono (security := security) (bits := precision.eval security) hec hsc
    (le_refl (kernelHeight bound)) (le_refl (kernelWork bound))
  have wparameters : parameters.work ≤ BinaryDiffuseCurrent.metadataWork security := BinaryDiffuseCurrent.metadata_work security
  have wwindow : window.work ≤ BinaryActivationProgram.cutoffWork security := BinaryActivationProgram.cutoff_work security
  have wsquare : square.work ≤ 2*(security+2)^2+1 := by
    rw [addCounter_work]
    omega
  have wmargin : margin.work = 3*(2*(security+2)^2+3)+1 :=
    (multiplyCounter_work 3 square.count).trans (congrArg (fun count => 3*(2*count+3)+1) hsq)
  have wresult : (evaluate security parameters.colors margin.count parameters.cutoff window.count
      (precision.eval security) includeScalar output).work ≤
      BinarySeedAverage.workBound security ((security+2)^2) ((security+2)^2) (precision.eval security) (kernelHeight bound) (kernelWork bound) := we.trans hfinal
  have htotal : (current security (precision.eval security) includeScalar output).work ≤
      BinaryDiffuseCurrent.metadataWork security+BinaryActivationProgram.cutoffWork security+(2*(security+2)^2+1)+
        (3*(2*(security+2)^2+3)+1)+BinarySeedAverage.workBound security ((security+2)^2) ((security+2)^2)
          (precision.eval security) (kernelHeight bound) (kernelWork bound)+5 := by
    change parameters.work+window.work+square.work+margin.work+
      (evaluate security parameters.colors margin.count parameters.cutoff window.count
        (precision.eval security) includeScalar output).work+5 ≤ _
    omega
  convert htotal using 1
  simp only [currentWorkPolynomial, BinaryDiffuseCurrent.metadataWorkPolynomial_eval,
    BinaryActivationProgram.cutoffWorkPolynomial_eval, BinarySeedAverage.workPolynomial_eval,
    kernelHeightPolynomial_eval, kernelWorkPolynomial_eval, parameterPolynomial,
    BinaryDiffuseCurrent.parameterPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  rfl

end
end CurrentAFT.BinaryBodyProgram

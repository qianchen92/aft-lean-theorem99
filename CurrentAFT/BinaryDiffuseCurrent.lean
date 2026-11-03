import CurrentAFT.BinaryDiffuseProgram

/-! # Self-generated current parameters for the binary diffuse leaf

The least prime, anchor width and edge window are calculated by genuine
counter/list programs before evaluating the local Gaussian average.
-/
namespace CurrentAFT.BinaryDiffuseCurrent
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  addCounter powerCounter differenceCounter divideCounter PublicParameterProgram.modulus

private opaque checkedPower (base exponent : ℕ) :
    {result : UnaryCounterResult // result.count = base^exponent ∧ result.work ≤ powerCounterWork base exponent} :=
  ⟨powerCounter base exponent, powerCounter_value base exponent, powerCounter_work base exponent⟩

structure Metadata where
  colors : ℕ
  width : ℕ
  cutoff : ℕ
  work : ℕ

def metadata (security : ℕ) : Metadata :=
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := (checkedPower base.count 48).val
  let square := (checkedPower base.count 2).val
  let last := differenceCounter square.count 1
  let half := divideCounter last.count 2
  ⟨colors.count, width.count, half.quotient,
    colors.work + base.work + width.work + square.work + last.work + half.work + 6⟩

theorem metadata_value (security : ℕ) :
    (metadata security).colors = Parameters.modulus security ∧
      (metadata security).width = (security+2)^48 ∧
      (metadata security).cutoff = ((security+2)^2-1)/2 := by
  let base := addCounter security 2
  let width := (checkedPower base.count 48).val
  let square := (checkedPower base.count 2).val
  let last := differenceCounter square.count 1
  have hb : base.count = security+2 := addCounter_value security 2
  have hw : width.count = (security+2)^48 :=
    (checkedPower base.count 48).property.1.trans (congrArg (·^48) hb)
  have hs : square.count = (security+2)^2 :=
    (checkedPower base.count 2).property.1.trans (congrArg (·^2) hb)
  have hl : last.count = (security+2)^2-1 :=
    (differenceCounter_value square.count 1).trans (congrArg (·-1) hs)
  exact ⟨PublicParameterProgram.modulus_value security, hw,
    (divideCounter_value last.count 2 (by omega)).1.trans (congrArg (·/2) hl)⟩

def metadataWork (security : ℕ) : ℕ :=
  PublicParameterProgram.workBound security + 2*security+1 + powerCounterWork (security+2) 48 +
    powerCounterWork (security+2) 2 + (2*(security+2)^2+1) +
    500*((security+2)^2+4)^2 + 6

theorem metadata_work (security : ℕ) : (metadata security).work ≤ metadataWork security := by
  let colors := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := (checkedPower base.count 48).val
  let square := (checkedPower base.count 2).val
  let last := differenceCounter square.count 1
  let half := divideCounter last.count 2
  have hb : base.count = security+2 := addCounter_value security 2
  have hs : square.count = (security+2)^2 :=
    (checkedPower base.count 2).property.1.trans (congrArg (·^2) hb)
  have hl : last.count = (security+2)^2-1 :=
    (differenceCounter_value square.count 1).trans (congrArg (·-1) hs)
  have wc : colors.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have wb : base.work = 2*security+1 := addCounter_work security 2
  have ww : width.work ≤ powerCounterWork (security+2) 48 :=
    (checkedPower base.count 48).property.2.trans_eq (congrArg (fun number => powerCounterWork number 48) hb)
  have ws : square.work ≤ powerCounterWork (security+2) 2 :=
    (checkedPower base.count 2).property.2.trans_eq (congrArg (fun number => powerCounterWork number 2) hb)
  have wl : last.work ≤ 2*(security+2)^2+1 :=
    (differenceCounter_work square.count 1).trans_eq (congrArg (fun number => 2*number+1) hs)
  have wh : half.work ≤ 500*((security+2)^2+4)^2 :=
    (divideCounter_work last.count 2 (by omega)).trans
      (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
  change colors.work + base.work + width.work + square.work + last.work + half.work + 6 ≤ _
  unfold metadataWork
  omega

def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let parameters := metadata security
  let result := BinaryDiffuseProgram.evaluate security parameters.colors parameters.width parameters.cutoff bits primary
    sourceSign source first second
  ⟨result.data, parameters.work + result.work + 2⟩

theorem current_value (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) :
    (current security bits primary sourceSign source first second).data.decode =
      LocalDiffuseProgram.current security bits primary (signedValue sourceSign source) (value first) (value second) := by
  rcases metadata_value security with ⟨hq, hw, hc⟩
  unfold current
  rw [BinaryDiffuseProgram.evaluate_value, hq, hw, hc]
  unfold LocalDiffuseProgram.current
  rw [PublicParameterProgram.modulus_value]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (sourceSign : Bool) (sourceCode firstCode secondCode : List Bool)
    (hs : signedValue sourceSign sourceCode = source.val)
    (hf : value firstCode = first.val) (ht : value secondCode = second.val) :
    |((current security bits primary.val sourceSign sourceCode firstCode secondCode).data.decode : ℝ) -
      (LocalReferenceEnergy.diffusePairAt security primary source).weight (first, second)| ≤ 2/(2:ℝ)^bits := by
  rw [current_value, hs, hf, ht]
  exact LocalDiffuseProgram.current_error security bits primary first second source

theorem current_work (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) :
    (current security bits primary sourceSign source first second).work ≤
      metadataWork security + BinaryDiffuseProgram.evaluateWork security (((security+2)^2-1)/2) bits
        (BinaryDiffuseProgram.inputBound (Parameters.modulus security) ((security+2)^48) primary
          (((security+2)^2-1)/2) source first second) + 2 := by
  rcases metadata_value security with ⟨hq, hw, hc⟩
  have hcut : (metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have we := (BinaryDiffuseProgram.evaluate_bounds security (metadata security).colors (metadata security).width
    (metadata security).cutoff bits primary sourceSign source first second hcut).2
  have wm := metadata_work security
  conv_rhs at we => rw [hq, hw, hc]
  unfold current
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add wm we) 2

def parameterBound (security inputBits : ℕ) : ℕ :=
  2*131072*(security+2)^64 + (security+2)^48 + 2*(security+2)^2 + 3*inputBits + 1

theorem input_bound (security : ℕ) (primary : FirstHistogram.Palette security)
    (source first second : List Bool) (inputBits : ℕ)
    (hs : source.length ≤ inputBits) (hf : first.length ≤ inputBits) (ht : second.length ≤ inputBits) :
    BinaryDiffuseProgram.inputBound (Parameters.modulus security) ((security+2)^48) primary.val
      (((security+2)^2-1)/2) source first second ≤ parameterBound security inputBits := by
  have hq : Parameters.modulus security ≤ 131072*(security+2)^64 := by
    simpa only [Parameters.base] using (Parameters.modulus_bounds security).2
  have hp := primary.isLt
  have hc : ((security+2)^2-1)/2 ≤ (security+2)^2 := by omega
  unfold BinaryDiffuseProgram.inputBound parameterBound
  omega

def currentHeight (security bits inputBits : ℕ) : ℕ :=
  BinaryDiffuseProgram.sumHeight (2*(security+2)^2+1) (parameterBound security inputBits)
    (BinaryDiffuseProgram.gaussianHeight security bits)

theorem current_height (security bits : ℕ) (primary : FirstHistogram.Palette security)
    (sourceSign : Bool) (source first second : List Bool) (inputBits : ℕ)
    (hs : source.length ≤ inputBits) (hf : first.length ≤ inputBits) (ht : second.length ≤ inputBits) :
    HeightBound (current security bits primary.val sourceSign source first second).data.decode
      (currentHeight security bits inputBits) := by
  rcases metadata_value security with ⟨hq, hw, hc⟩
  have hcut : (metadata security).cutoff ≤ (security+2)^2 := by rw [hc]; omega
  have hh := (BinaryDiffuseProgram.evaluate_bounds security (metadata security).colors (metadata security).width
    (metadata security).cutoff bits primary.val sourceSign source first second hcut).1
  conv_rhs at hh => rw [hq, hw, hc]
  apply hh.mono
  have hb := input_bound security primary source first second inputBits hs hf ht
  have hn : 2*(((security+2)^2-1)/2)+1 ≤ 2*(security+2)^2+1 := by omega
  unfold currentHeight BinaryDiffuseProgram.sumHeight BinaryDiffuseProgram.termHeight
    BinaryDiffuseProgram.averageHeight BinaryDiffuseProgram.coinIntegerBound
  gcongr

noncomputable def metadataWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial + 2*Polynomial.X+1 + 49*(6*(Polynomial.X+3)^50+4) +
    3*(6*(Polynomial.X+3)^4+4) + (2*(Polynomial.X+2)^2+1) +
    500*((Polynomial.X+2)^2+4)^2 + 6

theorem metadataWorkPolynomial_eval (security : ℕ) :
    metadataWorkPolynomial.eval security = metadataWork security := by
  simp only [metadataWorkPolynomial, metadataWork, PublicParameterProgram.workPolynomial_eval,
    powerCounterWork, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  norm_num
  ring

noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*131072*(Polynomial.X+2)^64 + (Polynomial.X+2)^48 + 2*(Polynomial.X+2)^2 + 3*inputBits + 1

theorem parameterPolynomial_eval (inputBits : Polynomial ℕ) (security : ℕ) :
    (parameterPolynomial inputBits).eval security = parameterBound security (inputBits.eval security) := by
  simp only [parameterPolynomial, parameterBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  metadataWorkPolynomial + BinaryDiffuseProgram.evaluateWorkPolynomial ((Polynomial.X+2)^2) precision
    (parameterPolynomial inputBits) + 2

theorem currentWorkPolynomial_eval (precision inputBits : Polynomial ℕ) (security : ℕ) :
    (currentWorkPolynomial precision inputBits).eval security =
      metadataWork security + BinaryDiffuseProgram.evaluateWork security ((security+2)^2)
        (precision.eval security) (parameterBound security (inputBits.eval security)) + 2 := by
  simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat,
    metadataWorkPolynomial_eval, BinaryDiffuseProgram.evaluateWorkPolynomial_eval,
    parameterPolynomial_eval, Polynomial.eval_pow, Polynomial.eval_X]

theorem current_polynomial_work (security : ℕ) (primary : FirstHistogram.Palette security)
    (sourceSign : Bool) (source first second : List Bool) (precision inputBits : Polynomial ℕ)
    (hs : source.length ≤ inputBits.eval security) (hf : first.length ≤ inputBits.eval security)
    (ht : second.length ≤ inputBits.eval security) :
    (current security (precision.eval security) primary.val sourceSign source first second).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  rw [currentWorkPolynomial_eval]
  have he := BinaryDiffuseProgram.evaluateWork_mono (security := security) (bits := precision.eval security)
    (show ((security+2)^2-1)/2 ≤ (security+2)^2 by omega)
    (input_bound security primary source first second (inputBits.eval security) hs hf ht)
  exact (current_work security (precision.eval security) primary.val sourceSign source first second).trans
    (Nat.add_le_add_right (Nat.add_le_add le_rfl he) 2)

end
end CurrentAFT.BinaryDiffuseCurrent

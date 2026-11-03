import CurrentAFT.BinaryRootProfile

/-! # Polynomial resources for every actual pre-root law -/
namespace CurrentAFT.BinaryRootProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
  BinaryPaletteLookup.current BinaryShiftedSafeProfile.current PublicParameterProgram.modulus
  BinaryActivationProgram.cutoff
noncomputable section

def cutoffPolynomial : Polynomial ℕ := (Polynomial.X+2)^2
def scalarBitsPolynomial : Polynomial ℕ := 2*cutoffPolynomial+1

def attachmentAtHeightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedSafeProfile.heightPolynomial scalarBitsPolynomial inputBits
def attachmentAtWorkPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryAnchorProgram.coordinateWorkPolynomial cutoffPolynomial+
    BinaryShiftedSafeProfile.workPolynomial scalarBitsPolynomial inputBits+2

theorem attachmentAt_bounds (security cutoff : ℕ) (inputBits : Polynomial ℕ)
    (output : List Bool) (index : Fin (2*cutoff+1)) (hcutoff : cutoff≤(security+2)^2)
    (houtput : output.length ≤ inputBits.eval security) :
    HeightBound (attachmentAt security cutoff output index).data.decode ((attachmentAtHeightPolynomial inputBits).eval security) ∧
      (attachmentAt security cutoff output index).work≤(attachmentAtWorkPolynomial inputBits).eval security := by
  let scalar := BinaryAnchorProgram.coordinate cutoff index.val
  have hs := BinaryAnchorProgram.coordinate_bounds cutoff index.val ((security+2)^2) hcutoff (by have := index.isLt; omega)
  have hl : scalar.digits.length≤scalarBitsPolynomial.eval security := by
    simpa only [scalarBitsPolynomial, cutoffPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] using hs.1
  have hh := BinaryShiftedSafeProfile.current_bounds security ⟨scalar.negative,scalar.digits⟩ output scalarBitsPolynomial inputBits hl houtput
  constructor
  · exact hh.1
  · change scalar.work+(BinaryShiftedSafeProfile.current security ⟨scalar.negative,scalar.digits⟩ output).work+2≤_
    have hw : scalar.work≤(BinaryAnchorProgram.coordinateWorkPolynomial cutoffPolynomial).eval security := by
      simpa only [BinaryAnchorProgram.coordinateWorkPolynomial, BinaryAnchorProgram.coordinateWork, cutoffPolynomial,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
        Polynomial.eval_one] using hs.2
    simpa only [attachmentAtWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat] using
      Nat.add_le_add_right (Nat.add_le_add hw hh.2) 2

def attachmentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  (2*cutoffPolynomial+1)*(500000000*((Polynomial.X+2)^2+precision+2)^6+attachmentAtHeightPolynomial inputBits+1)
def attachmentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.cutoffWorkPolynomial+
    BinaryWindowAverage.evaluateWorkPolynomial cutoffPolynomial precision (attachmentAtHeightPolynomial inputBits)
      (attachmentAtWorkPolynomial inputBits)+2

theorem attachment_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (output : List Bool)
    (houtput : output.length ≤ inputBits.eval security) :
    HeightBound (attachment security (precision.eval security) output).data.decode ((attachmentHeightPolynomial precision inputBits).eval security) ∧
      (attachment security (precision.eval security) output).work≤(attachmentWorkPolynomial precision inputBits).eval security := by
  let window := BinaryActivationProgram.cutoff security
  have hc : window.count≤(security+2)^2 := by rw [BinaryActivationProgram.cutoff_value]; omega
  have ht (index : Fin (2*window.count+1)) := attachmentAt_bounds security window.count inputBits output index hc houtput
  have h := BinaryWindowAverage.evaluate_bounds security window.count (precision.eval security)
    (attachmentAt security window.count output) ((attachmentAtHeightPolynomial inputBits).eval security)
    ((attachmentAtWorkPolynomial inputBits).eval security) hc (fun index => (ht index).1) (fun index => (ht index).2)
  have wh := BinaryActivationProgram.cutoff_work security
  constructor
  · apply h.1.mono
    simp only [attachmentHeightPolynomial, cutoffPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one,
      BinaryWindowAverage.sumHeight, BinaryGaussianAverage.gaussianHeight, CurrentGaussianBits.budget]
    gcongr
  · change window.work+(BinaryWindowAverage.evaluate security window.count (precision.eval security)
      (attachmentAt security window.count output)).work+2≤_
    rw [attachmentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_ofNat,
      BinaryActivationProgram.cutoffWorkPolynomial_eval, BinaryWindowAverage.evaluateWorkPolynomial_eval]
    have wm : BinaryWindowAverage.evaluateWork security window.count (precision.eval security)
        ((attachmentAtHeightPolynomial inputBits).eval security) ((attachmentAtWorkPolynomial inputBits).eval security) ≤
      BinaryWindowAverage.evaluateWork security (cutoffPolynomial.eval security) (precision.eval security)
        ((attachmentAtHeightPolynomial inputBits).eval security) ((attachmentAtWorkPolynomial inputBits).eval security) := by
      unfold BinaryWindowAverage.evaluateWork
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      exact BinaryWindowAverage.sumWork_mono (by simpa only [cutoffPolynomial, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1) le_rfl le_rfl le_rfl
    exact Nat.add_le_add_right (Nat.add_le_add wh (h.2.trans wm)) 2

def freeHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+1)
def freeWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let H := BinaryReferenceTables.heightPolynomial precision
  BinaryReferenceTables.currentWorkPolynomial precision+
    Q*(50*(Q+1)^2+48*(Q+inputBits)+42+3*Q+3+primitiveWorkPolynomial ((Q+1)*(H+1))+2)+4

theorem free_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (queue : IntegerBits) (output : List Bool)
    (houtput : output.length ≤ inputBits.eval security) :
    HeightBound (preRoot security (precision.eval security) .free queue output).data.decode ((freeHeightPolynomial precision).eval security) ∧
      (preRoot security (precision.eval security) .free queue output).work≤(freeWorkPolynomial precision inputBits).eval security := by
  let reference := BinaryReferenceTables.current security (precision.eval security)
  have hr := BinaryReferenceTables.current_bounds security precision
  have h := BinaryPaletteLookup.current_bounds reference.center output (inputBits.eval security)
    ((BinaryReferenceTables.heightPolynomial precision).eval security) houtput hr.2.1
  have hq := BinaryFirstInverseProgram.colors_bound security
  constructor
  · apply h.1.mono
    simp only [freeHeightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · change reference.work+(BinaryPaletteLookup.current reference.center output).work+2≤_
    simp only [freeWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, primitiveWorkPolynomial_eval]
    have hw : BinaryPaletteLookup.work (colors security) (inputBits.eval security)
        ((BinaryReferenceTables.heightPolynomial precision).eval security) ≤
      BinaryFirstInverseProgram.colorsPolynomial.eval security*
        (50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
          48*(BinaryFirstInverseProgram.colorsPolynomial.eval security+inputBits.eval security)+42+
          3*BinaryFirstInverseProgram.colorsPolynomial.eval security+3+
          primitiveWorkBound ((BinaryFirstInverseProgram.colorsPolynomial.eval security+1)*
            ((BinaryReferenceTables.heightPolynomial precision).eval security+1))+2)+2 := by
      unfold BinaryPaletteLookup.work BinaryPaletteLookup.termWork primitiveWorkBound
      gcongr
    have wr : reference.work≤(BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
    have wh : (BinaryPaletteLookup.current reference.center output).work ≤
        BinaryPaletteLookup.work (colors security) (inputBits.eval security)
          ((BinaryReferenceTables.heightPolynomial precision).eval security) := h.2
    have wt := wh.trans hw
    omega

def preRootHeightPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  freeHeightPolynomial precision+attachmentHeightPolynomial precision inputBits+
    BinaryShiftedSafeProfile.heightPolynomial queueBits inputBits
def preRootWorkPolynomial (precision queueBits inputBits : Polynomial ℕ) : Polynomial ℕ :=
  freeWorkPolynomial precision inputBits+attachmentWorkPolynomial precision inputBits+
    BinaryShiftedSafeProfile.workPolynomial queueBits inputBits

theorem preRoot_bounds (security : ℕ) (precision queueBits inputBits : Polynomial ℕ)
    (role : BodyRole) (queue : IntegerBits) (output : List Bool)
    (hqueue : queue.digits.length ≤ queueBits.eval security) (houtput : output.length ≤ inputBits.eval security) :
    HeightBound (preRoot security (precision.eval security) role queue output).data.decode
      ((preRootHeightPolynomial precision queueBits inputBits).eval security) ∧
      (preRoot security (precision.eval security) role queue output).work≤
        (preRootWorkPolynomial precision queueBits inputBits).eval security := by
  have hfree := free_bounds security precision inputBits queue output houtput
  have hatt := attachment_bounds security precision inputBits output houtput
  have hque := BinaryShiftedSafeProfile.current_bounds security queue output queueBits inputBits hqueue houtput
  have heH : (preRootHeightPolynomial precision queueBits inputBits).eval security =
      (freeHeightPolynomial precision).eval security+(attachmentHeightPolynomial precision inputBits).eval security+
        (BinaryShiftedSafeProfile.heightPolynomial queueBits inputBits).eval security := by
    simp only [preRootHeightPolynomial, Polynomial.eval_add]
  have heW : (preRootWorkPolynomial precision queueBits inputBits).eval security =
      (freeWorkPolynomial precision inputBits).eval security+(attachmentWorkPolynomial precision inputBits).eval security+
        (BinaryShiftedSafeProfile.workPolynomial queueBits inputBits).eval security := by
    simp only [preRootWorkPolynomial, Polynomial.eval_add]
  cases role with
  | free => exact ⟨hfree.1.mono (by rw [heH]; omega),hfree.2.trans (by rw [heW]; omega)⟩
  | attachment => exact ⟨hatt.1.mono (by rw [heH]; omega),hatt.2.trans (by rw [heW]; omega)⟩
  | queue => exact ⟨hque.1.mono (by rw [heH]; omega),hque.2.trans (by rw [heW]; omega)⟩

end
end CurrentAFT.BinaryRootProfile

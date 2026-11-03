import CurrentAFT.RationalRootProfileProgram
import CurrentAFT.RationalRootConvolutionCongr
import CurrentAFT.BinaryMassLiftInput
import CurrentAFT.BinaryShiftedSafeProfile
import CurrentAFT.BinaryReferenceTables
import AFT.BinaryChartProjectionCost

/-! # Executed shifted and averaged profiles for the actual root channels -/
namespace CurrentAFT.BinaryRootProfile
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram FiniteConvolutionProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryActivationProgram.cutoff
  BinaryReferenceTables.current BinaryShiftedSafeProfile.current BinaryRootConvolution.current
  BinaryMassLiftInput.current IntegerBits.residue

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def attachmentAt (security cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := BinaryAnchorProgram.coordinate cutoff index.val
  let result := BinaryShiftedSafeProfile.current security ⟨scalar.negative, scalar.digits⟩ output
  ⟨result.data, scalar.work+result.work+2⟩

theorem attachmentAt_value (security cutoff : ℕ) (output : List Bool) (index : Fin (2*cutoff+1)) :
    (attachmentAt security cutoff output index).data.decode =
      RationalBackgroundProfiles.shifted security ((index.val:ℤ)-cutoff) (value output) := by
  simp only [attachmentAt, BinaryShiftedSafeProfile.current_value, IntegerBits.decode,
    BinaryAnchorProgram.coordinate_value]

def attachment (security bits : ℕ) (output : List Bool) : RationalResult :=
  let window := BinaryActivationProgram.cutoff security
  let result := BinaryWindowAverage.evaluate security window.count bits (attachmentAt security window.count output)
  ⟨result.data, window.work+result.work+2⟩

theorem attachment_value (security bits : ℕ) (output : List Bool) :
    (attachment security bits output).data.decode =
      RationalRootProfileProgram.attachment security bits (value output) := by
  unfold attachment
  rw [BinaryWindowAverage.evaluate_value, BinaryActivationProgram.cutoff_value]
  simp only [attachmentAt_value]
  unfold RationalRootProfileProgram.attachment
  have hreindex := (windowIndexEquiv ((security+2)^2-1)).sum_comp (fun scalar : Window ((security+2)^2-1) =>
    RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits scalar *
      RationalBackgroundProfiles.shifted security scalar.val (value output))
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro index _
  rw [RationalProposalProgram.gaussianWeight_eq]
  rfl

def preRoot (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  match role with
  | .free =>
    let reference := BinaryReferenceTables.current security bits
    let result := BinaryPaletteLookup.current reference.center output
    ⟨result.data, reference.work+result.work+2⟩
  | .attachment => attachment security bits output
  | .queue => BinaryShiftedSafeProfile.current security queue output

theorem preRoot_value (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool)
    (houtput : value output<colors security) :
    (preRoot security bits role queue output).data.decode =
      RationalRootProfileProgram.preRoot security bits role queue.decode (value output) := by
  cases role with
  | free =>
    change (BinaryPaletteLookup.current (BinaryReferenceTables.current security bits).center output).data.decode = _
    rw [BinaryPaletteLookup.current_value _ output ⟨value output,houtput⟩ rfl,
      BinaryReferenceTables.center_value]
    rfl
  | attachment => exact attachment_value security bits output
  | queue => exact BinaryShiftedSafeProfile.current_value security queue output

def key (security : ℕ) (root : IntegerBits) (output : List Bool) : BinaryArithmetic.Result :=
  let modulus := PublicParameterProgram.modulus security
  let code := canonicalCounter modulus.count
  let difference := signedAdd false (!root.negative) output root.digits
  let residue := IntegerBits.residue ⟨difference.negative,difference.digits⟩ code.digits
  ⟨residue.digits, modulus.work+code.work+difference.work+residue.work+4⟩

theorem key_value (security : ℕ) (root : IntegerBits) (output : List Bool) :
    value (key security root output).digits =
      RationalBackgroundProfiles.inverseShift security root.decode (value output) := by
  have hq : 0<(PublicParameterProgram.modulus security).count := by
    rw [PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  unfold key
  have h := IntegerBits.residue_value
    (⟨(signedAdd false (!root.negative) output root.digits).negative,
      (signedAdd false (!root.negative) output root.digits).digits⟩:IntegerBits)
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits
    (by rw [canonicalCounter_value]; exact hq)
  rw [IntegerBits.decode, signedAdd_value, signedValue_not] at h
  simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value] at h
  have hn := congrArg Int.toNat h
  simpa only [Int.toNat_natCast, RationalBackgroundProfiles.inverseShift, RationalBackgroundProfiles.colors,
    IntegerBits.decode, signedValue, sub_eq_add_neg] using hn

theorem key_lt (security : ℕ) (root : IntegerBits) (output : List Bool) :
    value (key security root output).digits<colors security := by
  rw [key_value]
  exact RationalBackgroundProfiles.inverseShift_lt security (value output) root.decode

def shifted (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) : RationalResult :=
  let index := key security root output
  let result := preRoot security bits role queue index.digits
  ⟨result.data,index.work+result.work+2⟩

theorem shifted_value (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) :
    (shifted security bits role queue root output).data.decode =
      RationalRootProfileProgram.shifted security bits role queue.decode root.decode (value output) := by
  unfold shifted
  rw [preRoot_value security bits role queue _ (key_lt security root output), key_value]
  rfl

def profileAt (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := preRoot security bits role queue code.digits
  ⟨result.data,code.work+result.work+2⟩

theorem profileAt_value (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : Fin (colors security)) :
    (profileAt security bits role queue output).data.decode =
      RationalRootProfileProgram.preRoot security bits role queue.decode output.val := by
  unfold profileAt
  rw [preRoot_value _ _ _ _ _ (by rw [canonicalCounter_value]; exact output.isLt), canonicalCounter_value]

def mean (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let profile := buildArray modulus.count (profileAt security bits role queue)
  let result := BinaryRootConvolution.current security bits profile.data output
  ⟨result.data,modulus.work+profile.work+result.work+3⟩

theorem mean_value (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) :
    (mean security bits role queue output).data.decode =
      RationalRootProfileProgram.mean security bits role queue.decode (value output) := by
  change (BinaryRootConvolution.current _ _ _ _).data.decode = _
  rw [BinaryRootConvolution.current_of_entries _ _ _ _ (RationalRootProfileProgram.preRoot security bits role queue.decode)
    (fun color => by rw [buildArray_get, profileAt_value])]
  rfl

def deviation (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) : RationalResult :=
  let first := shifted security bits role queue root output
  let second := mean security bits role queue output
  let result := difference first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩

theorem deviation_value (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits) (output : List Bool) :
    (deviation security bits role queue root output).data.decode =
      RationalRootProfileProgram.deviation security bits role queue.decode root.decode (value output) := by
  simp only [deviation, difference_value, shifted_value, mean_value, RationalRootProfileProgram.deviation]

def meanDeviation (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := ofCounter modulus.count
  let reciprocal := RationalBits.inverse encoded.data
  let average := mean security bits role queue output
  let result := difference average.data reciprocal.data
  ⟨result.data,modulus.work+encoded.work+reciprocal.work+average.work+result.work+5⟩

theorem meanDeviation_value (security bits : ℕ) (role : BodyRole) (queue : IntegerBits) (output : List Bool) :
    (meanDeviation security bits role queue output).data.decode =
      RationalRootProfileProgram.meanDeviation security bits role queue.decode (value output) := by
  simp only [meanDeviation, difference_value, mean_value, inverse_value, ofCounter_value,
    RationalRootProfileProgram.meanDeviation, one_div]

def densityInput (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := deviation security bits role queue root code.digits
  ⟨result.data,code.work+result.work+2⟩

def meanDensityInput (security bits : ℕ) (role : BodyRole) (queue : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := meanDeviation security bits role queue code.digits
  ⟨result.data,code.work+result.work+2⟩

def firstDensity (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (densityInput security bits role queue root) output

def meanDensity (security bits : ℕ) (role : BodyRole) (queue : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (meanDensityInput security bits role queue) output

theorem firstDensity_value (security bits : ℕ) (role : BodyRole) (queue root : IntegerBits)
    (output : Fin (colors security)) :
    (firstDensity security bits role queue root output).data.decode =
      RationalRootProfileProgram.firstDensity security bits role queue.decode root.decode output.val := by
  apply BinaryMassLiftInput.current_value
  intro color
  simp only [densityInput, deviation_value, canonicalCounter_value]

theorem meanDensity_value (security bits : ℕ) (role : BodyRole) (queue : IntegerBits)
    (output : Fin (colors security)) :
    (meanDensity security bits role queue output).data.decode =
      RationalRootProfileProgram.meanDensity security bits role queue.decode output.val := by
  apply BinaryMassLiftInput.current_value
  intro color
  simp only [meanDensityInput, meanDeviation_value, canonicalCounter_value]

end CurrentAFT.BinaryRootProfile

import AFT.ActualAnchorProgram

/-! # Rational computation of the actual response matrix -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def paletteSignProgram (modulus color : ℕ) : ℚ :=
  if 2*color < modulus-1 then -1 else if modulus-1 < 2*color then 1 else 0

def actualNormalizedSignProgram (constant n : ℕ) (output : ℤ) : ℚ :=
  actualActivationInverseApprox constant n n*
    (actualMixedSliceProgram constant n true true output-actualMixedSliceProgram constant n false true output)-
    (actualMixedSliceProgram constant n true false output-actualMixedSliceProgram constant n false false output)

def actualResponseProgram (constant n input output : ℕ) : ℚ :=
  (if input=output then 1 else 0)+
    paletteSignProgram (ParameterProgram.modulus n).value input*actualNormalizedSignProgram constant n output+
    actualAnchorProgram constant n false input output-actualAnchorProgram constant n true input output

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance responseProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem paletteSignProgram_cast (modulus : ℕ) (color : Fin modulus) :
    (paletteSignProgram modulus color.val : ℝ)=paletteSign modulus color := by
  unfold paletteSignProgram paletteSign
  split_ifs <;> norm_num

def actualSignedSliceMean (constant : ℝ) (n : ℕ) (positive shifted : Bool) (output : ℤ) : ℝ :=
  TrimmedSlice.mixedLaw (Parameters.modulus n) (boundaryHalf constant n)
    (if positive then startsPlus constant n else startsMinus constant n)
    (if shifted then pairSourceShift constant n else fun _ => 0)
    (pairSourceLaw constant n).weight (Parameters.anchorWidth n) output

def actualNormalizedSign (constant : ℝ) (n : ℕ) (output : ℤ) : ℝ :=
  (v7Activation constant n)⁻¹*
    (actualSignedSliceMean constant n true true output-actualSignedSliceMean constant n false true output)-
    (actualSignedSliceMean constant n true false output-actualSignedSliceMean constant n false false output)

theorem actualNormalizedSign_eq (constant : ℝ) (n : ℕ) (hc : 1≤constant) (hn : 1≤n)
    (output : Fin (Parameters.modulus n)) :
    actualNormalizedSign constant n output.val=(v7Activation constant n)⁻¹*
      signResponse n constant (boundaryHalf constant n) (startsPlus constant n) (startsMinus constant n)
        (pairSourceShift constant n) (pairSourceLaw constant n) output := by
  have ha : v7Activation constant n≠0 := ne_of_gt (activation_positive _ _ _ _
    (legFeatureCount_positive constant n hc hn))
  simp only [actualNormalizedSign,actualSignedSliceMean,signResponse,TrimmedSlice.actualSignResponse,
    calibratedSignResponse,Bool.false_eq_true,if_false,if_true]
  field_simp

theorem approximation_sub_error (a b c d : ℝ) : |(a-b)-(c-d)|≤|a-c|+|b-d| := by
  rw [show (a-b)-(c-d)=(a-c)-(b-d) by ring]
  exact abs_sub _ _

theorem approximation_mul_error (a b c d : ℝ) : |a*b-c*d|≤|a-c| *|d|+|a| *|b-d| := by
  rw [show a*b-c*d=(a-c)*d+a*(b-d) by ring]
  simpa only [abs_mul] using abs_add_le ((a-c)*d) (a*(b-d))

def actualNormalizedSignProgramError (n : ℕ) : ℝ :=
  2*actualActivationInverseError n+(4*(n : ℝ)^5+2)*actualPairSourceProgramError n

theorem actual_normalized_sign_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ output : ℤ,
      |(actualNormalizedSignProgram constant n output : ℝ)-actualNormalizedSign (constant : ℝ) n output|≤
        actualNormalizedSignProgramError n := by
  filter_upwards [actual_mixed_slice_program_eventually constant,
    actual_activation_inverse_program_eventually constant hc,actual_activation_inverse_bound_eventually constant hc]
    with n hslice hi hInv output
  have hs (positive shifted : Bool) :
      |(actualMixedSliceProgram constant n positive shifted output : ℝ)-
        actualSignedSliceMean (constant : ℝ) n positive shifted output|≤actualPairSourceProgramError n :=
    hslice positive shifted output
  have hbound (positive shifted : Bool) : |actualSignedSliceMean (constant : ℝ) n positive shifted output|≤1 :=
    mixed_slice_abs_le_one _ _ _ _ _ _ _
  have hdiff (shifted : Bool) :
      |((actualMixedSliceProgram constant n true shifted output : ℝ)-actualMixedSliceProgram constant n false shifted output)-
        (actualSignedSliceMean (constant : ℝ) n true shifted output-actualSignedSliceMean (constant : ℝ) n false shifted output)|≤
        2*actualPairSourceProgramError n :=
    (approximation_sub_error _ _ _ _).trans ((add_le_add (hs true shifted) (hs false shifted)).trans_eq (by ring))
  have htrue : |actualSignedSliceMean (constant : ℝ) n true true output-
      actualSignedSliceMean (constant : ℝ) n false true output|≤2 :=
    (abs_sub _ _).trans (by linarith [hbound true true,hbound false true])
  have he0 : 0≤actualPairSourceProgramError n := by
    unfold actualPairSourceProgramError actualBodyBlurProgramError actualRootMarginalError;positivity
  have hi0 : 0≤actualActivationInverseError n := by unfold actualActivationInverseError;positivity
  simp only [actualNormalizedSignProgram,Rat.cast_sub,Rat.cast_mul,actualNormalizedSign]
  apply (approximation_sub_error _ _ _ _).trans
  apply (add_le_add (approximation_mul_error _ _ _ _) (hdiff false)).trans
  calc
    _ ≤ actualActivationInverseError n*2+(2*(n : ℝ)^5)*(2*actualPairSourceProgramError n)+
        2*actualPairSourceProgramError n := by gcongr;exact hdiff true
    _ = _ := by unfold actualNormalizedSignProgramError;ring

def actualResponseProgramError (n : ℕ) : ℝ :=
  actualNormalizedSignProgramError n+2*actualPairSourceProgramError n

theorem actualResponseProgramError_negligible : Negligible actualResponseProgramError := by
  have hh := (actualActivationInverseError_negligible.const_mul 2).add
    (((actualPairSourceProgramError_negligible.mul_polynomial 5).const_mul 4).add
      (actualPairSourceProgramError_negligible.const_mul 4))
  convert hh using 1
  funext n
  unfold actualResponseProgramError actualNormalizedSignProgramError
  ring

theorem actualResponse_basis (constant : ℝ) (n : ℕ) (hc : 1≤constant) (hn : 1≤n)
    (input output : Fin (Parameters.modulus n)) :
    actualResponse constant n (Pi.single input 1) output=
      (if input=output then 1 else 0)+paletteSign (Parameters.modulus n) input*
        actualNormalizedSign constant n output.val+
      actualAnchorMatrix constant n false input output.val-actualAnchorMatrix constant n true input output.val := by
  rw [actualResponse_apply_formula]
  have hsign : (∑ color,paletteSign (Parameters.modulus n) color*(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color)=
      paletteSign (Parameters.modulus n) input := by simp [Pi.single_apply]
  have hanchor (f : Fin (Parameters.modulus n) → ℝ) :
      (∑ color,(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color*f color)=f input := by simp [Pi.single_apply]
  rw [hsign,hanchor,actualNormalizedSign_eq constant n hc hn]
  simp only [Pi.single_apply,actualAnchorMatrix,Bool.false_eq_true,if_false,if_true,eq_comm]
  ring

/-- Every entry is the actual response on a coordinate basis vector.
The body and root-only anchor branches are both explicitly evaluated. -/
theorem actual_response_program_eventually (constant : ℕ) (hc : 1≤constant) :
    ∀ᶠ n : ℕ in atTop,∀ (input output : Fin (Parameters.modulus n)),
      |(actualResponseProgram constant n input.val output.val : ℝ)-
        actualResponse (constant : ℝ) n (Pi.single input 1) output|≤actualResponseProgramError n := by
  filter_upwards [actual_normalized_sign_program_eventually constant hc,
    actual_anchor_program_eventually constant,eventually_ge_atTop 1] with n hs ha hn input output
  rw [actualResponse_basis _ _ (by exact_mod_cast hc) hn]
  simp only [actualResponseProgram,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    ParameterProgram.modulus_value,paletteSignProgram_cast]
  have heq : ((if input.val=output.val then 1 else 0 : ℚ) : ℝ)=
      (if input=output then 1 else 0 : ℝ) := by
    simp only [Fin.val_inj]
    split_ifs <;> norm_num
  rw [heq]
  rw [show ∀ delta sign a b c d e f : ℝ,
      (delta+sign*a+b-c)-(delta+sign*d+e-f)=sign*(a-d)+(b-e)-(c-f) by intros;ring]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  rw [abs_mul]
  apply (add_le_add (add_le_add (mul_le_mul (paletteSign_abs_le _ _) (hs output.val)
    (abs_nonneg _) (by norm_num)) (ha false input output.val)) (ha true input output.val)).trans_eq
  unfold actualResponseProgramError
  ring

end
end AFT.V7Calibration

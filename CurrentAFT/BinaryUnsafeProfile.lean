import CurrentAFT.BinarySafeProfile

/-! # Actual shifted unsafe profile with binary interval tests -/
namespace CurrentAFT.BinaryUnsafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus signedAdd signedLe BinaryBodyKernel.translated

def membership (modulus margin output : List Bool) : CountedValue Bool :=
  let lower := signedLe false false margin output
  let upper := signedAdd false true modulus margin
  let last := signedLe upper.negative false upper.digits output
  ⟨lower.value && !last.value, lower.work+upper.work+last.work+4⟩

theorem membership_value (modulus margin output : List Bool) :
    (membership modulus margin output).value=true ↔
      (value margin:ℤ)≤value output ∧ (value output:ℤ)<(value modulus:ℤ)-value margin := by
  let lower := signedLe false false margin output
  let upper := signedAdd false true modulus margin
  let last := signedLe upper.negative false upper.digits output
  have hl : lower.value=true ↔ (value margin:ℤ)≤value output := by
    simpa only [signedValue, Bool.false_eq_true, if_false] using signedLe_value false false margin output
  have hu : last.value=true ↔ (value modulus:ℤ)-value margin≤value output := by
    rw [signedLe_value, signedAdd_value]
    simp only [signedValue, Bool.false_eq_true, if_false, if_true]
    rfl
  change (lower.value && !last.value)=true ↔ _
  constructor
  · intro h
    have hp : lower.value=true ∧ (!last.value)=true := by simpa only [Bool.and_eq_true] using h
    have hleft := hp.1
    have hn : last.value≠true := by
      intro hv
      have ht := hp.2
      simp only [hv, Bool.not_true] at ht
      contradiction
    exact ⟨hl.mp hleft, lt_of_not_ge (fun hle => hn (hu.mpr hle))⟩
  · intro h
    have hleft := hl.mpr h.1
    have hn : last.value=false := by
      cases hv : last.value
      · rfl
      · have hx := hu.mp hv
        omega
    simp only [hleft, hn, Bool.not_false, Bool.and_self]

theorem membership_work (modulus margin output : List Bool) (bound : ℕ)
    (hq : modulus.length≤bound) (hm : margin.length≤bound) (ho : output.length≤bound) :
    (membership modulus margin output).work≤100*bound+100 := by
  have wl := signedLe_work false false margin output
  have wu := signedAdd_work false true modulus margin
  have hu := signedAdd_length false true modulus margin
  have wr := signedLe_work (signedAdd false true modulus margin).negative false
    (signedAdd false true modulus margin).digits output
  change _+_+_+4≤_
  omega

def kernel (count margin : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulusCode := canonicalCounter count
  let marginCode := canonicalCounter margin
  let safe := membership modulusCode.digits marginCode.digits output
  let shifted := BinaryBodyKernel.translated count margin shift.negative shift.digits output
  ⟨if safe.value then zero else shifted.data,
    modulusCode.work+marginCode.work+safe.work+shifted.work+5⟩

theorem kernel_value (count margin : ℕ) (shift : IntegerBits) (output : List Bool) (hq : 0<count) :
    (kernel count margin shift output).data.decode =
      if (margin:ℤ)≤value output ∧ (value output:ℤ)<(count:ℤ)-margin then 0 else
        RationalProposalProgram.bodyKernel count margin shift.decode (value output) := by
  have hs := membership_value (canonicalCounter count).digits (canonicalCounter margin).digits output
  simp only [canonicalCounter_value] at hs
  unfold kernel
  dsimp only
  by_cases h : (membership (canonicalCounter count).digits (canonicalCounter margin).digits output).value=true
  · simp only [if_pos h, if_pos (hs.mp h), zero_value]
  · rw [if_neg h, if_neg (fun hp => h (hs.mpr hp))]
    exact BinaryBodyKernel.translated_value count margin shift.negative shift.digits output hq

def kernelWork (bound : ℕ) := 100*(bound+1)^2+100*bound+100+BinaryBodyKernel.translatedWork bound+5

theorem kernel_bounds (count margin : ℕ) (shift : IntegerBits) (output : List Bool) (bound : ℕ)
    (hq : count≤bound) (hm : margin≤bound) (hs : shift.digits.length≤bound) (ho : output.length≤bound) :
    HeightBound (kernel count margin shift output).data.decode (bound*(bound+4)) ∧
      (kernel count margin shift output).work≤kernelWork bound := by
  have hqc : (canonicalCounter count).digits.length≤bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := count))).trans hq
  have hmc : (canonicalCounter margin).digits.length≤bound := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := margin))).trans hm
  have hshift := BinaryBodyKernel.translated_bounds count margin shift.negative shift.digits output bound hq hm hs ho
  have wsafe := membership_work (canonicalCounter count).digits (canonicalCounter margin).digits output bound hqc hmc ho
  have wq := (canonicalCounter_work count).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wm := (canonicalCounter_work margin).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2))
  constructor
  · unfold kernel
    dsimp only
    split
    · rw [zero_value]
      exact HeightBound.zero.mono (Nat.zero_le _)
    · exact hshift.1
  · change _+_+_+_+5≤_
    unfold kernelWork
    omega

def current (security : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let result := kernel modulus.count margin.count shift output
  ⟨result.data, modulus.work+margin.work+result.work+3⟩

theorem current_value (security : ℕ) (shift : IntegerBits) (output : List Bool) :
    (current security shift output).data.decode = RationalBackgroundProfiles.unsafeProfile security shift.decode (value output) := by
  have hq : 0<(PublicParameterProgram.modulus security).count := by
    rw [PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  change (kernel _ _ _ _).data.decode=_
  rw [kernel_value _ _ _ _ hq, BinarySafeProfile.margin_value]
  rfl

noncomputable section
noncomputable def parameterPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+shiftBits+outputBits
noncomputable def heightPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  parameterPolynomial shiftBits outputBits*(parameterPolynomial shiftBits outputBits+4)
noncomputable def kernelWorkPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  100*(bound+1)^2+100*bound+100+BinaryBodyKernel.translatedWorkPolynomial bound+5
noncomputable def workPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    kernelWorkPolynomial (parameterPolynomial shiftBits outputBits)+3

theorem kernelWorkPolynomial_eval (bound : Polynomial ℕ) (security : ℕ) :
    (kernelWorkPolynomial bound).eval security=kernelWork (bound.eval security) := by
  simp only [kernelWorkPolynomial, kernelWork, BinaryBodyKernel.translatedWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem current_bounds (security : ℕ) (shift : IntegerBits) (output : List Bool) (shiftBits outputBits : Polynomial ℕ)
    (hs : shift.digits.length≤shiftBits.eval security) (ho : output.length≤outputBits.eval security) :
    HeightBound (current security shift output).data.decode ((heightPolynomial shiftBits outputBits).eval security) ∧
      (current security shift output).work≤(workPolynomial shiftBits outputBits).eval security := by
  let q := PublicParameterProgram.modulus security
  let m := BinarySafeProfile.margin security
  let B := (parameterPolynomial shiftBits outputBits).eval security
  have hB : B=BinaryFirstInverseProgram.colorsPolynomial.eval security+3*(security+2)^2+
      shiftBits.eval security+outputBits.eval security := by
    simp only [B, parameterPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
  have hq : q.count≤B := (BinaryFirstInverseProgram.colors_bound security).trans (by rw [hB]; omega)
  have hm : m.count≤B := by rw [BinarySafeProfile.margin_value, hB]; omega
  have h := kernel_bounds q.count m.count shift output B hq hm (hs.trans (by rw [hB]; omega)) (ho.trans (by rw [hB]; omega))
  constructor
  · simpa only [heightPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat] using h.1
  · have wq := PublicParameterProgram.modulus_work security
    have wm := BinarySafeProfile.margin_work security
    change q.work≤_ at wq
    change m.work≤_ at wm
    change q.work+m.work+(kernel q.count m.count shift output).work+3≤_
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat, PublicParameterProgram.workPolynomial_eval,
      BinarySafeProfile.marginWorkPolynomial_eval, kernelWorkPolynomial_eval]
    dsimp only [B] at h
    omega

end
end CurrentAFT.BinaryUnsafeProfile

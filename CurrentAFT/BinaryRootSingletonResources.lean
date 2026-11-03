import CurrentAFT.BinaryRootSingleton

/-! # Polynomial resources for the pure-primary singleton reciprocal -/
namespace CurrentAFT.BinaryRootSingleton
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProfileLookup.current BinaryRootProfile.firstDensity BinaryRootProfile.meanDensity
noncomputable section

def firstHeightPolynomial (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileLookup.heightPolynomial (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
def firstWorkPolynomial (order : ℕ) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial
    (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
    (BinaryRootProfile.firstDensityWorkPolynomial precision queueBits rootBits)
def meanFirstHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileLookup.heightPolynomial (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
def meanFirstWorkPolynomial (order : ℕ) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial
    (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
    (BinaryRootProfile.meanDensityWorkPolynomial precision queueBits)

theorem first_bounds (security order : ℕ) (precision queueBits rootBits : Polynomial ℕ) (role : BodyRole)
    (queue root : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (first security (precision.eval security) order role queue root arity colors centers).value.decode
      ((firstHeightPolynomial precision queueBits rootBits).eval security) ∧
      (first security (precision.eval security) order role queue root arity colors centers).work ≤
        (firstWorkPolynomial order precision queueBits rootBits).eval security := by
  let profile := BinaryRootProfile.firstDensity security (precision.eval security) role queue root
  have hh (color : Fin (BinaryProfileLookup.colors security)) :=
    BinaryRootProfile.firstDensity_bounds security precision queueBits rootBits role queue root color hq hr
  have hl (output : ℕ) (ho : output<BinaryProfileLookup.colors security) := BinaryProfileLookup.current_bounds security
    (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
    (BinaryRootProfile.firstDensityWorkPolynomial precision queueBits rootBits) profile output ho
    (fun color => (hh color).1) (fun color => (hh color).2)
  have h := BinaryFirstCoefficient.current_bounds order (BinaryProfileLookup.colors security)
    ((firstHeightPolynomial precision queueBits rootBits).eval security)
    ((BinaryProfileLookup.workPolynomial (BinaryRootProfile.firstDensityHeightPolynomial precision queueBits rootBits)
      (BinaryRootProfile.firstDensityWorkPolynomial precision queueBits rootBits)).eval security+1)
    (BinaryProfileLookup.current security profile) zeroProfile
    (fun color ho => ⟨(hl color ho).1,(hl color ho).2.trans (Nat.le_add_right _ _)⟩)
    (fun _ _ => ⟨HeightBound.zero.mono (Nat.zero_le _),by simp only [zeroProfile]; omega⟩)
    arity colors centers hc hd
  dsimp only [profile] at h
  constructor
  · exact h.1
  · unfold first
    simp only [firstWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

theorem meanFirst_bounds (security order : ℕ) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (meanFirst security (precision.eval security) order role queue arity colors centers).value.decode
      ((meanFirstHeightPolynomial precision queueBits).eval security) ∧
      (meanFirst security (precision.eval security) order role queue arity colors centers).work ≤
        (meanFirstWorkPolynomial order precision queueBits).eval security := by
  let profile := BinaryRootProfile.meanDensity security (precision.eval security) role queue
  have hh (color : Fin (BinaryProfileLookup.colors security)) :=
    BinaryRootProfile.meanDensity_bounds security precision queueBits role queue color hq
  have hl (output : ℕ) (ho : output<BinaryProfileLookup.colors security) := BinaryProfileLookup.current_bounds security
    (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
    (BinaryRootProfile.meanDensityWorkPolynomial precision queueBits) profile output ho
    (fun color => (hh color).1) (fun color => (hh color).2)
  have h := BinaryFirstCoefficient.current_bounds order (BinaryProfileLookup.colors security)
    ((meanFirstHeightPolynomial precision queueBits).eval security)
    ((BinaryProfileLookup.workPolynomial (BinaryRootProfile.meanDensityHeightPolynomial precision queueBits)
      (BinaryRootProfile.meanDensityWorkPolynomial precision queueBits)).eval security+1)
    (BinaryProfileLookup.current security profile) zeroProfile
    (fun color ho => ⟨(hl color ho).1,(hl color ho).2.trans (Nat.le_add_right _ _)⟩)
    (fun _ _ => ⟨HeightBound.zero.mono (Nat.zero_le _),by simp only [zeroProfile]; omega⟩)
    arity colors centers hc hd
  dsimp only [profile] at h
  constructor
  · exact h.1
  · unfold meanFirst
    simp only [meanFirstWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

def positiveHeightPolynomial (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  meanFirstHeightPolynomial precision queueBits+1
def positiveWorkPolynomial (order : ℕ) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+8)+meanFirstWorkPolynomial order precision queueBits+
    primitiveWorkPolynomial (meanFirstHeightPolynomial precision queueBits)

theorem positive_bounds (security order : ℕ) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (positive security (precision.eval security) order role queue arity colors centers).value.decode
      ((positiveHeightPolynomial precision queueBits).eval security) ∧
      (positive security (precision.eval security) order role queue arity colors centers).work ≤
        (positiveWorkPolynomial order precision queueBits).eval security := by
  let unit := BinaryFamilyPower.unit order arity colors centers
  let first := meanFirst security (precision.eval security) order role queue arity colors centers
  have hu := BinaryFamilyPower.unit_bounds order arity colors centers
  have hf := meanFirst_bounds security order precision queueBits role queue hq arity colors centers hc hd
  have hw := RationalBits.add_work unit.value first.value ((meanFirstHeightPolynomial precision queueBits).eval security)
    (hu.1.mono (Nat.zero_le _)) hf.1
  constructor
  · change HeightBound (RationalBits.add unit.value first.value).data.decode _
    rw [RationalBits.add_value]
    simpa only [positiveHeightPolynomial,Polynomial.eval_add,Polynomial.eval_one,zero_add] using hu.1.add hf.1
  · change unit.work+first.work+(RationalBits.add unit.value first.value).work+2 ≤ _
    have wu : unit.work ≤ 12*order+6 := hu.2
    have wf : first.work ≤ (meanFirstWorkPolynomial order precision queueBits).eval security := hf.2
    simp only [positiveWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C,primitiveWorkPolynomial_eval]
    omega

def inverseHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeightPolynomial precision queueBits)
def inverseWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeightPolynomial precision queueBits)
    (positiveWorkPolynomial order precision queueBits)

theorem inverse_bounds (security order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) (role : BodyRole)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (inverse security (precision.eval security) order programs role queue arity colors centers).value.decode
      ((inverseHeightPolynomial order programs precision queueBits).eval security) ∧
      (inverse security (precision.eval security) order programs role queue arity colors centers).work ≤
        (inverseWorkPolynomial order programs precision queueBits).eval security :=
  BinaryFamilyReciprocal.polynomial_bounds order (BinaryProfileLookup.colors security) security programs
    (positive security (precision.eval security) order role queue) (positiveHeightPolynomial precision queueBits)
    (positiveWorkPolynomial order precision queueBits)
    (positive_bounds security order precision queueBits role queue hq) arity colors centers hc hd

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (firstHeightPolynomial precision queueBits rootBits+inverseHeightPolynomial order programs precision queueBits)
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (firstHeightPolynomial precision queueBits rootBits+inverseHeightPolynomial order programs precision queueBits)
    (firstWorkPolynomial order precision queueBits rootBits+inverseWorkPolynomial order programs precision queueBits)

theorem current_bounds (security order : ℕ) (programs : List (Entry order))
    (precision queueBits rootBits : Polynomial ℕ) (role : BodyRole) (queue root : IntegerBits)
    (hq : queue.digits.length ≤ queueBits.eval security) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (current security (precision.eval security) order programs role queue root arity colors centers).value.decode
      ((heightPolynomial order programs precision queueBits rootBits).eval security) ∧
      (current security (precision.eval security) order programs role queue root arity colors centers).work ≤
        (workPolynomial order programs precision queueBits rootBits).eval security := by
  have hf := first_bounds security order precision queueBits rootBits role queue root hq hr
  have hi := inverse_bounds security order programs precision queueBits role queue hq
  let H := firstHeightPolynomial precision queueBits rootBits+inverseHeightPolynomial order programs precision queueBits
  let W := firstWorkPolynomial order precision queueBits rootBits+inverseWorkPolynomial order programs precision queueBits
  have hfirst (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
      (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
      HeightBound (first security (precision.eval security) order role queue root arity colors centers).value.decode (H.eval security) ∧
      (first security (precision.eval security) order role queue root arity colors centers).work ≤ W.eval security := by
    have h := hf arity colors centers hc hd
    simp only [H,W,Polynomial.eval_add]
    exact ⟨h.1.mono (Nat.le_add_right _ _),h.2.trans (Nat.le_add_right _ _)⟩
  have hinverse (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
      (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
      HeightBound (inverse security (precision.eval security) order programs role queue arity colors centers).value.decode (H.eval security) ∧
      (inverse security (precision.eval security) order programs role queue arity colors centers).work ≤ W.eval security := by
    have h := hi arity colors centers hc hd
    simp only [H,W,Polynomial.eval_add]
    exact ⟨h.1.mono (Nat.le_add_left _ _),h.2.trans (Nat.le_add_left _ _)⟩
  simpa only [heightPolynomial,workPolynomial,BinaryFamilyArithmetic.heightPolynomial_eval,
    BinaryFamilyArithmetic.workPolynomial_eval] using
    BinaryFamilyArithmetic.multiply_bounds order (BinaryProfileLookup.colors security) (H.eval security) (W.eval security) programs
      (first security (precision.eval security) order role queue root) (inverse security (precision.eval security) order programs role queue)
      hfirst hinverse arity colors centers hc hd

end
end CurrentAFT.BinaryRootSingleton

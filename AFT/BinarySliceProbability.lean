import AFT.BinaryIntervalProbability

/-! Trimmed-slice probabilities from actual signed binary endpoints. The
interval width is computed by signed subtraction, never encoded from a
precomputed rational probability. -/
namespace AFT.BinaryArithmetic
open RationalNumerics V7Calibration RationalBits

/-- Clip a signed integer to its nonnegative part. -/
def nonnegativeDigits (sign : Bool) (digits : List Bool) : List Bool :=
  if sign then [] else digits

theorem nonnegativeDigits_value (sign : Bool) (digits : List Bool) :
    value (nonnegativeDigits sign digits)=(signedValue sign digits).toNat := by
  cases sign <;> simp [nonnegativeDigits,signedValue,value]

theorem nonnegativeDigits_length (sign : Bool) (digits : List Bool) :
    (nonnegativeDigits sign digits).length≤digits.length := by
  cases sign <;> simp [nonnegativeDigits]

/-- Probability on a signed half-open interval, including an empty one. -/
def binaryEndpointProbability (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) : RationalResult :=
  let difference := signedAdd upperSign (!lowerSign) upper lower
  let width := nonnegativeDigits difference.negative difference.digits
  let result := binaryIntervalProbability lowerSign colorSign lower width color
  ⟨result.data,difference.work+result.work+3⟩

theorem binaryEndpointProbability_value (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) :
    (binaryEndpointProbability lowerSign upperSign colorSign lower upper color).data.decode=
      (if signedValue lowerSign lower≤signedValue colorSign color ∧
        signedValue colorSign color<signedValue upperSign upper
       then (((signedValue upperSign upper-signedValue lowerSign lower).toNat : ℕ) : ℚ)⁻¹ else 0) := by
  have hneg : signedValue (!lowerSign) lower= -signedValue lowerSign lower := by
    cases lowerSign <;> simp [signedValue]
  have hv := signedAdd_value upperSign (!lowerSign) upper lower
  rw [hneg,←sub_eq_add_neg] at hv
  simp only [binaryEndpointProbability,binaryIntervalProbability_value,nonnegativeDigits_value,hv]
  rw [←countedIntervalProbability_value]
  simp only [countedIntervalProbability]
  have he : (signedValue lowerSign lower≤signedValue colorSign color ∧
      signedValue colorSign color<signedValue lowerSign lower+
        ((signedValue upperSign upper-signedValue lowerSign lower).toNat : ℤ)) ↔
      (signedValue lowerSign lower≤signedValue colorSign color ∧
        signedValue colorSign color<signedValue upperSign upper) := by omega
  simp only [he]

def binaryEndpointProbabilityWork (bits : ℕ) : ℕ :=
  20*bits+11+binaryIntervalProbabilityWork (bits+1)

theorem binaryEndpointProbability_work (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) (bits : ℕ)
    (hl : lower.length≤bits) (hu : upper.length≤bits) (hc : color.length≤bits) :
    (binaryEndpointProbability lowerSign upperSign colorSign lower upper color).work≤
      binaryEndpointProbabilityWork bits := by
  have hd := signedAdd_work upperSign (!lowerSign) upper lower
  have hdl := signedAdd_length upperSign (!lowerSign) upper lower
  have hn := nonnegativeDigits_length
    (signedAdd upperSign (!lowerSign) upper lower).negative
    (signedAdd upperSign (!lowerSign) upper lower).digits
  have hm : max upper.length lower.length≤bits := max_le hu hl
  have hw := binaryIntervalProbability_work lowerSign colorSign lower
    (nonnegativeDigits (signedAdd upperSign (!lowerSign) upper lower).negative
      (signedAdd upperSign (!lowerSign) upper lower).digits) color (bits+1)
    (by omega) (by omega) (by omega)
  simp only [binaryEndpointProbability,binaryEndpointProbabilityWork]
  omega

theorem binaryEndpointProbability_height (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) (bits : ℕ) (hl : lower.length≤bits) (hu : upper.length≤bits) :
    HeightBound (binaryEndpointProbability lowerSign upperSign colorSign lower upper color).data.decode (bits+1) := by
  have hdl := signedAdd_length upperSign (!lowerSign) upper lower
  have hn := nonnegativeDigits_length
    (signedAdd upperSign (!lowerSign) upper lower).negative
    (signedAdd upperSign (!lowerSign) upper lower).digits
  have hm : max upper.length lower.length≤bits := max_le hu hl
  exact binaryIntervalProbability_height _ _ _ _ _ _ (by omega)

structure SliceEndpoints where
  lower : SignedResult
  upper : SignedResult
  work : ℕ

/-- Both shifts are built by signed arithmetic on the supplied operands. -/
def binarySliceEndpoints (modulusSign boundarySign shiftSign : Bool)
    (modulus boundary shift : List Bool) : SliceEndpoints :=
  let difference := signedAdd modulusSign (!boundarySign) modulus boundary
  let lower := signedAdd boundarySign false boundary (if shiftSign then [] else shift)
  let upper := signedAdd difference.negative true difference.digits (if shiftSign then shift else [])
  ⟨lower,upper,difference.work+lower.work+upper.work+4⟩

theorem binarySliceEndpoints_values (modulusSign boundarySign shiftSign : Bool)
    (modulus boundary shift : List Bool) :
    let result := binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift
    signedValue result.lower.negative result.lower.digits=
      signedValue boundarySign boundary+max (signedValue shiftSign shift) 0 ∧
    signedValue result.upper.negative result.upper.digits=
      signedValue modulusSign modulus-signedValue boundarySign boundary+min (signedValue shiftSign shift) 0 := by
  have hneg : signedValue (!boundarySign) boundary= -signedValue boundarySign boundary := by
    cases boundarySign <;> simp [signedValue]
  simp only [binarySliceEndpoints,signedAdd_value,hneg]
  cases shiftSign <;> simp [signedValue,sub_eq_add_neg]


def binarySliceProbability (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) : RationalResult :=
  let endpoints := binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift
  let result := binaryEndpointProbability endpoints.lower.negative endpoints.upper.negative colorSign
    endpoints.lower.digits endpoints.upper.digits color
  ⟨result.data,endpoints.work+result.work+2⟩

theorem binarySliceProbability_value (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) :
    (binarySliceProbability modulusSign boundarySign shiftSign colorSign modulus boundary shift color).data.decode=
      sliceProbabilityProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
        (signedValue shiftSign shift) (signedValue colorSign color) := by
  have he := binarySliceEndpoints_values modulusSign boundarySign shiftSign modulus boundary shift
  simp only [binarySliceProbability,binaryEndpointProbability_value,he.1,he.2]
  rw [←countedSliceProbability_value]
  simp only [countedSliceProbability]
  have heq : signedValue modulusSign modulus-signedValue boundarySign boundary+
      min (signedValue shiftSign shift) 0-
        (signedValue boundarySign boundary+max (signedValue shiftSign shift) 0)=
      signedValue modulusSign modulus-2*signedValue boundarySign boundary-|signedValue shiftSign shift| := by
    rcases le_total (signedValue shiftSign shift) 0 with hs | hs
    · rw [min_eq_left hs,max_eq_right hs,abs_of_nonpos hs];ring
    · rw [min_eq_right hs,max_eq_left hs,abs_of_nonneg hs];ring
  rw [heq]

def binarySliceProbabilityWork (bits : ℕ) : ℕ :=
  100*(bits+2)+binaryEndpointProbabilityWork (bits+2)

theorem binarySliceEndpoints_bounds (modulusSign boundarySign shiftSign : Bool)
    (modulus boundary shift : List Bool) (bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (hs : shift.length≤bits) :
    let result := binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift
    result.lower.digits.length≤bits+2 ∧ result.upper.digits.length≤bits+2 ∧ result.work≤100*(bits+2)-2 := by
  have hpos : (if shiftSign then [] else shift).length≤bits := by split <;> simp_all
  have hneg : (if shiftSign then shift else []).length≤bits := by split <;> simp_all
  have hd := signedAdd_work modulusSign (!boundarySign) modulus boundary
  have hdl := signedAdd_length modulusSign (!boundarySign) modulus boundary
  have hl := signedAdd_work boundarySign false boundary (if shiftSign then [] else shift)
  have hll := signedAdd_length boundarySign false boundary (if shiftSign then [] else shift)
  have hu := signedAdd_work (signedAdd modulusSign (!boundarySign) modulus boundary).negative true
    (signedAdd modulusSign (!boundarySign) modulus boundary).digits (if shiftSign then shift else [])
  have hul := signedAdd_length (signedAdd modulusSign (!boundarySign) modulus boundary).negative true
    (signedAdd modulusSign (!boundarySign) modulus boundary).digits (if shiftSign then shift else [])
  simp only [binarySliceEndpoints]
  omega

theorem binarySliceProbability_work (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) (bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (hs : shift.length≤bits) (hc : color.length≤bits) :
    (binarySliceProbability modulusSign boundarySign shiftSign colorSign modulus boundary shift color).work≤
      binarySliceProbabilityWork bits := by
  have he := binarySliceEndpoints_bounds modulusSign boundarySign shiftSign modulus boundary shift bits hm hb hs
  have hw := binaryEndpointProbability_work
    (binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift).lower.negative
    (binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift).upper.negative colorSign
    (binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift).lower.digits
    (binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift).upper.digits color
    (bits+2) he.1 he.2.1 (by omega)
  simp only [binarySliceProbability,binarySliceProbabilityWork]
  omega

theorem binarySliceProbability_height (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) (bits : ℕ)
    (hm : modulus.length≤bits) (hb : boundary.length≤bits) (hs : shift.length≤bits) :
    HeightBound (binarySliceProbability modulusSign boundarySign shiftSign colorSign modulus boundary shift color).data.decode (bits+3) := by
  have he := binarySliceEndpoints_bounds modulusSign boundarySign shiftSign modulus boundary shift bits hm hb hs
  exact binaryEndpointProbability_height _ _ _ _ _ _ (bits+2) he.1 he.2.1

end AFT.BinaryArithmetic

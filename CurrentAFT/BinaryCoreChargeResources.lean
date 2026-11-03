import CurrentAFT.BinaryCoreChargeCost
import CurrentAFT.CurrentProposalResources

/-! Fixed explicit polynomial resources for the actual current charge guard. -/
namespace CurrentAFT.BinaryCoreCharge
open AFT CurrentProposalResources
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current

def colorsPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
def leafLengthPolynomial : Polynomial ℕ := colorsPolynomial+2*(Polynomial.X+2)^48+2*(Polynomial.X+2)^2+3
def leafWorkPolynomial : Polynomial ℕ :=
  shiftWorkPolynomial+100*(colorsPolynomial+1)^2+18*countPolynomial+20*leafLengthPolynomial+30
def totalLengthPolynomial : Polynomial ℕ := 4*countPolynomial+3*leafLengthPolynomial+5
def totalWorkPolynomial : Polynomial ℕ :=
  metadataWorkPolynomial+3*countPolynomial*(leafWorkPolynomial+20*(countPolynomial+leafLengthPolynomial)+11)+
    50*(countPolynomial+1)^2+60*totalLengthPolynomial+60
def workPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+50*(colorsPolynomial+1)^2+totalWorkPolynomial+
    60*(totalLengthPolynomial+colorsPolynomial+1)^2+4*(totalLengthPolynomial+colorsPolynomial)+18

theorem colorsPolynomial_eval (security : ℕ) : colorsPolynomial.eval security = colorsBound security := by
  simp only [colorsPolynomial, colorsBound, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem leafLengthPolynomial_eval (security : ℕ) : leafLengthPolynomial.eval security = leafLength security := by
  simp only [leafLengthPolynomial, leafLength, colorsPolynomial_eval, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem leafWork_bound (security : ℕ) : leafWork security ≤ leafWorkPolynomial.eval security := by
  rcases count_bounds security with ⟨hc, hl, hq, _, _⟩
  simp only [leafWork, leafWorkPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, colorsPolynomial_eval, leafLengthPolynomial_eval, shiftWorkPolynomial_eval]
  omega

theorem totalLength_bound (security : ℕ) : totalLength security ≤ totalLengthPolynomial.eval security := by
  rcases count_bounds security with ⟨hc, hl, hq, _, _⟩
  simp only [totalLength, totalLengthPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_ofNat, leafLengthPolynomial_eval]
  omega

theorem totalWork_bound (security : ℕ) : totalWork security ≤ totalWorkPolynomial.eval security := by
  rcases count_bounds security with ⟨hc, hl, hq, _, _⟩
  have hw := leafWork_bound security
  have hh := totalLength_bound security
  have hm := metadata_work security
  let S := countPolynomial.eval security
  let W := leafWorkPolynomial.eval security
  let B := leafLength security
  have hb (count : ℕ) (hcount : count ≤ S) : count*(leafWork security+20*(count+B)+11) ≤
      S*(W+20*(S+B)+11) := Nat.mul_le_mul hcount
        (Nat.add_le_add_right (Nat.add_le_add hw (Nat.mul_le_mul_left 20 (Nat.add_le_add_right hcount B))) 11)
  have hctrl := hb _ hc
  have hleg := hb _ hl
  have hqueue := hb _ hq
  have hsq := Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2)
  simp only [totalWork, totalWorkPolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, leafLengthPolynomial_eval]
  change _ ≤ metadataWorkPolynomial.eval security+3*S*(W+20*(S+B)+11)+
    50*(S+1)^2+60*totalLengthPolynomial.eval security+60
  have he : 3*S*(W+20*(S+B)+11) = 3*(S*(W+20*(S+B)+11)) := by ring
  rw [he]
  dsimp only [S, W, B] at *
  omega

theorem polynomial_work (security : ℕ) (data : CurrentCoreProposal.MaterializedCore security) :
    (current security data).work ≤ workPolynomial.eval security := by
  apply (current_work security data).trans
  have ht := totalWork_bound security
  have hh := totalLength_bound security
  have hquad := Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add_right hh (colorsBound security)) 1) 2)
  have hlinear := Nat.mul_le_mul_left 4 (Nat.add_le_add_right hh (colorsBound security))
  unfold work workPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_one, PublicParameterProgram.workPolynomial_eval, colorsPolynomial_eval]
  omega

end
end CurrentAFT.BinaryCoreCharge

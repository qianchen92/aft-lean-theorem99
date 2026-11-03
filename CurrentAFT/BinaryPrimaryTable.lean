import CurrentAFT.BinaryPrimaryRaw
import CurrentAFT.BinaryProposalGuard

/-! # The full binary primary proposal table

The raw entries, lower guard and uniform fallback are all executed.  The
index loop is over the computed current prime and not over a hidden seed.
-/
namespace CurrentAFT.BinaryPrimaryTable
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalCounter PublicParameterProgram.modulus

def point (security bits output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let result := BinaryPrimaryRaw.current security bits code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits output : ℕ) :
    (point security bits output).data.decode = RationalProposalProgram.primaryRaw security bits output := by
  simp only [point, BinaryPrimaryRaw.current_value, canonicalCounter_value]

def raw (security bits : ℕ) : ArrayResult (PublicParameterProgram.modulus security).count :=
  let colors := PublicParameterProgram.modulus security
  let values := buildArray colors.count (fun index => point security bits index.val)
  ⟨values.data, colors.work+values.work+2⟩

theorem raw_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((raw security bits).data.get index).decode = RationalProposalProgram.primaryRaw security bits index.val := by
  simp only [raw, buildArray_get, point_value]

def current (security bits : ℕ) : ArrayResult (PublicParameterProgram.modulus security).count :=
  let values := raw security bits
  let guarded := BinaryProposalGuard.primary values.data
  ⟨guarded.data, values.work+guarded.work+2⟩

theorem current_value (security bits : ℕ) (index : Fin (PublicParameterProgram.modulus security).count) :
    ((current security bits).data.get index).decode = RationalProposalProgram.primary security bits index.val := by
  exact BinaryProposalGuard.primary_value security bits (raw security bits).data (raw_value security bits) index

theorem guarded_height {count : ℕ} (values : Vector RationalBits count) (height : ℕ)
    (hv : ∀ index, HeightBound (values.get index).decode height) (index : Fin count) :
    HeightBound ((BinaryProposalGuard.primary values).data.get index).decode (height+count) := by
  change HeightBound ((BinaryProposalGuard.guardedTable (BinaryProposalGuard.threshold count).data values).data.get index).decode _
  rw [BinaryProposalGuard.guardedTable_value]
  split_ifs
  · exact (hv index).mono (Nat.le_add_right _ _)
  · exact (HeightBound.nat_coarse count).inv.mono (Nat.le_add_left _ _)

noncomputable section

noncomputable def countPolynomial : Polynomial ℕ := 131072*(Polynomial.X+2)^64
noncomputable def rawHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryRaw.currentHeightPolynomial precision countPolynomial
noncomputable def rawWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    countPolynomial*(50*(countPolynomial+1)^2+BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial+4)+4

noncomputable def guardWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  (4*(2*count+3)+1)+60*(4*count+1)^2+primitiveWorkPolynomial (4*count)+3+
  (count*(3*count+BinaryRationalCompare.workPolynomial (4*count+height)+7)+1)+
  (60*(count+1)^2+primitiveWorkPolynomial count+3*count+5)+6

noncomputable def currentHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := rawHeightPolynomial precision+countPolynomial
noncomputable def currentWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  rawWorkPolynomial precision+guardWorkPolynomial countPolynomial (rawHeightPolynomial precision)+2

theorem count_bound (security : ℕ) :
    (PublicParameterProgram.modulus security).count ≤ countPolynomial.eval security := by
  rw [PublicParameterProgram.modulus_value]
  simpa only [countPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat, Parameters.base] using (Parameters.modulus_bounds security).2

theorem raw_bounds (security : ℕ) (precision : Polynomial ℕ) :
    (∀ index, HeightBound ((raw security (precision.eval security)).data.get index).decode
      ((rawHeightPolynomial precision).eval security)) ∧
    (raw security (precision.eval security)).work ≤ (rawWorkPolynomial precision).eval security := by
  let colors := PublicParameterProgram.modulus security
  let bound := countPolynomial.eval security
  have hc : colors.count ≤ bound := count_bound security
  have hp (index : Fin colors.count) :
      HeightBound (point security (precision.eval security) index.val).data.decode ((rawHeightPolynomial precision).eval security) ∧
      (point security (precision.eval security) index.val).work ≤
        50*(bound+1)^2+(BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial).eval security+2 := by
    have hi : index.val ≤ bound := (Nat.le_of_lt index.isLt).trans hc
    have hl : (canonicalCounter index.val).digits.length ≤ bound := by
      rw [canonicalCounter_length]
      exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := index.val))).trans hi
    have hraw := BinaryPrimaryRaw.current_bounds security (canonicalCounter index.val).digits precision countPolynomial hl
    have hw := (canonicalCounter_work index.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
    exact ⟨hraw.1, Nat.add_le_add_right (Nat.add_le_add hw hraw.2) 2⟩
  constructor
  · intro index
    simpa only [raw, buildArray_get] using (hp index).1
  · have wt := buildArray_work colors.count
      (50*(bound+1)^2+(BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial).eval security+2)
      (fun index => point security (precision.eval security) index.val) (fun index => (hp index).2)
    have wc : colors.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
    have wb := Nat.mul_le_mul_right
      (50*(bound+1)^2+(BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial).eval security+4) hc
    change colors.work+(buildArray colors.count (fun index => point security (precision.eval security) index.val)).work+2 ≤ _
    simp only [rawWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, PublicParameterProgram.workPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+
      bound*(50*(bound+1)^2+(BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial).eval security+4)+4
    have wt' : (buildArray colors.count (fun index => point security (precision.eval security) index.val)).work ≤
        colors.count*(50*(bound+1)^2+(BinaryPrimaryRaw.currentWorkPolynomial precision countPolynomial).eval security+4)+2 := by
      convert wt using 1
    omega

theorem guardWorkPolynomial_eval (count height : Polynomial ℕ) (security : ℕ) :
    (guardWorkPolynomial count height).eval security =
      BinaryProposalGuard.thresholdWork (count.eval security)+
      BinaryProposalGuard.lowerCheckWork (count.eval security) (4*count.eval security+height.eval security)+
      BinaryProposalGuard.uniformWork (count.eval security)+6 := by
  simp only [guardWorkPolynomial, BinaryProposalGuard.thresholdWork, BinaryProposalGuard.lowerCheckWork,
    BinaryProposalGuard.uniformWork, BinaryRationalCompare.workPolynomial_eval, primitiveWorkPolynomial_eval,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) :
    (∀ index, HeightBound ((current security (precision.eval security)).data.get index).decode
      ((currentHeightPolynomial precision).eval security)) ∧
    (current security (precision.eval security)).work ≤ (currentWorkPolynomial precision).eval security := by
  let colors := (PublicParameterProgram.modulus security).count
  let bound := countPolynomial.eval security
  let height := (rawHeightPolynomial precision).eval security
  have hc : colors ≤ bound := count_bound security
  have hb := raw_bounds security precision
  have hw := BinaryProposalGuard.primary_work (raw security (precision.eval security)).data height hb.1
  have hguard : BinaryProposalGuard.thresholdWork colors+BinaryProposalGuard.lowerCheckWork colors (4*colors+height)+
      BinaryProposalGuard.uniformWork colors+6 ≤ (guardWorkPolynomial countPolynomial (rawHeightPolynomial precision)).eval security := by
    rw [guardWorkPolynomial_eval]
    unfold BinaryProposalGuard.thresholdWork BinaryProposalGuard.lowerCheckWork BinaryProposalGuard.uniformWork
      BinaryRationalCompare.workBound primitiveWorkBound
    gcongr
  constructor
  · intro index
    have hh := guarded_height (raw security (precision.eval security)).data height hb.1 index
    apply hh.mono
    simp only [currentHeightPolynomial, Polynomial.eval_add]
    exact Nat.add_le_add_left hc height
  · change (raw security (precision.eval security)).work+(BinaryProposalGuard.primary (raw security (precision.eval security)).data).work+2 ≤ _
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    exact Nat.add_le_add_right (Nat.add_le_add hb.2 (hw.trans hguard)) 2

end
end CurrentAFT.BinaryPrimaryTable

import CurrentAFT.BinaryPackedRootGuard
import CurrentAFT.BinaryPackedRootFactorResources

/-! The complete executed scalar multiplying each whole packed source family.
Safety is tested by binary counters and every probability factor is computed. -/
namespace CurrentAFT.BinaryPackedRootScalar
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def current {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let guard := BinaryPackedRootGuard.current security data source
  let control := BinaryPackedRootFactors.control security bits program data sourcePrimary sourceBody source
  let untagged := BinaryPackedRootFactors.untagged security bits data source
  let signed := BinaryPackedRootFactors.signed security bits data source
  let pair := RationalBits.multiply control.data untagged.data
  let result := RationalBits.multiply pair.data signed.data
  ⟨if guard.value then result.data else RationalBits.zero,
    guard.work+control.work+untagged.work+signed.work+pair.work+result.work+7⟩

 theorem current_value {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (hprogram : program.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax r s)
    (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (current security bits program data sourcePrimary sourceBody source).data.decode =
      if RationalPackedRootProgram.Valid security data.metadata (word security source) then
        RationalPackedRootProgram.control security bits data.metadata (fun index => (sourcePrimary.get index).val)
          (fun index => (sourceBody.get index).val) (word security source) *
        RationalPackedRootProgram.untagged security bits data.metadata (word security source) *
        RationalPackedRootProgram.signed security bits data.metadata (word security source) else 0 := by
  simp only [current]
  by_cases h : (BinaryPackedRootGuard.current security data source).value = true
  · simp only [if_pos h,if_pos ((BinaryPackedRootGuard.current_value _ _ _).mp h),RationalBits.multiply_value,
      BinaryPackedRootFactors.control_value _ _ _ hprogram,BinaryPackedRootFactors.untagged_value,BinaryPackedRootFactors.signed_value]
  · simp only [if_neg h,if_neg (fun he => h ((BinaryPackedRootGuard.current_value _ _ _).mpr he)),RationalBits.zero_value]

noncomputable section


def heightPolynomial {r s : ℕ} (kept tags : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightedPointKernel.heightPolynomial program precision+
    BinaryPackedRootFactorResources.untaggedHeightPolynomial ((r+s)+kept) precision+
    BinaryRootSignedMassResources.heightPolynomial tags precision


def workPolynomial {r s : ℕ} (kept tags : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootGuard.workPolynomial ((r+s)+kept)+BinaryPackedRootFactorResources.controlWorkPolynomial kept program precision+
    BinaryPackedRootFactorResources.untaggedWorkPolynomial ((r+s)+kept) tags precision+
    BinaryPackedRootFactorResources.signedWorkPolynomial ((r+s)+kept) tags precision+
    2*RationalBits.primitiveWorkPolynomial (heightPolynomial kept tags program precision)+7

 theorem current_bounds {r s kept tags : ℕ} (security : ℕ) (precision : Polynomial ℕ)
    (program : BinaryWeightedPointKernel.Program r s) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    HeightBound (current security (precision.eval security) program data sourcePrimary sourceBody source).data.decode
      ((heightPolynomial kept tags program precision).eval security) ∧
    (current security (precision.eval security) program data sourcePrimary sourceBody source).work ≤
      (workPolynomial kept tags program precision).eval security := by
  let guard := BinaryPackedRootGuard.current security data source
  let control := BinaryPackedRootFactors.control security (precision.eval security) program data sourcePrimary sourceBody source
  let untagged := BinaryPackedRootFactors.untagged security (precision.eval security) data source
  let signed := BinaryPackedRootFactors.signed security (precision.eval security) data source
  let pair := RationalBits.multiply control.data untagged.data
  let result := RationalBits.multiply pair.data signed.data
  let H := (heightPolynomial kept tags program precision).eval security
  have hc := BinaryPackedRootFactorResources.control_bounds security precision program data sourcePrimary sourceBody source
  have hu := BinaryPackedRootFactorResources.untagged_bounds security precision data source
  have hs := BinaryPackedRootFactorResources.signed_bounds security precision data source
  have hpair : HeightBound pair.data.decode
      ((BinaryWeightedPointKernel.heightPolynomial program precision).eval security+
        (BinaryPackedRootFactorResources.untaggedHeightPolynomial ((r+s)+kept) precision).eval security) := by
    rw [RationalBits.multiply_value]
    exact hc.1.mul hu.1
  have ht : HeightBound result.data.decode H := by
    rw [RationalBits.multiply_value]
    simpa only [H,heightPolynomial,Polynomial.eval_add] using hpair.mul hs.1
  have hch : HeightBound control.data.decode H := hc.1.mono (by simp only [H,heightPolynomial,Polynomial.eval_add];omega)
  have huh : HeightBound untagged.data.decode H := hu.1.mono (by simp only [H,heightPolynomial,Polynomial.eval_add];omega)
  have hsh : HeightBound signed.data.decode H := hs.1.mono (by simp only [H,heightPolynomial,Polynomial.eval_add];omega)
  have wp := RationalBits.multiply_work control.data untagged.data H hch huh
  have wr := RationalBits.multiply_work pair.data signed.data H
    (hpair.mono (by simp only [H,heightPolynomial,Polynomial.eval_add];omega)) hsh
  constructor
  · change HeightBound (if guard.value then result.data else RationalBits.zero).decode H
    split_ifs
    · exact ht
    · exact HeightBound.zero.mono (Nat.zero_le _)
  · have wg := BinaryPackedRootGuard.current_work security data source
    change guard.work+control.work+untagged.work+signed.work+pair.work+result.work+7 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,RationalBits.primitiveWorkPolynomial_eval]
    dsimp only [guard,control,untagged,signed,pair,result] at wp wr ⊢
    dsimp only [H] at wp wr
    omega

end
end CurrentAFT.BinaryPackedRootScalar

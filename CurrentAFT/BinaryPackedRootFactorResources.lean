import CurrentAFT.BinaryPackedRootFactors

/-! Fixed-order closed resource polynomials for all packed root scalar factors. -/
namespace CurrentAFT.BinaryPackedRootFactorResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata BinaryPackedRootFactors
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def untaggedHeightPolynomial (groups : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (groups*2)*BinaryRootReferenceResources.heightPolynomial precision

def untaggedLeafWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*groups+tags*(3*tags+6*groups+34)+20+30*groups+20+3)+
    BinaryRootReferenceResources.workPolynomial precision

def untaggedWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteProduct.workPolynomial (groups*2) (BinaryRootReferenceResources.heightPolynomial precision)
    (untaggedLeafWorkPolynomial groups tags precision)

 theorem untagged_bounds {r s kept tags : ℕ} (security : ℕ) (precision : Polynomial ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    HeightBound (untagged security (precision.eval security) data source).data.decode
      ((untaggedHeightPolynomial ((r+s)+kept) precision).eval security) ∧
    (untagged security (precision.eval security) data source).work ≤
      (untaggedWorkPolynomial ((r+s)+kept) tags precision).eval security := by
  have leaf (index : Fin (((r+s)+kept)*2)) :
      HeightBound (untaggedFactor security (precision.eval security) data source index).data.decode
        ((BinaryRootReferenceResources.heightPolynomial precision).eval security) ∧
      (untaggedFactor security (precision.eval security) data source index).work ≤
        (untaggedLeafWorkPolynomial ((r+s)+kept) tags precision).eval security := by
    let pair := finProdFinEquiv.symm index
    let used := active data pair.1 pair.2
    let output := sourceEntry security source pair.1 pair.2.castSucc
    have href := BinaryRootReferenceResources.referenceEntry_polynomial_bounds security precision output.value.val
      (output.value.isLt.le.trans (BinaryRootReferenceResources.colors_bound security))
    constructor
    · change HeightBound (if used.value then _ else RationalBits.one).decode _
      split_ifs
      · exact href.1
      · exact HeightBound.one.mono (Nat.zero_le _)
    · have ha := active_work data pair.1 pair.2
      have ho := sourceEntry_work security source pair.1 pair.2.castSucc
      change used.work+output.work+(BinaryRootSignedMass.referenceEntry _ _ _).work+3 ≤ _
      simp only [untaggedLeafWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
      change used.work ≤ _ at ha
      change output.work ≤ _ at ho
      dsimp only [output,pair] at href ho ⊢
      omega
  constructor
  · simpa only [untaggedHeightPolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      BinaryFiniteProduct.current_height _ _ _ (fun index => (leaf index).1)
  · simpa only [untaggedWorkPolynomial,BinaryFiniteProduct.workPolynomial_eval] using
      BinaryFiniteProduct.current_work _ _ _ _ (fun index => (leaf index).1) (fun index => (leaf index).2)


def signedWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSignedMassResources.workPolynomial tags precision+Polynomial.C (tags*(3*tags+30*groups+27)+4)

 theorem signed_bounds {r s kept tags : ℕ} (security : ℕ) (precision : Polynomial ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    HeightBound (signed security (precision.eval security) data source).data.decode
      ((BinaryRootSignedMassResources.heightPolynomial tags precision).eval security) ∧
    (signed security (precision.eval security) data source).work ≤
      (signedWorkPolynomial ((r+s)+kept) tags precision).eval security := by
  have h := BinaryRootSignedMassResources.weightedEntry_polynomial_bounds security tags precision
    (taggedOutputs security data source).value le_rfl (fun index => by
      rw [taggedOutputs_get]
      unfold word
      exact (source.get _).isLt.le.trans (BinaryRootReferenceResources.colors_bound security))
  constructor
  · exact h.1
  · have hw := taggedOutputs_work security data source
    change (taggedOutputs security data source).work+(BinaryRootSignedMass.weightedEntry _ _ _).work+2 ≤ _
    simp only [signedWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega


def controlWorkPolynomial {r s : ℕ} (kept : ℕ) (program : BinaryWeightedPointKernel.Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightedPointKernel.workPolynomial program precision+
    Polynomial.C (r*(30*((r+s)+kept)+22)+s*(2*r+30*((r+s)+kept)+25)+7)

 theorem control_bounds {r s kept tags : ℕ} (security : ℕ) (precision : Polynomial ℕ)
    (program : BinaryWeightedPointKernel.Program r s) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    HeightBound (control security (precision.eval security) program data sourcePrimary sourceBody source).data.decode
      ((BinaryWeightedPointKernel.heightPolynomial program precision).eval security) ∧
    (control security (precision.eval security) program data sourcePrimary sourceBody source).work ≤
      (controlWorkPolynomial kept program precision).eval security := by
  have h := BinaryWeightedPointKernel.current_bounds security precision program sourcePrimary
    (primaryOutputs security source).value sourceBody (bodyOutputs security source).value
  constructor
  · exact h.1
  · have hp := primaryOutputs_work security source
    have hb := bodyOutputs_work security source
    change (primaryOutputs security source).work+(bodyOutputs security source).work+
      (BinaryWeightedPointKernel.current _ _ _ _ _ _ _).work+3 ≤ _
    simp only [controlWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

end
end CurrentAFT.BinaryPackedRootFactorResources

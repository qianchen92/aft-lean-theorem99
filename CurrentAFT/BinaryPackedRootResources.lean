import CurrentAFT.BinaryPackedRootCurrent

/-! Polynomial work for the entire actual packed coefficient producer,
including all local family production and all joint source buffers. -/
namespace CurrentAFT.BinaryPackedRootResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms BinaryPackedRootMetadata BinaryPackedRootCurrent
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def localLeafWorkPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootGroupProgram.workPolynomial order programs precision queueBits+Polynomial.C (93*groups+74)

 theorem localFamily_bounds {r s kept tags : ℕ} (security order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin ((r+s)+kept))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    HeightBound (localFamily security (precision.eval security) order programs queue data source index arity colors centers).value.decode
      ((BinaryRootGroupProgram.heightPolynomial order programs precision queueBits).eval security) ∧
    (localFamily security (precision.eval security) order programs queue data source index arity colors centers).work ≤
      (localLeafWorkPolynomial order ((r+s)+kept) programs precision queueBits).eval security := by
  let role := readVector RationalRootGroupProgram.LocalRole.primary data.roles index
  let input := sourceGroup security source index
  have ht := BinaryRootGroupProgram.localTable_bounds security order programs precision queueBits queue hq role.value input.value arity colors centers hc hb
  constructor
  · exact ht.1
  · have wr := readVector_work RationalRootGroupProgram.LocalRole.primary data.roles index
    have wi := sourceGroup_work security source index
    change role.work+input.work+(BinaryRootGroupProgram.localTable _ _ _ _ _ _ _ _ _ _).work+3 ≤ _
    simp only [localLeafWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    change role.work ≤ _ at wr
    change input.work ≤ _ at wi
    dsimp only [role,input] at ht wr wi ⊢
    omega


def localHeightPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyPower.heightPolynomial order programs.programs (BinaryRootGroupProgram.heightPolynomial order programs precision queueBits) groups

def localWorkPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyPower.workPolynomial order programs.programs (BinaryRootGroupProgram.heightPolynomial order programs precision queueBits)
    (localLeafWorkPolynomial order groups programs precision queueBits) groups

 theorem localProduct_bounds {r s kept tags : ℕ} (security order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security)
    (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    HeightBound (localProduct security (precision.eval security) order programs queue data source arity colors centers).value.decode
      ((localHeightPolynomial order ((r+s)+kept) programs precision queueBits).eval security) ∧
    (localProduct security (precision.eval security) order programs queue data source arity colors centers).work ≤
      (localWorkPolynomial order ((r+s)+kept) programs precision queueBits).eval security := by
  exact BinaryFamilyWordProduct.product_polynomial_bounds order (PublicParameterProgram.modulus security).count security programs.programs
    ((r+s)+kept) (localFamily security (precision.eval security) order programs queue data source)
    (BinaryRootGroupProgram.heightPolynomial order programs precision queueBits)
    (localLeafWorkPolynomial order ((r+s)+kept) programs precision queueBits)
    (fun index arity colors centers hc hb => localFamily_bounds security order programs precision queueBits queue hq data source index arity colors centers hc hb)
    arity colors centers hc hb


def summandHeightPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootScalar.heightPolynomial kept tags pointProgram precision+
    localHeightPolynomial order ((r+s)+kept) programs precision queueBits

def summandWorkPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootScalar.workPolynomial kept tags pointProgram precision+
    localWorkPolynomial order ((r+s)+kept) programs precision queueBits+
    RationalBits.primitiveWorkPolynomial (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)+3

 theorem summand_bounds {r s kept tags : ℕ} (security order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    HeightBound (summand security (precision.eval security) order programs pointProgram queue data sourcePrimary sourceBody source arity colors centers).value.decode
      ((summandHeightPolynomial order kept tags programs pointProgram precision queueBits).eval security) ∧
    (summand security (precision.eval security) order programs pointProgram queue data sourcePrimary sourceBody source arity colors centers).work ≤
      (summandWorkPolynomial order kept tags programs pointProgram precision queueBits).eval security := by
  let scalar := BinaryPackedRootScalar.current security (precision.eval security) pointProgram data sourcePrimary sourceBody source
  let family := localProduct security (precision.eval security) order programs queue data source arity colors centers
  have hs := BinaryPackedRootScalar.current_bounds security precision pointProgram data sourcePrimary sourceBody source
  have hf := localProduct_bounds security order programs precision queueBits queue hq data source arity colors centers hc hb
  let H := (summandHeightPolynomial order kept tags programs pointProgram precision queueBits).eval security
  have hm := RationalBits.multiply_work scalar.data family.value H
    (hs.1.mono (by simp only [H,summandHeightPolynomial,Polynomial.eval_add];omega))
    (hf.1.mono (by simp only [H,summandHeightPolynomial,Polynomial.eval_add];omega))
  constructor
  · change HeightBound (RationalBits.multiply scalar.data family.value).data.decode _
    rw [RationalBits.multiply_value]
    simpa only [summandHeightPolynomial,Polynomial.eval_add] using hs.1.mul hf.1
  · change scalar.work+family.work+(RationalBits.multiply scalar.data family.value).work+3 ≤ _
    simp only [summandWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,RationalBits.primitiveWorkPolynomial_eval]
    dsimp only [scalar,family,H] at hm ⊢
    omega


def heightPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootSum.heightPolynomial ((r+s)+kept)
    (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)

def workPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootSum.workPolynomial ((r+s)+kept)
    (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)
    (summandWorkPolynomial order kept tags programs pointProgram precision queueBits)+1

 theorem current_bounds {r s kept tags : ℕ} (security order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ)
    (queue : IntegerBits) (hq : queue.digits.length ≤ queueBits.eval security) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i < (PublicParameterProgram.modulus security).count)
    (hb : ∀ i, centers.get i < (PublicParameterProgram.modulus security).count) :
    HeightBound (current security (precision.eval security) order programs pointProgram queue data sourcePrimary sourceBody arity colors centers).value.decode
      ((heightPolynomial order kept tags programs pointProgram precision queueBits).eval security) ∧
    (current security (precision.eval security) order programs pointProgram queue data sourcePrimary sourceBody arity colors centers).work ≤
      (workPolynomial order kept tags programs pointProgram precision queueBits).eval security := by
  have hs (source : BinaryPackedRootSum.Source security ((r+s)+kept)) :=
    summand_bounds security order programs pointProgram precision queueBits queue hq data sourcePrimary sourceBody source arity colors centers hc hb
  let kernel : BinaryPackedRootSum.Source security ((r+s)+kept) → RationalResult := fun input =>
    let value := summand security (precision.eval security) order programs pointProgram queue data sourcePrimary sourceBody input arity colors centers
    ⟨value.value,value.work⟩
  have h := BinaryPackedRootSum.current_polynomial_bounds security ((r+s)+kept) ((r+s)+kept) le_rfl kernel
    (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)
    (summandWorkPolynomial order kept tags programs pointProgram precision queueBits) (fun source => (hs source).1) (fun source => (hs source).2)
  refine ⟨h.1,?_⟩
  change (BinaryPackedRootSum.current security ((r+s)+kept) kernel).work+1 ≤ _
  simpa only [workPolynomial,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right h.2 1

end
end CurrentAFT.BinaryPackedRootResources

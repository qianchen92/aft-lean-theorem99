import CurrentAFT.BinaryRootGroupProgram
import CurrentAFT.BinaryFixedPointPrograms
import CurrentAFT.BinaryFiniteCoefficient
import CurrentAFT.RationalFullResponseProgram

/-! # Finite stored full-response metadata and its genuine weighted point basis -/
namespace CurrentAFT.BinaryFullResponseData
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Data (order : ℕ) where
  groups : BinaryRootGroupProgram.Data order
  points : List (BinaryFixedPointPrograms.Entry order)

def Correct {order : ℕ} (data : Data order) : Prop :=
  BinaryRootGroupProgram.Correct data.groups ∧ BinaryFixedPointPrograms.Correct order data.points ∧ BinaryFixedPointPrograms.Complete order data.points

def finiteBasis (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) : BinaryFiniteCoefficient.FiniteProgram security order :=
  fun output inputs centers =>
    let checked := FixedFamilyPrograms.matchArity order output source
    if h : checked.value=true then
      let same := (FixedFamilyPrograms.matchArity_value order output source).mp h
      let result := BinaryFixedPointPrograms.current security bits order data.points source sourcePrimary
        (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.1.val) same) inputs)
        sourceBody (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.2.val) same) centers)
      ⟨result.data,checked.work+result.work+3⟩
    else ⟨zero,checked.work+2⟩

def basis (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finiteBasis security bits order data source sourcePrimary sourceBody)

noncomputable section
theorem exists_data (order : ℕ) : ∃ data : Data order, Correct data := by
  obtain ⟨groups,hgroups⟩ := BinaryRootGroupProgram.exists_data order
  obtain ⟨points,hpoints,hcomplete⟩ := BinaryFixedPointPrograms.exists_complete order
  exact ⟨⟨groups,points⟩,hgroups,hpoints,hcomplete⟩

theorem finiteBasis_value (security bits order : ℕ) (data : Data order) (hdata : Correct data) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) (output : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) output.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) output.val.2.val) :
    (finiteBasis security bits order data source sourcePrimary sourceBody output inputs centers).data.decode=
      RationalFullResponseProgram.basis security bits order source (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) output (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  by_cases h : (FixedFamilyPrograms.matchArity order output source).value=true
  · have he := (FixedFamilyPrograms.matchArity_value order output source).mp h
    simp only [finiteBasis,dif_pos h,RationalFullResponseProgram.basis,dif_pos he]
    rw [BinaryFixedPointPrograms.current_value security bits order data.points hdata.2.1 hdata.2.2]
    congr 1
  · have hn : output≠source := fun he => h ((FixedFamilyPrograms.matchArity_value order output source).mpr he)
    simp only [finiteBasis,dif_neg h,RationalFullResponseProgram.basis,dif_neg hn,zero_value]

theorem basis_value (security bits order : ℕ) (data : Data order) (hdata : Correct data) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) (output : TruncatedArity order)
    (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (basis security bits order data source sourcePrimary sourceBody output inputs centers).value.decode=
      RationalFullResponseProgram.basis security bits order source (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) output inputs.get centers.get :=
  BinaryFiniteCoefficient.lift_value security order (finiteBasis security bits order data source sourcePrimary sourceBody) _
    (finiteBasis_value security bits order data hdata source sourcePrimary sourceBody) output inputs centers hi hb

noncomputable def basisHeightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedPointPrograms.heightPolynomial order data.points precision
noncomputable def finiteBasisWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedPointPrograms.workPolynomial order data.points precision+Polynomial.C (12*order+8)
noncomputable def basisWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteBasisWorkPolynomial order data precision)

theorem finiteBasis_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) (output : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) output.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) output.val.2.val) :
    HeightBound (finiteBasis security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).data.decode
      ((basisHeightPolynomial order data precision).eval security) ∧
    (finiteBasis security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).work ≤
      (finiteBasisWorkPolynomial order data precision).eval security := by
  have wm := FixedFamilyPrograms.matchArity_work order output source
  by_cases h : (FixedFamilyPrograms.matchArity order output source).value=true
  · have he := (FixedFamilyPrograms.matchArity_value order output source).mp h
    have hp := BinaryFixedPointPrograms.current_bounds security order data.points precision source sourcePrimary
      (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.1.val) he) inputs)
      sourceBody (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.2.val) he) centers)
    constructor
    · simpa only [finiteBasis,dif_pos h] using hp.1
    · rw [finiteBasis,dif_pos h]
      change (FixedFamilyPrograms.matchArity order output source).work+_+3 ≤ _
      simp only [finiteBasisWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
      omega
  · constructor
    · simp only [finiteBasis,dif_neg h,zero_value]
      exact HeightBound.zero.mono (Nat.zero_le _)
    · rw [finiteBasis,dif_neg h]
      change (FixedFamilyPrograms.matchArity order output source).work+2 ≤ _
      simp only [finiteBasisWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
      omega

theorem basis_bounds (security order : ℕ) (data : Data order) (precision : Polynomial ℕ) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) (output : TruncatedArity order)
    (inputs : Vector ℕ output.val.1.val) (centers : Vector ℕ output.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (basis security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).value.decode
      ((basisHeightPolynomial order data precision).eval security) ∧
    (basis security (precision.eval security) order data source sourcePrimary sourceBody output inputs centers).work ≤
      (basisWorkPolynomial order data precision).eval security := by
  exact BinaryFiniteCoefficient.lift_bounds security order _ _ (finiteBasis security (precision.eval security) order data source sourcePrimary sourceBody)
    (fun output inputs centers => (finiteBasis_bounds security order data precision source sourcePrimary sourceBody output inputs centers).1)
    (fun output inputs centers => (finiteBasis_bounds security order data precision source sourcePrimary sourceBody output inputs centers).2) output inputs centers hi hb

end
end CurrentAFT.BinaryFullResponseData

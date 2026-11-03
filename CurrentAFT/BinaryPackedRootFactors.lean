import CurrentAFT.BinaryPackedRootMetadata
import CurrentAFT.BinaryWeightedPointKernel

/-! The three actual scalar multipliers of a packed joint source column:
reference-weighted canonical point input, untagged root marginals, and centered
joint tagged cycle mass. All dynamic coordinates are read from stored arrays. -/
namespace CurrentAFT.BinaryPackedRootFactors
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def untaggedFactor {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin (((r+s)+kept)*2)) : RationalResult :=
  let pair := finProdFinEquiv.symm index
  let used := active data pair.1 pair.2
  let output := sourceEntry security source pair.1 pair.2.castSucc
  let reference := BinaryRootSignedMass.referenceEntry security bits output.value.val
  ⟨if used.value then reference.data else RationalBits.one,used.work+output.work+reference.work+3⟩


def untagged {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  BinaryFiniteProduct.current (((r+s)+kept)*2) (untaggedFactor security bits data source)

 theorem untaggedFactor_value {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin (((r+s)+kept)*2)) :
    (untaggedFactor security bits data source index).data.decode =
      if RationalPackedRootProgram.rootActive (data.metadata.roles (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2 ∧
          ¬∃ tag, data.metadata.taggedSlots tag = finProdFinEquiv.symm index then
        RootSignedMassProgram.referenceEntry security bits
          (word security source (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2.castSucc) else 1 := by
  simp only [untaggedFactor]
  by_cases h : (active data (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).value = true
  · simp only [if_pos h,if_pos ((active_value _ _ _).mp h),BinaryRootSignedMass.referenceEntry_value,sourceEntry_value,word]
  · simp only [if_neg h,if_neg (fun he => h ((active_value _ _ _).mpr he)),RationalBits.one_value]

 theorem untagged_value {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (untagged security bits data source).data.decode = RationalPackedRootProgram.untagged security bits data.metadata (word security source) := by
  rw [untagged,BinaryFiniteProduct.current_value]
  rw [← Equiv.prod_comp finProdFinEquiv (fun index => (untaggedFactor security bits data source index).data.decode),Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro group _
  apply Finset.prod_congr rfl
  intro slot _
  simp only [untaggedFactor_value,Equiv.symm_apply_apply]


def taggedOutputs {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CountedValue (Vector ℕ tags) :=
  storeData tags (fun index =>
    let position := readVector (taggedDefault data.tagged index) data.tagged index
    let output := sourceEntry security source position.value.1 position.value.2.castSucc
    ⟨output.value.val,position.work+output.work+2⟩)

 theorem taggedOutputs_get {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin tags) :
    (taggedOutputs security data source).value.get index =
      word security source (data.metadata.taggedSlots index).1 (data.metadata.taggedSlots index).2.castSucc := by
  simp only [taggedOutputs,storeData_get,readVector_value,sourceEntry_value,word,Data.metadata]

 theorem taggedOutputs_work {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (taggedOutputs security data source).work ≤ tags*(3*tags+30*((r+s)+kept)+27)+2 := by
  apply storeData_work
  intro index
  have hp := readVector_work (taggedDefault data.tagged index) data.tagged index
  have ho := sourceEntry_work security source (readVector (taggedDefault data.tagged index) data.tagged index).value.1
    (readVector (taggedDefault data.tagged index) data.tagged index).value.2.castSucc
  change _+_+2 ≤ _
  omega


def signed {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let outputs := taggedOutputs security data source
  let result := BinaryRootSignedMass.weightedEntry security bits outputs.value
  ⟨result.data,outputs.work+result.work+2⟩

 theorem signed_value {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (signed security bits data source).data.decode = RationalPackedRootProgram.signed security bits data.metadata (word security source) := by
  change (BinaryRootSignedMass.weightedEntry _ _ _).data.decode = _
  rw [BinaryRootSignedMass.weightedEntry_value]
  apply congrArg (RootSignedMassProgram.weightedEntry security bits tags)
  funext index
  exact taggedOutputs_get security data source index


def primaryOutputs {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CountedValue (Vector (Color security) r) :=
  storeData r (fun index => sourceEntry security source (RationalPackedRootProgram.primaryGroup r s kept index) 2)


def bodyOutputs {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CountedValue (Vector (Color security) s) :=
  storeData s (fun index =>
    let position := addCounter r index.val
    let output := sourceEntry security source ⟨position.count,by rw [addCounter_value];have := index.isLt;omega⟩ 1
    ⟨output.value,position.work+output.work+2⟩)

 theorem primaryOutputs_get {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin r) :
    ((primaryOutputs security source).value.get index).val =
      word security source (RationalPackedRootProgram.primaryGroup r s kept index) 2 := by
  simp only [primaryOutputs,storeData_get,sourceEntry_value,word]

 theorem bodyOutputs_get {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin s) :
    ((bodyOutputs security source).value.get index).val =
      word security source (RationalPackedRootProgram.ordinaryGroup r s kept index) 1 := by
  simp only [bodyOutputs,storeData_get,sourceEntry_value,word]
  congr 2
  apply Fin.ext
  simp only [finProdFinEquiv_apply_val,addCounter_value,RationalPackedRootProgram.ordinaryGroup]

 theorem primaryOutputs_work {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    (primaryOutputs security source).work ≤ r*(30*((r+s)+kept)+22)+2 :=
  storeData_work _ _ _ (fun _ => sourceEntry_work security source _ _)

 theorem bodyOutputs_work {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    (bodyOutputs security source).work ≤ s*(2*r+30*((r+s)+kept)+25)+2 := by
  apply storeData_work
  intro index
  have hp := addCounter_work r index.val
  have ho := sourceEntry_work security source (⟨(addCounter r index.val).count,by rw [addCounter_value];have := index.isLt;omega⟩ : Fin ((r+s)+kept)) 1
  change _+_+2 ≤ _
  omega


def control {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (_data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let colors := primaryOutputs security source
  let centers := bodyOutputs security source
  let result := BinaryWeightedPointKernel.current security bits program sourcePrimary colors.value sourceBody centers.value
  ⟨result.data,colors.work+centers.work+result.work+3⟩

 theorem control_value {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (hprogram : program.meaning RationalBits.decode = BinaryWeightedPointKernel.pointSyntax r s)
    (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) :
    (control security bits program data sourcePrimary sourceBody source).data.decode =
      RationalPackedRootProgram.control security bits data.metadata (fun index => (sourcePrimary.get index).val)
        (fun index => (sourceBody.get index).val) (word security source) := by
  change (BinaryWeightedPointKernel.current _ _ _ _ _ _ _).data.decode = _
  rw [BinaryWeightedPointKernel.current_value _ _ _ hprogram]
  unfold RationalPackedRootProgram.control
  congr 1 <;> funext index
  · exact primaryOutputs_get security source index
  · exact bodyOutputs_get security source index

end CurrentAFT.BinaryPackedRootFactors

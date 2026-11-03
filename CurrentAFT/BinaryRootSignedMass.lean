import CurrentAFT.BinarySparseCycleAverage
import CurrentAFT.BinaryCycleTest
import CurrentAFT.CurrentEdgeDrawProgram
import CurrentAFT.RootSignedMassProgram

/-! Actual binary reference and centered root masses. Only selected sites and
their touched-edge Gaussian words are enumerated; no root atom is inverted. -/
namespace CurrentAFT.BinaryRootSignedMass
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def bodyProgram (security : ℕ) : UnaryCounterResult :=
  let q := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let scale := powerCounter base.count 96
  let result := multiplyCounter q.count scale.count
  ⟨result.count,q.work+base.work+scale.work+result.work+4⟩

 theorem bodyProgram_value (security : ℕ) : (bodyProgram security).count = CurrentCycleEntryProgram.bodyCount security := by
  simp only [bodyProgram,multiplyCounter_value,powerCounter_value,addCounter_value,CurrentCycleEntryProgram.bodyCount]

 theorem bodyProgram_positive (security : ℕ) : 0 < (bodyProgram security).count := by
  rw [bodyProgram_value,CurrentCycleEntryProgram.bodyCount,PublicParameterProgram.modulus_value]
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (pow_pos (by omega) _)


def referenceEntry (security bits output : ℕ) : RationalResult :=
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let expected := storeData 1 (fun _ => (⟨output,1⟩ : CountedValue ℕ))
  let result := BinarySparseCycleAverage.current security cutoff.quotient bits body.count 1 (bodyProgram_positive security)
    (BinaryCycleTest.point code.digits expected.value)
  ⟨result.data,body.work+cutoff.work+q.work+code.work+expected.work+result.work+6⟩

 theorem referenceEntry_value (security bits output : ℕ) :
    (referenceEntry security bits output).data.decode = RootSignedMassProgram.referenceEntry security bits output := by
  have hq : 0 < value (canonicalCounter (PublicParameterProgram.modulus security).count).digits := by
    rw [canonicalCounter_value,PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have ht : ∀ roots, (BinaryCycleTest.point
      (canonicalCounter (PublicParameterProgram.modulus security).count).digits
      (storeData 1 (fun _ => (⟨output,1⟩ : CountedValue ℕ))).value roots).data.decode =
      CurrentCycleEntryProgram.pointTest (PublicParameterProgram.modulus security).count 1 (fun _ => output)
        (fun slot => (roots.get slot).decode) := by
    intro roots
    rw [BinaryCycleTest.point_value _ hq,canonicalCounter_value]
    congr 1
    funext slot
    rw [storeData_get]
  change (BinarySparseCycleAverage.current _ _ _ _ _ _ _).data.decode = _
  rw [BinarySparseCycleAverage.current_value _ _ _ _ _ _ _ _ ht]
  simp only [RootSignedMassProgram.referenceEntry,CurrentCycleEntryProgram.selectedEntry,
    CurrentEdgeDrawProgram.cutoff_value]
  exact congrArg (fun body => CyclePatternProgram.averagedEvaluate security (DiffuseProfiles.edgeCutoff security) bits body 1
    (fun _ => CurrentCycleEntryProgram.pointTest (PublicParameterProgram.modulus security).count 1 (fun _ => output))) (bodyProgram_value security)


def references {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) :
    CountedValue (Vector RationalBits count) :=
  storeData count (fun slot =>
    let expected := readVector 0 output slot
    let mass := referenceEntry security bits expected.value
    ⟨mass.data,expected.work+mass.work+2⟩)

 theorem references_value {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) (slot : Fin count) :
    ((references security bits output).value.get slot).decode = RootSignedMassProgram.referenceEntry security bits (output.get slot) := by
  simp only [references,storeData_get,referenceEntry_value,readVector_value]


def weightedEntry {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) : RationalResult :=
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let masses := references security bits output
  let result := BinarySparseCycleAverage.current security cutoff.quotient bits body.count count (bodyProgram_positive security)
    (BinaryCycleTest.signed code.digits output masses.value)
  ⟨result.data,body.work+cutoff.work+q.work+code.work+masses.work+result.work+6⟩

 theorem weightedEntry_value {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) :
    (weightedEntry security bits output).data.decode = RootSignedMassProgram.weightedEntry security bits count output.get := by
  have hq : 0 < value (canonicalCounter (PublicParameterProgram.modulus security).count).digits := by
    rw [canonicalCounter_value,PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have ht : ∀ roots, (BinaryCycleTest.signed
      (canonicalCounter (PublicParameterProgram.modulus security).count).digits output (references security bits output).value roots).data.decode =
      RootSignedMassProgram.signedTest security bits count output.get (fun slot => (roots.get slot).decode) := by
    intro roots
    rw [BinaryCycleTest.signed_value _ hq]
    simp only [RootSignedMassProgram.signedTest,canonicalCounter_value,references_value]
  change (BinarySparseCycleAverage.current _ _ _ _ _ _ _).data.decode = _
  rw [BinarySparseCycleAverage.current_value _ _ _ _ _ _ _ _ ht]
  simp only [RootSignedMassProgram.weightedEntry,CurrentEdgeDrawProgram.cutoff_value]
  exact congrArg (fun body => CyclePatternProgram.averagedEvaluate security (DiffuseProfiles.edgeCutoff security) bits body count
    (fun _ => RootSignedMassProgram.signedTest security bits count output.get)) (bodyProgram_value security)

end CurrentAFT.BinaryRootSignedMass

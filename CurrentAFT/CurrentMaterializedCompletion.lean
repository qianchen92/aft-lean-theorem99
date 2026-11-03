import CurrentAFT.CappedPublicRejection
import CurrentAFT.CurrentCompletionResources

/-! The completed public sample retains every actual buffer required by the
integer affine emitter. The semantic sample is only its decoder. -/
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT GaussianSource BinaryArithmetic RationalRejectionProgram
open CurrentCoreProposal CurrentAffineData
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentChartsDraw.drawStored CurrentEdgeDrawProgram.draw
  CappedPublicRejection.current

structure Result (security : ℕ) where
  core : MaterializedCore security
  charts : Vector (Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))) (Parameters.legCount security)
  edge : Window (DiffuseProfiles.edgeCutoff security)

def Result.sample {security : ℕ} (result : Result security) : CurrentPublicAffineSample.Sample security :=
  ((result.core.core, result.charts.get), result.edge)

def complete (security : ℕ) (input : Option (MaterializedCore security)) (precision bits edgeBits : ℕ)
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) : CountedValue (Option (Result security)) :=
  match input with
  | none => ⟨none, 1⟩
  | some core =>
    let charts := CurrentChartsDraw.drawStored security core.inputs precision bits word.1
    let edge := CurrentEdgeDrawProgram.draw security edgeBits word.2
    ⟨some ⟨core, charts.value, edge.value⟩, charts.work+edge.work+3⟩

theorem complete_value (security : ℕ) (input : Option (MaterializedCore security)) (precision bits edgeBits : ℕ)
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) :
    Option.map Result.sample (complete security input precision bits edgeBits word).value =
      (CurrentPublicCompletion.complete security (Option.map MaterializedCore.cached input) precision bits edgeBits word).value := by
  cases input with
  | none => rfl
  | some core => rfl

theorem complete_work_eq (security : ℕ) (input : Option (MaterializedCore security)) (precision bits edgeBits : ℕ)
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) :
    (complete security input precision bits edgeBits word).work =
      (CurrentPublicCompletion.complete security (Option.map MaterializedCore.cached input) precision bits edgeBits word).work := by
  cases input <;> rfl

abbrev Tapes (security : ℕ) := CappedPublicRejection.Tapes security × CurrentPublicCompletion.Tapes security security security

def current (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (word : Tapes security) :
    CountedValue (Option (Result security)) :=
  let core := CappedPublicRejection.current security order table word.1
  let result := complete security core.value security security security word.2
  ⟨result.value, core.work+result.work+2⟩

noncomputable section
open scoped Classical
open Polynomial

def workPolynomial (order : ℕ) (tableBound : Polynomial ℕ) : Polynomial ℕ :=
  CappedPublicRejection.workPolynomial order tableBound+CurrentCompletionResources.workPolynomial X X X+2

theorem polynomial_work (security order : ℕ) (tableBound : Polynomial ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (ht : ∀ block word, RationalNumerics.HeightBound ((table.get block).get word).decode (tableBound.eval security))
    (word : Tapes security) :
    (current security order table word).work ≤ (workPolynomial order tableBound).eval security := by
  have hc := CappedPublicRejection.polynomial_work security order tableBound table ht word.1
  have hp := CurrentCompletionResources.complete_polynomial_work security X X X
    (Option.map MaterializedCore.cached (CappedPublicRejection.current security order table word.1).value)
  rw [eval_X] at hp
  have hp := hp word.2
  rw [← complete_work_eq] at hp
  change (CappedPublicRejection.current security order table word.1).work+
    (complete security (CappedPublicRejection.current security order table word.1).value security security security word.2).work+2 ≤ _
  simp only [workPolynomial, eval_add, eval_ofNat]
  omega

end
end CurrentAFT.CurrentMaterializedCompletion

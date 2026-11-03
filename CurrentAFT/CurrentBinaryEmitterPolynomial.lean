import CurrentAFT.CurrentBinaryEmitterResources
import CurrentAFT.UniformPolynomialBound

/-! A single polynomial bounds the complete executed integer emitter,
uniformly over every stored public record, including invalid records. -/
namespace CurrentAFT.CurrentBinaryEmitterPolynomial
open AFT BinaryArithmetic CurrentEmissionMetadata CurrentProposalResources CurrentBinaryEmitterResources
set_option maxHeartbeats 100000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section

 theorem metadata_work (security : ℕ) : (current security).work ≤
    (metadataWorkPolynomial + 8*countPolynomial+13).eval security := by
  let sizes := CurrentProposalDimensions.current security
  have hw := CurrentProposalResources.metadata_work security
  have hb := (count_bounds security).2.2.2.1
  have hd := (count_bounds security).2.2.2.2
  have hbe := subtractCounter_work_left sizes.body 1
  have he := subtractCounter_work_left sizes.dimension 1
  have hr := subtractCounter_work_left sizes.body sizes.legs
  have hc := subtractCounter_work_left (subtractCounter sizes.body sizes.legs).count sizes.colors
  have hrs : (subtractCounter sizes.body sizes.legs).count ≤ sizes.body := by
    rw [subtractCounter_value]; exact Nat.sub_le _ _
  unfold CurrentEmissionMetadata.current
  change sizes.work + (subtractCounter sizes.body 1).work + (subtractCounter sizes.dimension 1).work +
    (subtractCounter sizes.body sizes.legs).work + (subtractCounter (subtractCounter sizes.body sizes.legs).count sizes.colors).work + 5 ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  dsimp only [sizes] at *
  omega

private theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (h : ∀ security, resource security ≤ polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,h⟩

attribute [local irreducible] UniformPolynomialBound

 theorem hcontrols_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).controls) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).1)

 theorem hlegs_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).legs) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.1)

 theorem hcolors_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).colors) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.1)

 theorem hbody_uniform : UniformPolynomialBound (fun n => (CurrentProposalDimensions.current n).body) :=
    of_bound _ countPolynomial (fun n => (count_bounds n).2.2.2.1)

 theorem hedge_uniform : UniformPolynomialBound (fun n => (current n).edges) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).2.1
    have hd := (count_bounds n).2.2.2.2
    omega)

 theorem hbodyedge_uniform : UniformPolynomialBound (fun n => (current n).bodyEdges) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).1
    have hd := (count_bounds n).2.2.2.1
    omega)

 theorem hrest_uniform : UniformPolynomialBound (fun n => (current n).rest) := of_bound _ countPolynomial (fun n => by
    have h := (current_counts n).2.2.1
    have hd := (count_bounds n).2.2.2.1
    omega)

 theorem hq_uniform : UniformPolynomialBound Parameters.modulus := of_bound _ countPolynomial (fun n => by
    have h := (count_bounds n).2.2.1
    simpa only [(CurrentProposalDimensions.current_values n).1] using h)

 theorem hl_uniform : UniformPolynomialBound Parameters.legCount := of_bound _ countPolynomial (fun n => by
    have h := (count_bounds n).2.1
    simpa only [(CurrentProposalDimensions.current_values n).2.1] using h)

 theorem hm_uniform : UniformPolynomialBound (fun n => (current n).work) :=
    of_bound _ (metadataWorkPolynomial + 8*countPolynomial+13) metadata_work

 theorem hp_uniform : UniformPolynomialBound PublicParameterProgram.workBound := of_bound _ PublicParameterProgram.workPolynomial (fun n => by
    rw [PublicParameterProgram.workPolynomial_eval])

 theorem hs_uniform : UniformPolynomialBound CurrentPublicShiftProgram.workBound := of_bound _ shiftWorkPolynomial (fun n => by
    rw [shiftWorkPolynomial_eval])

attribute [local irreducible] Nat.add Nat.mul Nat.pow

macro "resource_finish" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact hcontrols_uniform
    | exact hlegs_uniform
    | exact hcolors_uniform
    | exact hbody_uniform
    | exact hedge_uniform
    | exact hbodyedge_uniform
    | exact hrest_uniform
    | exact hq_uniform
    | exact hl_uniform
    | exact hm_uniform
    | exact hp_uniform
    | exact hs_uniform
    | exact UniformPolynomialBound.identity
    | exact UniformPolynomialBound.constant _
    | apply UniformPolynomialBound.pow
    | apply UniformPolynomialBound.mul
    | apply UniformPolynomialBound.add)

 theorem operand_uniform : UniformPolynomialBound operandBits := by
  unfold operandBits
  resource_finish

 theorem field_uniform : UniformPolynomialBound fieldWork := by
  unfold fieldWork CurrentBinaryLoadColumns.Legs
  resource_finish

 theorem shift_uniform : UniformPolynomialBound shiftWork := by
  unfold shiftWork CurrentBinaryLoadColumns.Legs
  resource_finish

 theorem matrix_uniform : UniformPolynomialBound (fun n => CurrentBinaryLoadResources.matrixWork n (operandBits n)) := by
  have ho := operand_uniform
  unfold CurrentBinaryLoadResources.matrixWork CurrentBinaryLoadResources.entryWork
  dsimp only [CurrentBinaryLoadColumns.Legs, CurrentBinaryLoadColumns.Body]
  resource_finish

 theorem offset_uniform : UniformPolynomialBound (fun n => CurrentBinaryOffsetResources.loadWork n (operandBits n)) := by
  have ho := operand_uniform
  unfold CurrentBinaryOffsetResources.loadWork CurrentBinaryOffsetResources.entryWork CurrentBinaryBaselineResources.readWork
  dsimp only [CurrentBinaryLoadColumns.Legs, CurrentBinaryLoadColumns.Body]
  resource_finish

 theorem inverse_uniform {count modulus bits : ℕ → ℕ}
    (hc : UniformPolynomialBound count) (hq : UniformPolynomialBound modulus) (hb : UniformPolynomialBound bits) :
    UniformPolynomialBound (fun n => binaryRoundingInverseWork (count n) (modulus n) (bits n)) := by
  unfold binaryRoundingInverseWork binaryShiftedLoadWork binaryPathInverseWork
  resource_finish

 theorem assembled_uniform : UniformPolynomialBound assembledWork := by
  have hf := field_uniform
  have hs := shift_uniform
  have hm := matrix_uniform
  have ho := offset_uniform
  have hi := inverse_uniform hedge_uniform hq_uniform (operand_uniform.add (UniformPolynomialBound.constant 3))
  unfold assembledWork
  resource_finish

 theorem fallback_uniform : UniformPolynomialBound fallbackWork := by
  unfold fallbackWork
  dsimp only [CurrentBinaryAffinePrimitives.Size]
  resource_finish

 theorem guard_uniform : UniformPolynomialBound guardWork := by
  have hg : UniformPolynomialBound BinaryCoreCharge.workPolynomial.eval := UniformPolynomialBound.polynomial _
  unfold guardWork
  resource_finish

 theorem work_uniform : UniformPolynomialBound workBound := by
  unfold workBound
  exact ((assembled_uniform.add fallback_uniform).add guard_uniform).add (UniformPolynomialBound.constant 2)

 theorem work_exists : ∃ polynomial : Polynomial ℕ, ∀ security, workBound security ≤ polynomial.eval security := by
  simpa only [UniformPolynomialBound] using work_uniform

noncomputable def workPolynomial : Polynomial ℕ := Classical.choose work_exists

 theorem polynomial_work (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    (CurrentBinaryAffineEmitter.emit security layout input).work ≤ workPolynomial.eval security :=
  (emit_work security layout input).trans (Classical.choose_spec work_exists security)

end
end CurrentAFT.CurrentBinaryEmitterPolynomial

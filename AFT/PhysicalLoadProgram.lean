import AFT.IntegerCoordinateProgram
import AFT.PhysicalAffineLoad

/-! # Integer programs for the physical edge loads and initial offset -/
namespace AFT
open scoped BigOperators

 def physicalEdgeNumberingProgram (legs bodyEdges count : ℕ) (hcount : legs*2+bodyEdges=count) :
    ((Fin legs×Fin 2)⊕Fin bodyEdges)≃Fin count :=
  (blockEdgeNumbering legs bodyEdges).trans (finCongr hcount)

 def physicalVertexNumberingProgram (legs rest count : ℕ) (hcount : legs*3+rest=count+1) :
    (Sigma (blockSlotsProgram legs rest))≃Fin (count+1) :=
  (blockVertexNumbering legs rest).trans (finCongr hcount)

/-- Scale/shear the two leg edges, compute the body path once, then emit all vertices. -/
def physicalEdgeLoadProgram (legs rest bodyEdges count : ℕ)
    (hbody : legs+rest=bodyEdges+1) (hedge : legs*2+bodyEdges=count) (hvertex : legs*3+rest=count+1)
    (scale shear : Vector ℤ legs) (input : Vector ℤ count) : IntegerLoadRun count :=
  let edges := physicalEdgeNumberingProgram legs bodyEdges count hedge
  let body := pathForwardProgram bodyEdges (Vector.ofFn (fun index => input.get (edges (.inr index))))
  let roots := (blockNumbering legs rest).trans (finCongr hbody)
  let legValues := Vector.ofFn (fun leg : Fin legs =>
    (scale.get leg*input.get (edges (.inl (leg,0)))+shear.get leg*input.get (edges (.inl (leg,1))),
      input.get (edges (.inl (leg,1)))))
  let vertices := physicalVertexNumberingProgram legs rest count hvertex
  let output := Vector.ofFn (fun vertex : Fin (count+1) =>
    match vertices.symm vertex with
    | ⟨.inl leg,slot⟩ => ![(legValues.get leg).1,-(legValues.get leg).1-(legValues.get leg).2,
        body.value.get (roots (.inl leg))+(legValues.get leg).2] slot
    | ⟨.inr index,slot⟩ => ![body.value.get (roots (.inr index))] slot)
  ⟨output,body.work+20*(count+1)+20*(legs+1)⟩

 theorem physicalEdgeLoadProgram_work (legs rest bodyEdges count : ℕ)
    (hbody : legs+rest=bodyEdges+1) (hedge : legs*2+bodyEdges=count) (hvertex : legs*3+rest=count+1)
    (scale shear : Vector ℤ legs) (input : Vector ℤ count) :
    (physicalEdgeLoadProgram legs rest bodyEdges count hbody hedge hvertex scale shear input).work≤
      60*(count+1)^2 := by
  have hh := pathForwardProgram_work bodyEdges (Vector.ofFn (fun index =>
    input.get (physicalEdgeNumberingProgram legs bodyEdges count hedge (.inr index))))
  have hb : bodyEdges≤count := by omega
  have hl : legs≤count := by omega
  have hsq : (bodyEdges+1)^2≤(count+1)^2 := Nat.pow_le_pow_left (by omega) 2
  simp only [physicalEdgeLoadProgram]
  nlinarith

/-- The initial offset uses the chart shift, complementary baseline and body centers. -/
def physicalInitialLoadProgram (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
    (modulus : ℤ) (shift baseline : Vector ℤ legs) (center : Vector ℤ (legs+rest)) :
    IntegerLoadRun count :=
  let vertices := physicalVertexNumberingProgram legs rest count hvertex
  let roots := blockNumbering legs rest
  ⟨Vector.ofFn (fun vertex : Fin (count+1) => match vertices.symm vertex with
    | ⟨.inl leg,slot⟩ => ![shift.get leg,modulus-1+baseline.get leg-shift.get leg,
        center.get (roots (.inl leg))] slot
    | ⟨.inr index,slot⟩ => ![center.get (roots (.inr index))] slot),10*(count+1)+10*(legs+1)⟩

/-- A shared queue is inserted only in the body coordinate of its selected block. -/
def physicalQueueLoadProgram (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
    (mask : Vector ℤ (legs+rest)) : IntegerLoadRun count :=
  let vertices := physicalVertexNumberingProgram legs rest count hvertex
  let roots := blockNumbering legs rest
  ⟨Vector.ofFn (fun vertex : Fin (count+1) => match vertices.symm vertex with
    | ⟨.inl leg,slot⟩ => ![0,0,mask.get (roots (.inl leg))] slot
    | ⟨.inr index,slot⟩ => ![mask.get (roots (.inr index))] slot),10*(count+1)⟩

namespace V7Calibration
open GaussianSource BoundaryCalibration
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem physicalVertexNumberingProgram_actual_leg (n : ℕ)
    (hvertex : Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1)
    (leg : Fin (Parameters.legs n)) (slot : Fin 3) :
    physicalVertexNumberingProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)
      (Parameters.dimension n-1) hvertex ⟨.inl leg,slot⟩=physicalVertexEquiv n ⟨.inl leg,slot⟩ := rfl

 theorem physicalVertexNumberingProgram_actual_body (n : ℕ)
    (hvertex : Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1)
    (body : Fin (Parameters.bodies n-Parameters.legs n)) (slot : Fin 1) :
    physicalVertexNumberingProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)
      (Parameters.dimension n-1) hvertex ⟨.inr body,slot⟩=physicalVertexEquiv n ⟨.inr body,slot⟩ := rfl

 theorem physicalEdgeLoadProgram_actual (n : ℕ)
    (hbody : Parameters.legs n+(Parameters.bodies n-Parameters.legs n)=Parameters.bodies n-1+1)
    (hedge : Parameters.legs n*2+(Parameters.bodies n-1)=Parameters.dimension n-1)
    (hvertex : Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (input : Vector ℤ (Parameters.dimension n-1)) :
    (physicalEdgeLoadProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)
      (Parameters.bodies n-1) (Parameters.dimension n-1) hbody hedge hvertex
      (Vector.ofFn (fun leg => ((chart leg).2.1.val : ℤ)))
      (Vector.ofFn (fun leg => ((chart leg).2.2.val : ℤ))) input).value.get=
        (actualPhysicalIncidenceBasis n (actualPhysicalEdgeLinear n chart input.get)).val := by
  funext vertex
  obtain ⟨⟨index,slot⟩,rfl⟩ := (physicalVertexEquiv n).surjective vertex
  rw [actualPhysicalIncidenceBasis_apply,actualPhysicalEdgeLinear_coordinates]
  cases index with
  | inl leg =>
    change Fin 3 at slot
    have hv := physicalVertexNumberingProgram_actual_leg n hvertex leg slot
    simp only [physicalEdgeLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot <;>
      simp [physicalBlockIncidence,actualChartLegLinear,legTriangularLinear,physicalEdgeCoordinates,
        physicalEdgePairEquiv,physicalEdgeNumberingProgram,physicalEdgeIndexEquiv,actualBodyRootBasis,
        coordinateZeroSumCongr,pathForwardProgram_value,actualRootIndex,blockIndexNumbering,
        physicalEdgePairEquiv,LinearEquiv.sumArrowLequivProdArrow,LinearEquiv.funCongrLeft,
        Equiv.sumArrowEquivProdArrow,vectorGet_ofFn] <;> rfl
  | inr body =>
    change Fin 1 at slot
    have hv := physicalVertexNumberingProgram_actual_body n hvertex body slot
    simp only [physicalEdgeLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot
    simp [physicalBlockIncidence,physicalEdgeCoordinates,physicalEdgePairEquiv,physicalEdgeNumberingProgram,
      physicalEdgeIndexEquiv,actualBodyRootBasis,coordinateZeroSumCongr,pathForwardProgram_value,
      actualRootIndex,blockIndexNumbering,LinearEquiv.sumArrowLequivProdArrow,LinearEquiv.funCongrLeft,
      Equiv.sumArrowEquivProdArrow,vectorGet_ofFn] <;> rfl

 theorem physicalInitialLoadProgram_actual (C : ℝ) (n : ℕ)
    (hvertex : Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n)) :
    (physicalInitialLoadProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)
      (Parameters.dimension n-1) hvertex (Parameters.modulus n)
      (Vector.ofFn (fun leg => ((chart leg).1.val : ℤ))) (Vector.ofFn baseline)
      (Vector.ofFn (fun index => ((center ((blockNumbering (Parameters.legs n)
        (Parameters.bodies n-Parameters.legs n)).symm index)).val : ℤ)))).value.get=
      actualPhysicalInitialLoad C n chart baseline center := by
  funext vertex
  obtain ⟨⟨index,slot⟩,rfl⟩ := (physicalVertexEquiv n).surjective vertex
  dsimp only [actualPhysicalInitialLoad]
  rw [(physicalVertexEquiv n).symm_apply_apply ⟨index,slot⟩]
  cases index with
  | inl leg =>
    change Fin 3 at slot
    have hv := physicalVertexNumberingProgram_actual_leg n hvertex leg slot
    simp only [physicalInitialLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot <;> simp [actualIntegerBlockLoad,chartIntegerLoad,windowZero]
  | inr body =>
    change Fin 1 at slot
    have hv := physicalVertexNumberingProgram_actual_body n hvertex body slot
    simp only [physicalInitialLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot
    simp [actualIntegerBlockLoad]

 theorem physicalQueueLoadProgram_actual (n : ℕ)
    (hvertex : Parameters.legs n*3+(Parameters.bodies n-Parameters.legs n)=Parameters.dimension n-1+1)
    (placement : Equiv.Perm (blockIndex n)) :
    (physicalQueueLoadProgram (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)
      (Parameters.dimension n-1) hvertex
      (Vector.ofFn (fun index => actualQueueMask n placement
        ((blockNumbering (Parameters.legs n) (Parameters.bodies n-Parameters.legs n)).symm index)))).value.get=
      actualPhysicalInjection n placement := by
  funext vertex
  obtain ⟨⟨index,slot⟩,rfl⟩ := (physicalVertexEquiv n).surjective vertex
  dsimp only [actualPhysicalInjection]
  rw [(physicalVertexEquiv n).symm_apply_apply ⟨index,slot⟩]
  cases index with
  | inl leg =>
    change Fin 3 at slot
    have hv := physicalVertexNumberingProgram_actual_leg n hvertex leg slot
    simp only [physicalQueueLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot <;> simp [physicalBlockIncidence]
  | inr body =>
    change Fin 1 at slot
    have hv := physicalVertexNumberingProgram_actual_body n hvertex body slot
    simp only [physicalQueueLoadProgram,Vector.get_ofFn,← hv,Equiv.symm_apply_apply]
    fin_cases slot
    simp [physicalBlockIncidence]

end
end V7Calibration
end AFT

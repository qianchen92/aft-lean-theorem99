import AFT.PhysicalAffineMatrix

/-! # Actual queue injection and initial load in the fixed rounding coordinates -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] actualModulusNeZero

def actualQueueMask (n : ℕ) (placement : Equiv.Perm (blockIndex n)) : blockIndex n → ℤ :=
  fun index => if placement index ∈ actualQueueSelection n then 1 else 0

def actualPhysicalInjection (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :
    Fin (Parameters.dimension n-1+1) → ℤ :=
  fun vertex => physicalBlockIncidence n (fun _ => (0,0)) (actualQueueMask n placement)
    ((physicalVertexEquiv n).symm vertex).1 ((physicalVertexEquiv n).symm vertex).2

theorem actualPhysicalInjection_charge (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :
    totalCharge (actualPhysicalInjection n placement)=(Parameters.modulus n : ℤ) := by
  unfold totalCharge actualPhysicalInjection
  rw [Equiv.sum_comp (physicalVertexEquiv n).symm
    (fun coordinate : Sigma (blockSlots n) => physicalBlockIncidence n (fun _ => (0,0))
      (actualQueueMask n placement) coordinate.1 coordinate.2),physicalBlockIncidence_sum]
  unfold actualQueueMask
  rw [Equiv.sum_comp placement (fun index => if index ∈ actualQueueSelection n then (1 : ℤ) else 0)]
  simp [actualQueueSelection_card]

theorem actualQueueShifts_mask (n : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) (index : blockIndex n) :
    actualQueueShifts n sample index=(sample.1 : ℤ)*actualQueueMask n sample.2 index := by
  simp only [actualQueueShifts,FiniteDist.sharedQueueShift,actualQueueMask]
  split_ifs <;> ring

theorem actualPhysicalQueue_injection (n : ℕ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) (coordinate : Sigma (blockSlots n)) :
    physicalBlockIncidence n (fun _ => (0,0)) (actualQueueShifts n sample) coordinate.1 coordinate.2=
      (sample.1 : ℤ)*actualPhysicalInjection n sample.2 (physicalVertexEquiv n coordinate) := by
  dsimp only [actualPhysicalInjection]
  rw [(physicalVertexEquiv n).symm_apply_apply coordinate]
  rcases coordinate with ⟨index,slot⟩
  cases index with
  | inl leg =>
    change Fin 3 at slot
    fin_cases slot <;> simp [physicalBlockIncidence,actualQueueShifts_mask]
  | inr body =>
    change Fin 1 at slot
    fin_cases slot
    simp [physicalBlockIncidence,actualQueueShifts_mask]

theorem modulus_le_actualDimension (n : ℕ) : Parameters.modulus n ≤ Parameters.dimension n-1+1 := by
  have hq := modulus_le_bodies n
  have hb := Parameters.bodies_positive n
  have hd := Parameters.population_identity n
  omega

def actualPhysicalCorrection (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :
    Fin (Parameters.dimension n-1) → ℤ :=
  (pathBasis _).symm ⟨actualPhysicalInjection n placement-injectionColumn _ (Parameters.modulus n),by
    rw [mem_zeroSumLattice,totalCharge_sub,actualPhysicalInjection_charge,
      totalCharge_injectionColumn _ _ (modulus_le_actualDimension n),sub_self]⟩

theorem actualPhysicalCorrection_load (n : ℕ) (placement : Equiv.Perm (blockIndex n)) :
    pathLoad _ (actualPhysicalCorrection n placement)=
      actualPhysicalInjection n placement-injectionColumn _ (Parameters.modulus n) := by
  exact congrArg Subtype.val ((pathBasis _).apply_symm_apply _)

def actualPhysicalTransport (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (placement : Equiv.Perm (blockIndex n)) :
    ((Fin (Parameters.dimension n-1) → ℤ) × ℤ) →ₗ[ℤ] ((Fin (Parameters.dimension n-1) → ℤ) × ℤ) :=
  blockTransport _ (edgeBasisChange _ (actualPhysicalIncidenceBasis n))
    (actualPhysicalEdgeLinear n chart) (actualPhysicalCorrection n placement)

def actualPhysicalInitialLoad (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n)) :
    Fin (Parameters.dimension n-1+1) → ℤ :=
  fun vertex => actualIntegerBlockLoad C n chart baseline center (fun _ => 0) (fun _ => 0)
    (fun _ => (windowZero _,windowZero _))
    ((physicalVertexEquiv n).symm vertex).1 ((physicalVertexEquiv n).symm vertex).2

theorem actualPhysicalInitialLoad_charge (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ)) :
    (Parameters.modulus n : ℤ) ∣ totalCharge (actualPhysicalInitialLoad C n chart baseline center) := by
  unfold totalCharge actualPhysicalInitialLoad
  rw [Equiv.sum_comp (physicalVertexEquiv n).symm
    (fun coordinate : Sigma (blockSlots n) => actualIntegerBlockLoad C n chart baseline center
      (fun _ => 0) (fun _ => 0) (fun _ => (windowZero _,windowZero _)) coordinate.1 coordinate.2),
    actualIntegerBlockLoad_sum]
  simp only [Finset.sum_const_zero,add_zero]
  obtain ⟨multiple,hmultiple⟩ := hcharge
  refine ⟨(Parameters.legs n : ℤ)+multiple,?_⟩
  nlinarith

/-- The precise scalar extension of the actual incidence construction. -/
theorem actualPhysicalTransport_load (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (placement : Equiv.Perm (blockIndex n))
    (input : (Fin (Parameters.dimension n-1) → ℤ) × ℤ) :
    roundingLoad _ (injectionColumn _ (Parameters.modulus n)) (actualPhysicalTransport n chart placement input)=
      (actualPhysicalIncidenceBasis n (actualPhysicalEdgeLinear n chart input.1)).val+
        input.2 • actualPhysicalInjection n placement :=
  tree_transport_identity _ _ _ _ _ _ (actualPhysicalCorrection_load n placement) input

theorem actualPhysicalEdgeLinear_coordinates (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (input : Fin (Parameters.dimension n-1) → ℤ) :
    physicalEdgeCoordinates n (actualPhysicalEdgeLinear n chart input)=
      (actualChartLegLinear n chart (physicalEdgeCoordinates n input).1,(physicalEdgeCoordinates n input).2) := by
  exact (physicalEdgeCoordinates n).apply_symm_apply _

/-- The abstract transport loads are exactly the protected physical loads,
with the same chart, integer roots, shared queue and initial charge vector. -/
theorem actualPhysicalTransport_protected (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (roots : coordinateZeroSum (blockIndex n) ℤ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (input : Fin (Parameters.legs n) → V7Input C n)
    (coordinate : Sigma (blockSlots n)) :
    let edge := (physicalEdgeCoordinates n).symm
      ((fun leg => (((input leg).1 : ℤ),((input leg).2 : ℤ))),(actualBodyRootBasis n).symm roots)
    roundingLoad _ (injectionColumn _ (Parameters.modulus n))
      (actualPhysicalTransport n chart sample.2 (edge,(sample.1 : ℤ))) (physicalVertexEquiv n coordinate)+
      actualPhysicalInitialLoad C n chart baseline center (physicalVertexEquiv n coordinate)=
      actualIntegerBlockLoad C n chart baseline center roots.val (actualQueueShifts n sample) input coordinate.1 coordinate.2 := by
  dsimp only
  rw [actualPhysicalTransport_load]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [actualPhysicalIncidenceBasis_apply,actualPhysicalEdgeLinear_coordinates,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rw [← actualPhysicalQueue_injection,actualIntegerBlockLoad_affine]
  dsimp only [actualPhysicalInitialLoad]
  rw [(physicalVertexEquiv n).symm_apply_apply coordinate]

end
end AFT.V7Calibration

import CurrentAFT.CurrentAffineLoad
import AFT.BinaryAffineAssembly

/-! Identifying executable path-coordinate inversion with the current affine
data. The identification uses injectivity of the fixed rounding matrix. The
noncomputable extension-correction witness is never an executed input. -/
namespace CurrentAFT.CurrentAffineEmissionBridge
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean CurrentAffineGeometry CurrentAffineLoad
  LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount


def linearLoad (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) : Fin (Parameters.dimension security) → ℤ :=
  fun vertex =>
    ((relabeledBasis (bodyEdges security) (Parameters.legCount security)
      (placement security core) (attachments security layout) (relabeling security layout core)
      ((numberedMatrix (bodyEdges security) (Parameters.legCount security) scale shear).mulVec
        (splitSource security input).1)).val +
      (splitSource security input).2 • AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core))
          ((dimensionEquiv security).symm vertex)

 theorem linear_rounding (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    rounding security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      linearLoad security layout core scale shear input := by
  unfold rounding
  rw [matrix_split, AffineRealization.linearPart_load]
  rfl

 theorem offset_rounding (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closure : ℤ)
    (hcharge : publicCharge security core) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept closure hcharge) =
      load security layout core scale shear intercept closure 0 := by
  simpa only [Matrix.mulVec_zero, zero_add] using affine_rounding security layout core scale shear intercept closure hcharge 0

 theorem matrix_column_rounding (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (column : Fin (Parameters.dimension security)) :
    rounding security (fun row => CurrentAffineGeometry.matrix security layout core scale shear row column) =
      linearLoad security layout core scale shear (Pi.single column 1) := by
  have h := linear_rounding security layout core scale shear (Pi.single column 1)
  have he : (CurrentAffineGeometry.matrix security layout core scale shear).mulVec (Pi.single column 1) =
      fun row => CurrentAffineGeometry.matrix security layout core scale shear row column := by
    funext row
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rwa [he] at h

 theorem injection_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    totalCharge (injectionColumn (edgeCount security) (Parameters.modulus security)) = (Parameters.modulus security : ℤ) := by
  exact totalCharge_injectionColumn _ _ (AffineRealization.queue_modulus_le
    (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security) (queues security layout))

 theorem rounding_injective (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Function.Injective (rounding security) := by
  intro first second hequal
  have hload : roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security)) (splitSource security first) =
      roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security)) (splitSource security second) := by
    funext vertex
    have h := congrFun hequal (dimensionEquiv security vertex)
    simpa only [rounding, Equiv.symm_apply_apply] using h
  have hq : (Parameters.modulus security : ℤ) ≠ 0 := by exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
  have hs := roundingLoad_injective (edgeCount security) (Parameters.modulus security) hq
    (injectionColumn _ (Parameters.modulus security)) (injection_charge security layout) hload
  calc
    first = packSource security (splitSource security first) := (pack_split security first).symm
    _ = packSource security (splitSource security second) := congrArg (packSource security) hs
    _ = second := pack_split security second

/-- Any executed bit load with the specified current integral R-load has
exactly the specified coordinates. Only the actual bit inverse is run. -/
 theorem binary_inverse_eq (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (modulus : List Bool) (hmodulus : AFT.BinaryArithmetic.value modulus = Parameters.modulus security)
    (injection bitLoad : Vector IntegerBits (edgeCount security + 1))
    (hinjection : ∀ vertex, (injection.get vertex).decode = injectionColumn _ (Parameters.modulus security) vertex)
    (target : Fin (Parameters.dimension security) → ℤ)
    (hload : ∀ vertex, (bitLoad.get vertex).decode = rounding security target (dimensionEquiv security vertex)) :
    packSource security
      ((fun edge => ((binaryRoundingInverse (edgeCount security) modulus injection bitLoad).edges.get edge).decode),
        (binaryRoundingInverse (edgeCount security) modulus injection bitLoad).charge.decode) = target := by
  let decodedInjection := injection.map IntegerBits.decode
  let decodedLoad := bitLoad.map IntegerBits.decode
  have hi : decodedInjection.get = injectionColumn (edgeCount security) (Parameters.modulus security) := by
    funext vertex
    simpa only [decodedInjection, Vector.get_map] using hinjection vertex
  have hm : totalCharge decodedInjection.get = (Parameters.modulus security : ℤ) := by
    rw [hi]
    exact injection_charge security layout
  have hl : decodedLoad.get = roundingLoad (edgeCount security) decodedInjection.get (splitSource security target) := by
    funext vertex
    rw [hi]
    simpa only [decodedLoad, Vector.get_map, rounding, Equiv.symm_apply_apply] using hload vertex
  have hd : (Parameters.modulus security : ℤ) ∣ totalCharge decodedLoad.get := by
    exact (rounding_image_lattice _ _ _ hm _).mp ⟨splitSource security target, hl.symm⟩
  have hbitdiv : (AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ vertex, (bitLoad.get vertex).decode := by
    simpa only [hmodulus, decodedLoad, totalCharge, Vector.get_map] using hd
  have hb := binaryRoundingInverse_value (edgeCount security) modulus injection bitLoad
    (by rw [hmodulus]; exact (Parameters.modulus_spec security).2.pos) hbitdiv
  have hq : (Parameters.modulus security : ℤ) ≠ 0 := by exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
  have he : ((roundingInverseProgram (edgeCount security) (Parameters.modulus security) decodedInjection decodedLoad).value.1.get,
      (roundingInverseProgram (edgeCount security) (Parameters.modulus security) decodedInjection decodedLoad).value.2) =
        splitSource security target := by
    apply roundingLoad_injective (edgeCount security) (Parameters.modulus security) hq decodedInjection.get hm
    rw [roundingInverseProgram_load _ _ _ _ hm hd, hl]
  rw [hmodulus] at hb
  have hresult : ((fun edge => ((binaryRoundingInverse (edgeCount security) modulus injection bitLoad).edges.get edge).decode),
      (binaryRoundingInverse (edgeCount security) modulus injection bitLoad).charge.decode) = splitSource security target := by
    apply (Prod.ext (funext hb.2) hb.1).trans he
  rw [hresult, pack_split]

end
end CurrentAFT.CurrentAffineEmissionBridge

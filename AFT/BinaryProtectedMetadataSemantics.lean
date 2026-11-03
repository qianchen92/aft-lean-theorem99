import AFT.BinaryProtectedMetadata

/-! The generated bit masks are exactly the original protected chart sets. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration

 theorem protectedMetadata_feature (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (fun index point => (((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.feature).get index).get point)=
       finiteProtectedFeatures cutoff modulus := by
   funext index point
   rw [protectedMetadata_value,protectedMetadataCore_feature]
   rfl

 theorem protectedMetadata_allowed (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
     (((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
   rw [protectedMetadata_value,protectedMetadataCore_allowed]
   rfl

 theorem protectedMetadata_scale (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.scale).get=finiteAffineScale modulus := by
   funext point
   rw [protectedMetadata_value,protectedMetadataCore_scale]
   rfl

 theorem protectedMetadata_safe (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (point : Fin (modulus*(modulus*modulus))) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.safe).get point=true ↔
       point∈finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
         (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)) := by
   rw [protectedMetadata_value]
   simp only [protectedMetadataCore,storeData_get,safeChart_value,protectedScale_value,protectedFeature_value,
     Fin.cast_refl,id_eq,protectedPalette_value,finiteMarkedSafe,Finset.mem_filter,Finset.mem_univ,true_and]

 theorem protectedMetadata_fiber (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (point : Fin (modulus*(modulus*modulus))) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.fiber).get point=true ↔
       point∈finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
         (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline))
         (finiteProtectedMark cutoff) mark := by
   rw [protectedMetadata_value]
   simp only [protectedMetadataCore,storeData_get,fiberChart_value,protectedScale_value,protectedFeature_value,
     Fin.cast_refl,id_eq,protectedPalette_value,protectedMark_value,finiteMarkedFiber,Finset.mem_filter,Finset.mem_univ,true_and]

 theorem protectedMetadata_legal (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (point : Fin (modulus*(modulus*modulus))) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.legal).get point=
       (((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.safe).get point ||
         ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.fiber).get point) := by
   rw [protectedMetadata_value]
   simp only [protectedMetadataCore]
   exact Vector.getElem_zipWith ..

end AFT.BinaryArithmetic

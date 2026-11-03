import AFT.BinaryProtectedMetadataSemantics
import AFT.BinaryProtectedMetadataCost
import AFT.BinaryProtectedAtomCost
import AFT.BinaryMarkedChartCost

/-! The original actual protected-chart weights, evaluated solely on bits. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalNumerics RationalBits

 def protectedChartWeight (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
     ArrayResult (modulus*(modulus*modulus)) :=
   let metadata := protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark
   let marked := protectedMark cutoff
   let atom := protectedAtom cutoff
   let result := markedChartWeight metadata.value.feature metadata.value.allowed metadata.value.safe metadata.value.fiber marked.value atom.data steps
   ⟨result.data,metadata.work+marked.work+atom.work+result.work+4⟩

 theorem protectedChartWeight_value (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (steps : ℕ)
     (point : Fin (modulus*(modulus*modulus))) :
     ((protectedChartWeight cutoff modulus boundarySign baselineSign boundary baseline mark steps).data.get point).decode=
       (markedChartWeightProgram (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))
         (finiteProtectedFeatures cutoff modulus)
         (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline))
         (finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
           (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)))
         (finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
           (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline))
           (finiteProtectedMark cutoff) mark)
         (finiteProtectedMark cutoff) (finiteProtectedAtom cutoff) steps).get point := by
   let metadata := (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value
   have hfeature : (fun i => (metadata.feature.get i).get)=finiteProtectedFeatures cutoff modulus :=
     protectedMetadata_feature cutoff modulus boundarySign baselineSign boundary baseline mark
   have hallowed : (fun i => maskSet (metadata.allowed.get i))=
       finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) := by
     funext index
     ext color
     simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
     exact protectedMetadata_allowed cutoff modulus boundarySign baselineSign boundary baseline mark index color
   have hsafe : maskSet metadata.safe=finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
       (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)) := by
     ext p
     simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
     exact protectedMetadata_safe cutoff modulus boundarySign baselineSign boundary baseline mark p
   have hfiber : maskSet metadata.fiber=finiteMarkedFiber (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
       (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline))
       (finiteProtectedMark cutoff) mark := by
     ext p
     simp only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
     exact protectedMetadata_fiber cutoff modulus boundarySign baselineSign boundary baseline mark p
   simp only [protectedChartWeight,markedChartWeight_value,protectedMark_value,protectedAtom_value]
   change (markedChartWeightProgram _ _ _ (fun i => (metadata.feature.get i).get)
     (fun i => maskSet (metadata.allowed.get i)) (maskSet metadata.safe) (maskSet metadata.fiber) _ _ _).get point=_
   rw [hfeature,hallowed,hsafe,hfiber]

 def protectedChartWeightHeight (cutoff modulus steps : ℕ) : ℕ :=
   chartWeightHeight (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeight cutoff) steps

 theorem protectedChartWeight_height (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (steps : ℕ)
     (point : Fin (modulus*(modulus*modulus))) :
     HeightBound ((protectedChartWeight cutoff modulus boundarySign baselineSign boundary baseline mark steps).data.get point).decode
       (protectedChartWeightHeight cutoff modulus steps) :=
   markedChartWeight_output_height _ _ _ _ _ _ _ _ (protectedAtom_height cutoff) point

 def protectedChartWeightWork (cutoff modulus boundaryBits baselineBits steps : ℕ) : ℕ :=
   protectedMetadataWork cutoff modulus boundaryBits baselineBits+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+protectedAtomWork cutoff+
     markedChartWork (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeight cutoff) steps+4

 theorem protectedChartWeight_work (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
     (protectedChartWeight cutoff modulus boundarySign baselineSign boundary baseline mark steps).work≤
       protectedChartWeightWork cutoff modulus boundary.length baseline.length steps := by
   let metadata := (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value
   have hm := protectedMetadata_work cutoff modulus boundarySign baselineSign boundary baseline mark
   have hmark := protectedMark_work cutoff
   have ha := protectedAtom_work cutoff
   have hw := markedChartWeight_work metadata.feature metadata.allowed metadata.safe metadata.fiber
     (protectedMark cutoff).value (protectedAtom cutoff).data (protectedAtomHeight cutoff) steps (protectedAtom_height cutoff)
   simp only [protectedChartWeight,protectedChartWeightWork]
   dsimp only [metadata] at hw
   omega

end AFT.BinaryArithmetic

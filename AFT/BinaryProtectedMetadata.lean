import AFT.BinaryProtectedParameters
import AFT.BinaryProtectedPaletteCost
import AFT.BinaryChartSupports
import AFT.BinaryDataArrays

/-! Complete public chart metadata on stored bits. Dimensions are calculated
by the explicit counter program before materializing arrays; proof casts
only identify its addresses with the specification. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration

 structure BinaryPublicChartMetadata (charts colors features : ℕ) where
   feature : Vector (Vector (Fin colors) charts) features
   allowed : Vector (Vector Bool colors) features
   scale : Vector (Fin colors) charts
   safe : Vector Bool charts
   fiber : Vector Bool charts
   legal : Vector Bool charts

 def protectedMetadataCore (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     CountedValue (BinaryPublicChartMetadata charts modulus features) :=
   let feature := storeData features (fun index => storeData charts (fun point =>
     protectedFeature cutoff modulus (index.cast hfeatures) (point.cast hcharts)))
   let allowed := storeData features (fun index => storeData modulus (fun color =>
     protectedPalette cutoff modulus boundarySign baselineSign boundary baseline index.val color.val))
   let scale := storeData charts (fun point => protectedScale modulus (point.cast hcharts))
   let marked := protectedMark cutoff
   let markedIndex := marked.value.cast hfeatures.symm
   let safe := storeData charts (safeChart feature.value allowed.value scale.value)
   let fiber := storeData charts (fiberChart feature.value allowed.value scale.value markedIndex mark)
   ⟨⟨feature.value,allowed.value,scale.value,safe.value,fiber.value,safe.value.zipWith Bool.or fiber.value⟩,
     feature.work+allowed.work+scale.work+marked.work+safe.work+fiber.work+4*charts+8⟩

 theorem protectedMetadataCore_feature (cutoff modulus charts features : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin features) (point : Fin charts) :
     (((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.feature).get index).get point=
       finiteProtectedFeatures cutoff modulus (index.cast hfeatures) (point.cast hcharts) := by
   simp only [protectedMetadataCore,storeData_get,protectedFeature_value]

 theorem protectedMetadataCore_allowed (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin features) (color : Fin modulus) :
     (((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) (index.cast hfeatures) := by
   simp only [protectedMetadataCore,storeData_get]
   exact protectedPalette_value cutoff modulus boundarySign baselineSign boundary baseline (index.cast hfeatures) color

 theorem protectedMetadataCore_scale (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (point : Fin charts) :
     ((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.scale).get point=
       finiteAffineScale modulus (point.cast hcharts) := by
   simp only [protectedMetadataCore,storeData_get,protectedScale_value]

 theorem protectedMetadataCore_cast (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (h : BinaryPublicChartMetadata charts modulus features=
       BinaryPublicChartMetadata (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))) :
     cast h (protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value=
       (protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   subst charts
   subst features
   rfl

 def protectedMetadata (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     CountedValue (BinaryPublicChartMetadata (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))) :=
   let dimensions := protectedDimensions cutoff modulus
   let result := protectedMetadataCore cutoff modulus dimensions.charts dimensions.features
     (protectedDimensions_values cutoff modulus).1 (protectedDimensions_values cutoff modulus).2
     boundarySign baselineSign boundary baseline mark
   ⟨cast (by rw [(protectedDimensions_values cutoff modulus).1,(protectedDimensions_values cutoff modulus).2]) result.value,
     dimensions.work+result.work+2⟩

 theorem protectedMetadata_value (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value=
       (protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   dsimp only [protectedMetadata]
   exact protectedMetadataCore_cast cutoff modulus _ _ _ _ boundarySign baselineSign boundary baseline mark _


end AFT.BinaryArithmetic

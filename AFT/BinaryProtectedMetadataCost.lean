import AFT.BinaryProtectedMetadata

/-! Cost of all materialized public chart metadata, without field or lookup
oracles. Every bound is a polynomial in the displayed dimensions and lengths. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 theorem protectedFeatureWork_mono {c1 c2 q1 q2 i1 i2 t1 t2 : ℕ}
     (hc : c1≤ c2) (hq : q1≤ q2) (hi : i1≤ i2) (ht : t1≤ t2) :
     protectedFeatureWork c1 q1 i1 t1≤ protectedFeatureWork c2 q2 i2 t2 := by
   simp only [protectedFeatureWork,modularDifferenceWork];gcongr

 theorem protectedPaletteWork_mono {c1 c2 q1 q2 i1 i2 t1 t2 b1 b2 s1 s2 : ℕ}
     (hc : c1≤ c2) (hq : q1≤ q2) (hi : i1≤ i2) (ht : t1≤ t2) (hb : b1≤ b2) (hs : s1≤ s2) :
     protectedPaletteWork c1 q1 i1 t1 b1 s1≤ protectedPaletteWork c2 q2 i2 t2 b2 s2 := by
   unfold protectedPaletteWork;gcongr

 theorem protectedScaleWork_mono {q1 q2 t1 t2 : ℕ} (hq : q1≤ q2) (ht : t1≤ t2) :
     protectedScaleWork q1 t1≤ protectedScaleWork q2 t2 := by unfold protectedScaleWork;gcongr

 def protectedMetadataCoreWork (cutoff modulus charts features boundaryBits baselineBits : ℕ) : ℕ :=
   features*(charts*(protectedFeatureWork cutoff modulus features charts+2)+4)+2+
     features*(modulus*(protectedPaletteWork cutoff modulus features modulus boundaryBits baselineBits+2)+4)+2+
     charts*(protectedScaleWork modulus charts+2)+2+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+
     2*(charts*(supportWork charts modulus features+2)+2)+4*charts+8

 theorem protectedMetadataCore_work (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).work≤
       protectedMetadataCoreWork cutoff modulus charts features boundary.length baseline.length := by
   let feature := storeData features (fun index => storeData charts (fun point =>
     protectedFeature cutoff modulus (index.cast hfeatures) (point.cast hcharts)))
   let allowed := storeData features (fun index => storeData modulus (fun color =>
     protectedPalette cutoff modulus boundarySign baselineSign boundary baseline index.val color.val))
   let scale := storeData charts (fun point => protectedScale modulus (point.cast hcharts))
   let marked := protectedMark cutoff
   have hm : 0 < modulus := Nat.pos_of_ne_zero (NeZero.ne _)
   have hf : feature.work≤ features*(charts*(protectedFeatureWork cutoff modulus features charts+2)+4)+2 := by
     apply (storeData_work features (charts*(protectedFeatureWork cutoff modulus features charts+2)+2) _ (fun index =>
       storeData_work charts (protectedFeatureWork cutoff modulus features charts) _ (fun point => ?_))).trans_eq
     · congr 1
     · exact (protectedFeatureAddress_work cutoff modulus index.val point.val hm).trans
         (protectedFeatureWork_mono le_rfl le_rfl index.isLt.le point.isLt.le)
   have ha : allowed.work≤ features*(modulus*(protectedPaletteWork cutoff modulus features modulus boundary.length baseline.length+2)+4)+2 := by
     apply (storeData_work features (modulus*(protectedPaletteWork cutoff modulus features modulus boundary.length baseline.length+2)+2) _ (fun index =>
       storeData_work modulus (protectedPaletteWork cutoff modulus features modulus boundary.length baseline.length) _ (fun color => ?_))).trans_eq
     · congr 1
     · exact (protectedPalette_work cutoff modulus boundarySign baselineSign boundary baseline index.val color.val).trans
         (protectedPaletteWork_mono le_rfl le_rfl index.isLt.le color.isLt.le le_rfl le_rfl)
   have hs : scale.work≤ charts*(protectedScaleWork modulus charts+2)+2 :=
     storeData_work charts (protectedScaleWork modulus charts) _ (fun point =>
       (protectedScaleAddress_work modulus point.val hm).trans (protectedScaleWork_mono le_rfl point.isLt.le))
   have hsafe := storeData_work charts (supportWork charts modulus features) _
     (safeChart_work feature.value allowed.value scale.value)
   have hfiber := storeData_work charts (supportWork charts modulus features) _
     (fiberChart_work feature.value allowed.value scale.value (marked.value.cast hfeatures.symm) mark)
   have hmark := protectedMark_work cutoff
   change marked.work=_ at hmark
   change feature.work+allowed.work+scale.work+marked.work+
     (storeData charts (safeChart feature.value allowed.value scale.value)).work+
     (storeData charts (fiberChart feature.value allowed.value scale.value (marked.value.cast hfeatures.symm) mark)).work+4*charts+8≤_
   unfold protectedMetadataCoreWork
   omega

 def protectedMetadataWork (cutoff modulus boundaryBits baselineBits : ℕ) : ℕ :=
   protectedDimensionsWork cutoff modulus+
     protectedMetadataCoreWork cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) boundaryBits baselineBits+2

 theorem protectedMetadata_work (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).work≤
       protectedMetadataWork cutoff modulus boundary.length baseline.length := by
   have h := protectedMetadataCore_work cutoff modulus (protectedDimensions cutoff modulus).charts
     (protectedDimensions cutoff modulus).features (protectedDimensions_values cutoff modulus).1
     (protectedDimensions_values cutoff modulus).2 boundarySign baselineSign boundary baseline mark
   simp only [(protectedDimensions_values cutoff modulus).1,(protectedDimensions_values cutoff modulus).2] at h
   simp only [protectedMetadata,protectedDimensions_work,protectedMetadataWork]
   omega

end AFT.BinaryArithmetic

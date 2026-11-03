import AFT.BinaryChartInputs

/-! Explicit bit-operation budgets for materializing chart inputs. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def spikeWork (charts : ℕ) : ℕ :=
   3*charts+charts*(3*charts+6)+120*(charts+1)^2+2*primitiveWorkBound charts+12

 def deletionEntryWork (charts colors features : ℕ) : ℕ :=
   charts*(9*charts+10)+projectionWork charts colors features 0+primitiveWorkBound 0+5

 def deletionMatrixWork (charts colors features : ℕ) : ℕ :=
   charts*(charts*(deletionEntryWork charts colors features+2)+4)+2

 def defectWork (charts colors features atomBits : ℕ) : ℕ :=
   finiteSumWork features (chartFeatureHeight charts colors (2*charts))
     (featureWork charts colors (2*charts)+12*features+charts+colors+13)+
   primitiveWorkBound (atomBits+features*(chartFeatureHeight charts colors (2*charts)+1))+2

 theorem chartSpike_work {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) :
     (chartSpike fiber point).work ≤ spikeWork charts := by
   have ha := readVector_work false fiber point
   have hc := maskCount_work fiber
   have hcard := maskCount_le fiber
   have hn := ofCounter_work charts
   have hd := (ofCounter_work (maskCount fiber).count).trans
     (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (show (maskCount fiber).count+1 ≤ charts+1 by omega) 2))
   have hhn : HeightBound (ofCounter charts).data.decode charts := by
     rw [ofCounter_value];exact HeightBound.nat_coarse charts
   have hhd : HeightBound (ofCounter (maskCount fiber).count).data.decode charts := by
     rw [ofCounter_value];exact (HeightBound.nat_coarse _).mono hcard
   have hq := quotient_work (ofCounter charts).data (ofCounter (maskCount fiber).count).data charts hhn hhd
   simp only [chartSpike]
   split <;> dsimp only <;> unfold spikeWork <;> omega

 theorem chartDeletedBasis_work {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) :
     (chartDeletedBasis safe input point).work ≤ 9*charts+8 := by
   have hr := readVector_work false safe point
   have he := equalCounter_work point.val input.val
   have hp := point.isLt
   have hi := input.isLt
   simp only [chartDeletedBasis]
   split
   · dsimp only;omega
   · split <;> dsimp only <;> omega

 theorem chartDeletionEntry_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (chartDeletionEntry feature allowed safe output input).work ≤ deletionEntryWork charts colors features := by
   have hb := buildArray_work charts (9*charts+8) _ (chartDeletedBasis_work safe input)
   norm_num only [Nat.add_assoc] at hb
   have hh (point : Fin charts) : HeightBound ((buildArray charts (chartDeletedBasis safe input)).data.get point).decode 0 := by
     rw [buildArray_get,chartDeletedBasis_value]
     split_ifs <;> first | exact HeightBound.zero | exact HeightBound.one
   have hp := chartProjection_work feature allowed (buildArray charts (chartDeletedBasis safe input)).data 0 hh output
   have hn := negate_work (chartProjection feature allowed (buildArray charts (chartDeletedBasis safe input)).data output).data 0
   simp only [chartDeletionEntry,deletionEntryWork]
   omega

 theorem chartDeletionMatrix_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) :
     (chartDeletionMatrix feature allowed safe).work ≤ deletionMatrixWork charts colors features := by
   have hh (output : Fin charts) := buildArray_work charts (deletionEntryWork charts colors features)
     _ (chartDeletionEntry_work feature allowed safe output)
   have hs := Finset.sum_le_sum (s:=Finset.univ) (fun output _ => hh output)
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
   simp only [chartDeletionMatrix,Vector.get_ofFn,deletionMatrixWork]
   nlinarith

 theorem chartDefectTerm_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (spike : Vector RationalBits charts) (bits : ℕ)
     (hh : ∀ point,HeightBound (spike.get point).decode bits) (point : Fin charts) (index : Fin features) :
     (chartDefectTerm feature allowed marked spike point index).work ≤
       featureWork charts colors bits+12*features+charts+colors+13 := by
   have he := equalCounter_work index.val marked.val
   have hi := index.isLt
   have hm := marked.isLt
   have hf := readVector_work (Vector.replicate charts (0 : Fin colors)) feature index
   have ha := readVector_work (Vector.replicate colors false) allowed index
   have hv := chartFeature_work (readVector (Vector.replicate charts 0) feature index).value
     (readVector (Vector.replicate colors false) allowed index).value spike bits hh point
   simp only [chartDefectTerm]
   split
   · dsimp only;omega
   · simp only [chartProjectionTerm]
     omega

 theorem chartDefect_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (atom : RationalBits) (atomBits : ℕ) (ha : HeightBound atom.decode atomBits)
     (spike : Vector RationalBits charts)
     (hh : ∀ point,HeightBound (spike.get point).decode (2*charts)) (point : Fin charts) :
     (chartDefect feature allowed marked atom spike point).work ≤ defectWork charts colors features atomBits := by
   let H := chartFeatureHeight charts colors (2*charts)
   have ht (index : Fin features) : HeightBound (chartDefectTerm feature allowed marked spike point index).data.decode H := by
     rw [chartDefectTerm_value]
     split
     · exact HeightBound.zero.mono (Nat.zero_le _)
     · exact chartFeatureProgram_height charts colors (2*charts) _ _ _ hh point
   have hs := sumFin_work features H (featureWork charts colors (2*charts)+12*features+charts+colors+13)
     _ ht (chartDefectTerm_work feature allowed marked spike (2*charts) hh point)
   have hsum := sumFin_height features H _ ht
   have hm := multiply_work atom (sumFin features (chartDefectTerm feature allowed marked spike point)).data
     (atomBits+features*(H+1)) (ha.mono (by omega)) (hsum.mono (by omega))
   simp only [chartDefect,defectWork,finiteSumWork]
   dsimp only [H] at hs hm
   omega

end AFT.BinaryArithmetic.RationalBits

import AFT.BinaryMarkedChart
import AFT.BinaryChartInputsCost

/-! Polynomial binary work of the complete finite marked-chart repair. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def chartEntryBits (charts atomBits iterateBits : ℕ) : ℕ :=
   2*iterateBits+2*atomBits+3*charts+10

 def chartWeightEntryWork (charts atomBits iterateBits : ℕ) : ℕ :=
   12*charts+40+10*primitiveWorkBound (chartEntryBits charts atomBits iterateBits)+60*(charts+1)^2

 def markedChartWork (charts colors features atomBits steps : ℕ) : ℕ :=
   charts*(spikeWork charts+2)+2+deletionMatrixWork charts colors features+
     charts*(defectWork charts colors features atomBits+2)+2+
     2*(steps*iterationWorkStep charts (chartStoredHeight charts colors features atomBits) steps+2*charts+2)+
     charts*(chartWeightEntryWork charts atomBits (chartIterateHeight charts colors features atomBits steps)+2)+
     2*charts+9

 theorem chartInterior_work {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (base repair : Vector RationalBits charts) (atomBits iterateBits : ℕ)
     (ha : HeightBound atom.decode atomBits)
     (hb : ∀ point,HeightBound (base.get point).decode iterateBits)
     (hr : ∀ point,HeightBound (repair.get point).decode iterateBits) (point : Fin charts) :
     (chartInterior safe atom base repair point).work ≤
       9*charts+19+5*primitiveWorkBound (chartEntryBits charts atomBits iterateBits) := by
   let B := chartEntryBits charts atomBits iterateBits
   have hB : atomBits≤B ∧ iterateBits≤B ∧ atomBits+1+iterateBits≤B := by dsimp [B,chartEntryBits];omega
   have hsafe := readVector_work false safe point
   have hbase := readVector_work zero base point
   have hrepair := readVector_work zero repair point
   have hremaining := difference_work one atom B (by rw [one_value];exact HeightBound.one.mono (Nat.zero_le _)) (ha.mono hB.1)
   have hremainingheight : HeightBound (difference one atom).data.decode (atomBits+1) := by
     rw [difference_value,one_value,sub_eq_add_neg]
     simpa only [Nat.zero_add] using HeightBound.one.add ha.neg
   have hproduct := multiply_work (difference one atom).data (readVector zero base point).value B
     (hremainingheight.mono (by omega)) (by rw [readVector_value];exact (hb point).mono hB.2.1)
   have hproductheight : HeightBound (multiply (difference one atom).data (readVector zero base point).value).data.decode B := by
     rw [multiply_value,readVector_value]
     exact (hremainingheight.mul (hb point)).mono hB.2.2
   have hresult := difference_work (multiply (difference one atom).data (readVector zero base point).value).data
     (readVector zero repair point).value B hproductheight (by rw [readVector_value];exact (hr point).mono hB.2.1)
   simp only [chartInterior]
   split <;> dsimp only <;> dsimp only [B] at * <;> omega

 theorem chartWeightEntry_work {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (spike base repair : Vector RationalBits charts) (atomBits iterateBits : ℕ)
     (ha : HeightBound atom.decode atomBits)
     (hs : ∀ point,HeightBound (spike.get point).decode (2*charts))
     (hb : ∀ point,HeightBound (base.get point).decode iterateBits)
     (hr : ∀ point,HeightBound (repair.get point).decode iterateBits) (point : Fin charts) :
     (chartWeightEntry safe atom spike base repair point).work ≤ chartWeightEntryWork charts atomBits iterateBits := by
   let B := chartEntryBits charts atomBits iterateBits
   have hbounds : atomBits≤B ∧ 2*charts≤B ∧ atomBits+2*charts≤B ∧ charts≤B := by dsimp [B,chartEntryBits];omega
   have hi := chartInterior_work safe atom base repair atomBits iterateBits ha hb hr point
   have hsp := readVector_work zero spike point
   have hspikeheight : HeightBound (readVector zero spike point).value.decode (2*charts) := by rw [readVector_value];exact hs point
   have hm := multiply_work atom (readVector zero spike point).value B (ha.mono hbounds.1) (hspikeheight.mono hbounds.2.1)
   have hmheight : HeightBound (multiply atom (readVector zero spike point).value).data.decode (atomBits+2*charts) := by
     rw [multiply_value];exact ha.mul hspikeheight
   have hiheight : HeightBound (chartInterior safe atom base repair point).data.decode (2*iterateBits+atomBits+2) := by
     rw [chartInterior_value]
     split
     · have ht := ((HeightBound.one.add ha.neg).mul (hb point)).add (hr point).neg
       convert ht using 1 <;> first | simp only [sub_eq_add_neg] | ring
     · exact HeightBound.zero.mono (Nat.zero_le _)
   have hadd := add_work (chartInterior safe atom base repair point).data
     (multiply atom (readVector zero spike point).value).data B
     (hiheight.mono (by dsimp [B,chartEntryBits];omega)) (hmheight.mono hbounds.2.2.1)
   have hdensity : HeightBound (add (chartInterior safe atom base repair point).data
       (multiply atom (readVector zero spike point).value).data).data.decode B := by
     rw [add_value]
     exact (hiheight.add hmheight).mono (by dsimp [B,chartEntryBits];omega)
   have hden := ofCounter_work charts
   have hdenheight : HeightBound (ofCounter charts).data.decode B := by
     rw [ofCounter_value];exact (HeightBound.nat_coarse charts).mono hbounds.2.2.2
   have hq := quotient_work (add (chartInterior safe atom base repair point).data
       (multiply atom (readVector zero spike point).value).data).data (ofCounter charts).data B hdensity hdenheight
   simp only [chartWeightEntry,chartWeightEntryWork]
   dsimp only [B] at hm hadd hq
   omega

 theorem markedChartWeight_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe fiber : Vector Bool charts) (marked : Fin features) (atom : RationalBits) (bits steps : ℕ)
     (hatom : HeightBound atom.decode bits) :
     (markedChartWeight feature allowed safe fiber marked atom steps).work ≤ markedChartWork charts colors features bits steps := by
   let spike := buildArray charts (chartSpike fiber)
   let matrix := chartDeletionMatrix feature allowed safe
   let defect := buildArray charts (chartDefect feature allowed marked atom spike.data)
   let base := iteration matrix.data (Vector.replicate charts one) steps
   let repair := iteration matrix.data defect.data steps
   let S := chartStoredHeight charts colors features bits
   let I := chartIterateHeight charts colors features bits steps
   have hsheight (point : Fin charts) : HeightBound (spike.data.get point).decode (2*charts) := by
     dsimp only [spike];rw [buildArray_get,chartSpike_value]
     exact chartSpikeProgram_height charts _ point
   have hmheight (output input : Fin charts) : HeightBound ((matrix.data.get output).get input).decode S := by
     dsimp only [matrix];rw [chartDeletionMatrix_value]
     exact (chartDeletionMatrixProgram_height charts colors features _ _ _ output input).mono (by dsimp [S,chartStoredHeight];omega)
   have hdheight (point : Fin charts) : HeightBound (defect.data.get point).decode S := by
     dsimp only [defect];rw [buildArray_get,chartDefect_value]
     dsimp only [spike]
     simp only [buildArray_get,chartSpike_value]
     exact (chartSpikeDefectProgram_height charts colors features bits _ _ _ _ hatom _ point).mono (by dsimp [S,chartStoredHeight];omega)
   have hone (point : Fin charts) : HeightBound ((Vector.replicate charts one).get point).decode S := by
     simp only [Vector.get_replicate,one_value]
     exact HeightBound.one.mono (Nat.zero_le _)
   have hbheight (point : Fin charts) : HeightBound (base.data.get point).decode I := by
     dsimp only [base];rw [iteration_value]
     have h := linearIteration_height _ _ S steps hmheight hone point
     simpa only [Fintype.card_fin,S,I,chartIterateHeight] using h
   have hrheight (point : Fin charts) : HeightBound (repair.data.get point).decode I := by
     dsimp only [repair];rw [iteration_value]
     have h := linearIteration_height _ _ S steps hmheight hdheight point
     simpa only [Fintype.card_fin,S,I,chartIterateHeight] using h
   have hs := buildArray_work charts (spikeWork charts) _ (chartSpike_work fiber)
   have hm := chartDeletionMatrix_work feature allowed safe
   have hd := buildArray_work charts (defectWork charts colors features bits) _
     (chartDefect_work feature allowed marked atom bits hatom spike.data hsheight)
   have hb := iteration_work matrix.data (Vector.replicate charts one) S steps steps hmheight hone le_rfl
   have hr := iteration_work matrix.data defect.data S steps steps hmheight hdheight le_rfl
   have hw := buildArray_work charts (chartWeightEntryWork charts bits I) _
     (chartWeightEntry_work safe atom spike.data base.data repair.data bits I hatom hsheight hbheight hrheight)
   change spike.work+matrix.work+defect.work+base.work+repair.work+
     (buildArray charts (chartWeightEntry safe atom spike.data base.data repair.data)).work+2*charts+7 ≤ _
   change spike.work ≤ _ at hs
   change matrix.work ≤ _ at hm
   change defect.work ≤ _ at hd
   change base.work ≤ _ at hb
   change repair.work ≤ _ at hr
   simp only [markedChartWork]
   dsimp only [S,I] at hb hr hw
   omega

end AFT.BinaryArithmetic.RationalBits

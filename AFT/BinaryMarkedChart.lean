import AFT.BinaryChartInputs

/-! A fully materialized binary-rational marked chart computation. The two
Neumann iterates share one stored deletion matrix; no rational arithmetic
primitive or finite-set membership oracle occurs in this evaluator. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def chartInterior {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (base repair : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
   let active := readVector false safe point
   if active.value then
     let b := readVector zero base point
     let r := readVector zero repair point
     let remaining := difference one atom
     let product := multiply remaining.data b.value
     let result := difference product.data r.value
     ⟨result.data,active.work+b.work+r.work+remaining.work+product.work+result.work+6⟩
   else ⟨zero,active.work+2⟩

 theorem chartInterior_value {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (base repair : Vector RationalBits charts) (point : Fin charts) :
     (chartInterior safe atom base repair point).data.decode=
       if point∈maskSet safe then (1-atom.decode)*(base.get point).decode-(repair.get point).decode else 0 := by
   simp only [chartInterior,readVector_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   split <;> simp_all [difference_value,multiply_value,one_value]

 def chartWeightEntry {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (spike base repair : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
   let interior := chartInterior safe atom base repair point
   let sp := readVector zero spike point
   let spikeTerm := multiply atom sp.value
   let density := add interior.data spikeTerm.data
   let denominator := ofCounter charts
   let result := quotient density.data denominator.data
   ⟨result.data,interior.work+sp.work+spikeTerm.work+density.work+denominator.work+result.work+6⟩

 theorem chartWeightEntry_value {charts : ℕ} (safe : Vector Bool charts) (atom : RationalBits)
     (spike base repair : Vector RationalBits charts) (point : Fin charts) :
     (chartWeightEntry safe atom spike base repair point).data.decode=
       ((if point∈maskSet safe then (1-atom.decode)*(base.get point).decode-(repair.get point).decode else 0)+
         atom.decode*(spike.get point).decode)/(charts : ℚ) := by
   simp only [chartWeightEntry,quotient_value,add_value,multiply_value,chartInterior_value,readVector_value,ofCounter_value]

 def markedChartWeight {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe fiber : Vector Bool charts) (marked : Fin features) (atom : RationalBits) (steps : ℕ) : ArrayResult charts :=
   let spike := buildArray charts (chartSpike fiber)
   let matrix := chartDeletionMatrix feature allowed safe
   let defect := buildArray charts (chartDefect feature allowed marked atom spike.data)
   let base := iteration matrix.data (Vector.replicate charts one) steps
   let repair := iteration matrix.data defect.data steps
   let result := buildArray charts (chartWeightEntry safe atom spike.data base.data repair.data)
   ⟨result.data,spike.work+matrix.work+defect.work+base.work+repair.work+result.work+2*charts+7⟩

 theorem markedChartWeight_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe fiber : Vector Bool charts) (marked : Fin features) (atom : RationalBits) (steps : ℕ) (point : Fin charts) :
     ((markedChartWeight feature allowed safe fiber marked atom steps).data.get point).decode=
       (markedChartWeightProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) (maskSet safe) (maskSet fiber) marked atom.decode steps).get point := by
   simp only [markedChartWeight,buildArray_get,chartWeightEntry_value,chartSpike_value,
     iteration_value,chartDeletionMatrix_value,chartDefect_value,Vector.get_replicate,one_value,
     markedChartWeightProgram,markedChartDensityProgram,Vector.get_ofFn,chartNeumannProgram,
     cachedLinearIteration_get]

 theorem markedChartWeight_output_height {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe fiber : Vector Bool charts) (marked : Fin features) (atom : RationalBits) (bits steps : ℕ)
     (hatom : HeightBound atom.decode bits) (point : Fin charts) :
     HeightBound ((markedChartWeight feature allowed safe fiber marked atom steps).data.get point).decode
       (chartWeightHeight charts colors features bits steps) := by
   rw [markedChartWeight_value]
   exact markedChartWeightProgram_height charts colors features bits steps _ _ _ _ marked _ hatom point

end AFT.BinaryArithmetic.RationalBits

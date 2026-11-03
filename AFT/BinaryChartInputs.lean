import AFT.BinaryChartProjectionCost
import AFT.BinaryChartIteration

/-! Binary materialization of the protected deletion matrix and marked spike.
Masks are stored Boolean vectors; every read and cardinality scan is explicit. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def chartSpike {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) : RationalResult :=
   let active := readVector false fiber point
   if active.value then
     let cardinality := maskCount fiber
     let numerator := ofCounter charts
     let denominator := ofCounter cardinality.count
     let result := quotient numerator.data denominator.data
     ⟨result.data,active.work+cardinality.work+numerator.work+denominator.work+result.work+5⟩
   else ⟨zero,active.work+2⟩

 theorem chartSpike_value {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) :
     (chartSpike fiber point).data.decode=chartSpikeProgram charts (maskSet fiber) point := by
   simp only [chartSpike,readVector_value,chartSpikeProgram,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   split <;> simp_all [quotient_value,ofCounter_value,maskCount_value,maskSet]

 def chartDeletedBasis {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) : RationalResult :=
   let allowed := readVector false safe point
   let same := equalCounter point.val input.val
   if allowed.value then ⟨zero,allowed.work+2⟩
   else if same.value then ⟨one,allowed.work+same.work+3⟩
   else ⟨zero,allowed.work+same.work+3⟩

 theorem chartDeletedBasis_value {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) :
     (chartDeletedBasis safe input point).data.decode=
       if point∈maskSet safe then 0 else if point=input then 1 else 0 := by
   have he : (equalCounter point.val input.val).value=true ↔ point=input := by
     rw [equalCounter_value,Fin.val_inj]
   simp only [chartDeletedBasis,readVector_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases hs : safe.get point=true
   · simp [hs]
   · simp only [hs,Bool.false_eq_true,ite_false]
     by_cases hi : point=input
     · simp only [he.mpr hi,ite_true,if_pos hi,one_value]
     · have hn : (equalCounter point.val input.val).value=false := Bool.eq_false_iff.mpr (fun h => hi (he.mp h))
       simp [hn,hi]

 def chartDeletionEntry {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) : RationalResult :=
   let basis := buildArray charts (chartDeletedBasis safe input)
   let projected := chartProjection feature allowed basis.data output
   let result := negate projected.data
   ⟨result.data,basis.work+projected.work+result.work+3⟩

 theorem chartDeletionEntry_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (chartDeletionEntry feature allowed safe output input).data.decode=
       chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) (maskSet safe) output input := by
   simp only [chartDeletionEntry,negate_value,chartProjection_value,buildArray_get,chartDeletedBasis_value,
     chartDeletionMatrixProgram,chartDeletionProgram]

 structure ChartMatrixResult (charts : ℕ) where
   data : Vector (Vector RationalBits charts) charts
   work : ℕ

 def chartDeletionMatrix {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) : ChartMatrixResult charts :=
   let rows := Vector.ofFn (fun output => buildArray charts (chartDeletionEntry feature allowed safe output))
   ⟨rows.map (fun row => row.data),(∑ output,(rows.get output).work)+2*charts+2⟩

 theorem chartDeletionMatrix_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (((chartDeletionMatrix feature allowed safe).data.get output).get input).decode=
       chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) (maskSet safe) output input := by
   simp only [chartDeletionMatrix,Vector.get_map,Vector.get_ofFn,buildArray_get,chartDeletionEntry_value]

 def chartDefectTerm {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (spike : Vector RationalBits charts) (point : Fin charts) (index : Fin features) : RationalResult :=
   let same := equalCounter index.val marked.val
   if same.value then ⟨zero,same.work+2⟩
   else
     let result := chartProjectionTerm feature allowed spike point index
     ⟨result.data,same.work+result.work+2⟩

 theorem chartDefectTerm_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (spike : Vector RationalBits charts) (point : Fin charts) (index : Fin features) :
     (chartDefectTerm feature allowed marked spike point index).data.decode=
       if index=marked then 0 else chartFeatureProgram charts colors (feature.get index).get
         (maskSet (allowed.get index)) (fun i => (spike.get i).decode) point := by
   have he : (equalCounter index.val marked.val).value=true ↔ index=marked := by
     rw [equalCounter_value,Fin.val_inj]
   by_cases h : index=marked
   · simp only [chartDefectTerm,he.mpr h,ite_true,if_pos h,zero_value]
   · have hn : (equalCounter index.val marked.val).value=false := Bool.eq_false_iff.mpr (fun hh => h (he.mp hh))
     simp only [chartDefectTerm,hn,Bool.false_eq_true,ite_false,if_neg h,
       chartProjectionTerm,readVector_value,chartFeature_value]

 def chartDefect {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (atom : RationalBits) (spike : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
   let total := sumFin features (chartDefectTerm feature allowed marked spike point)
   let result := multiply atom total.data
   ⟨result.data,total.work+result.work+2⟩

 theorem chartDefect_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (atom : RationalBits) (spike : Vector RationalBits charts) (point : Fin charts) :
     (chartDefect feature allowed marked atom spike point).data.decode=
       chartSpikeDefectProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) marked atom.decode (fun i => (spike.get i).decode) point := by
   simp only [chartDefect,multiply_value,sumFin_value,chartDefectTerm_value,chartSpikeDefectProgram]

end AFT.BinaryArithmetic.RationalBits

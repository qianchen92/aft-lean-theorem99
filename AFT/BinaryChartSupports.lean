import AFT.BinaryChartMetadata
import AFT.CountedChartSupports

/-! Safe and marked-fiber masks built by real sequential array scans. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration

 def chartAllowedAt {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) : CountedValue Bool :=
   let frow := readVector (Vector.replicate charts 0) feature index
   let arow := readVector (Vector.replicate colors false) allowed index
   let color := readVector 0 frow.value point
   let result := readVector false arow.value color.value
   ⟨result.value,frow.work+arow.work+color.work+result.work+charts+colors+4⟩

 theorem chartAllowedAt_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) :
     (chartAllowedAt feature allowed point index).value=(allowed.get index).get ((feature.get index).get point) := by
   simp only [chartAllowedAt,readVector_value]

 theorem chartAllowedAt_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) :
     (chartAllowedAt feature allowed point index).work≤6*features+4*charts+4*colors+16 := by
   have hf := readVector_work (Vector.replicate charts (0 : Fin colors)) feature index
   have ha := readVector_work (Vector.replicate colors false) allowed index
   have hc := readVector_work (0 : Fin colors) (readVector (Vector.replicate charts 0) feature index).value point
   have hr := readVector_work false (readVector (Vector.replicate colors false) allowed index).value
     (readVector (0 : Fin colors) (readVector (Vector.replicate charts 0) feature index).value point).value
   simp only [chartAllowedAt]
   omega

 def safeChart {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) : CountedValue Bool :=
   let all := countedFinAll features (chartAllowedAt feature allowed point)
   let s := readVector 0 scale point
   let isZero := equalCounter s.value.val 0
   ⟨!isZero.value && all.value,all.work+s.work+isZero.work+features*features+2*features+4⟩

 theorem safeChart_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) :
     (safeChart feature allowed scale point).value=true ↔
       scale.get point≠0 ∧ ∀ index,(allowed.get index).get ((feature.get index).get point)=true := by
   simp only [safeChart,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equalCounter_value,
     readVector_value,countedFinAll_value,chartAllowedAt_value]
   have hzero : (scale.get point).val=0 ↔ scale.get point=0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
   rw [hzero]

 def chartAllowedExceptAt {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (point : Fin charts) (index : Fin features) : CountedValue Bool :=
   let same := equalCounter index.val marked.val
   let result := chartAllowedAt feature allowed point index
   ⟨same.value || result.value,same.work+result.work+2⟩

 theorem chartAllowedExceptAt_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (point : Fin charts) (index : Fin features) :
     (chartAllowedExceptAt feature allowed marked point index).value=true ↔
       index≠marked → (allowed.get index).get ((feature.get index).get point)=true := by
   simp only [chartAllowedExceptAt,Bool.or_eq_true,equalCounter_value,chartAllowedAt_value,Fin.val_inj,
     or_iff_not_imp_left]

 def fiberChart {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (marked : Fin features) (mark : Fin colors) (point : Fin charts) : CountedValue Bool :=
   let all := countedFinAll features (chartAllowedExceptAt feature allowed marked point)
   let s := readVector 0 scale point
   let isZero := equalCounter s.value.val 0
   let row := readVector (Vector.replicate charts 0) feature marked
   let color := readVector 0 row.value point
   let same := equalCounter color.value.val mark.val
   ⟨same.value && !isZero.value && all.value,
     all.work+s.work+isZero.work+row.work+color.work+same.work+features*features+2*features+charts+7⟩

 theorem fiberChart_value {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (marked : Fin features) (mark : Fin colors) (point : Fin charts) :
     (fiberChart feature allowed scale marked mark point).value=true ↔
       (feature.get marked).get point=mark ∧ scale.get point≠0 ∧
         ∀ index,index≠marked → (allowed.get index).get ((feature.get index).get point)=true := by
   simp only [fiberChart,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equalCounter_value,
     readVector_value,countedFinAll_value,chartAllowedExceptAt_value,Fin.val_inj,and_assoc]
   have hzero : (scale.get point).val=0 ↔ scale.get point=0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
   rw [hzero]

 def supportWork (charts colors features : ℕ) : ℕ :=
   features*(12*features+4*charts+4*colors+22)+features*features+5*features+7*charts+9*colors+32

 theorem safeChart_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) :
     (safeChart feature allowed scale point).work≤supportWork charts colors features := by
   have hall := countedFinAll_work features (chartAllowedAt feature allowed point)
     (6*features+4*charts+4*colors+16) (chartAllowedAt_work feature allowed point)
   have hs := readVector_work (0 : Fin colors) scale point
   have he := equalCounter_work (readVector (0 : Fin colors) scale point).value.val 0
   have hb := (readVector (0 : Fin colors) scale point).value.isLt
   simp only [safeChart,supportWork]
   nlinarith

 theorem fiberChart_work {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (marked : Fin features) (mark : Fin colors) (point : Fin charts) :
     (fiberChart feature allowed scale marked mark point).work≤supportWork charts colors features := by
   have hw (index : Fin features) : (chartAllowedExceptAt feature allowed marked point index).work≤12*features+4*charts+4*colors+20 := by
     have ht := chartAllowedAt_work feature allowed point index
     have he := equalCounter_work index.val marked.val
     have hi := index.isLt
     have hm := marked.isLt
     simp only [chartAllowedExceptAt]
     omega
   have hall := countedFinAll_work features (chartAllowedExceptAt feature allowed marked point)
     (12*features+4*charts+4*colors+20) hw
   have hs := readVector_work (0 : Fin colors) scale point
   have hz := equalCounter_work (readVector (0 : Fin colors) scale point).value.val 0
   have hsb := (readVector (0 : Fin colors) scale point).value.isLt
   have hr := readVector_work (Vector.replicate charts (0 : Fin colors)) feature marked
   have hc := readVector_work (0 : Fin colors) (readVector (Vector.replicate charts 0) feature marked).value point
   have he := equalCounter_work (readVector (0 : Fin colors) (readVector (Vector.replicate charts 0) feature marked).value point).value.val mark.val
   have hcb := (readVector (0 : Fin colors) (readVector (Vector.replicate charts 0) feature marked).value point).value.isLt
   have hmb := mark.isLt
   simp only [fiberChart,supportWork]
   nlinarith

end AFT.BinaryArithmetic

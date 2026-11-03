import AFT.BinaryChartMetadata
import AFT.ChartProgramHeight

/-! Literal Boolean-mask chart projection evaluated with binary arithmetic.
The program does not call a finite-set membership or cardinality primitive. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration
open scoped BigOperators

def difference (first second : RationalBits) : RationalResult :=
  let negative := negate second
  let result := add first negative.data
  ⟨result.data,negative.work+result.work+2⟩

theorem difference_value (first second : RationalBits) :
    (difference first second).data.decode=first.decode-second.decode := by
  simp only [difference,add_value,negate_value,sub_eq_add_neg]

def chartExpectation (charts : ℕ) (term : Fin charts → RationalResult) : RationalResult :=
  let total := sumFin charts term
  let denominator := ofCounter charts
  let result := quotient total.data denominator.data
  ⟨result.data,total.work+denominator.work+result.work+3⟩

theorem chartExpectation_value (charts : ℕ) (term : Fin charts → RationalResult) :
    (chartExpectation charts term).data.decode=chartExpectationProgram charts (fun index => (term index).data.decode) := by
  simp only [chartExpectation,quotient_value,sumFin_value,ofCounter_value,chartExpectationProgram]

def chartConditionalTerm {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts)
    (color : Fin colors) (point : Fin charts) : RationalResult :=
  let mapped := readVector 0 feature point
  let equal := equalCounter mapped.value.val color.val
  if equal.value then
    let term := readVector zero profile point
    ⟨term.value,mapped.work+equal.work+term.work+2⟩
  else ⟨zero,mapped.work+equal.work+2⟩

theorem chartConditionalTerm_value {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts)
    (color : Fin colors) (point : Fin charts) :
    (chartConditionalTerm feature profile color point).data.decode=
      if feature.get point=color then (profile.get point).decode else 0 := by
  have he : (equalCounter (readVector 0 feature point).value.val color.val).value=true ↔ feature.get point=color := by
    rw [equalCounter_value,readVector_value]
    exact Fin.val_injective.eq_iff
  by_cases hh : feature.get point=color
  · have hb := he.mpr hh
    simp only [readVector_value] at hb
    simp only [chartConditionalTerm,readVector_value,hb,ite_true,if_pos hh]
  · have hb : (equalCounter (readVector 0 feature point).value.val color.val).value=false := by
      cases hv : (equalCounter (readVector 0 feature point).value.val color.val).value
      · rfl
      · exact False.elim (hh (he.mp hv))
    simp only [chartConditionalTerm,hb,Bool.false_eq_true,ite_false,if_neg hh,zero_value]

def chartConditional {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts) (color : Fin colors) : RationalResult :=
  let average := chartExpectation charts (chartConditionalTerm feature profile color)
  let coefficient := ofCounter colors
  let result := multiply coefficient.data average.data
  ⟨result.data,average.work+coefficient.work+result.work+3⟩

theorem chartConditional_value {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts) (color : Fin colors) :
    (chartConditional feature profile color).data.decode=
      chartConditionalProgram charts colors feature.get (fun index => (profile.get index).decode) color := by
  simp only [chartConditional,multiply_value,ofCounter_value,chartExpectation_value,chartConditionalTerm_value,chartConditionalProgram]

def chartAllowedTerm {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (color : Fin colors) : RationalResult :=
  let active := readVector false allowed color
  if active.value then
    let term := chartConditional feature profile color
    ⟨term.data,active.work+term.work+2⟩
  else ⟨zero,active.work+2⟩

theorem chartAllowedTerm_value {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (color : Fin colors) :
    (chartAllowedTerm feature allowed profile color).data.decode=
      if color∈maskSet allowed then chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color else 0 := by
  simp only [chartAllowedTerm,readVector_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
  split <;> simp_all only [chartConditional_value,zero_value]

def chartFeature {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let mapped := readVector 0 feature point
  let active := readVector false allowed mapped.value
  if active.value then
    let current := chartConditional feature profile mapped.value
    let total := sumFin colors (chartAllowedTerm feature allowed profile)
    let counter := maskCount allowed
    let denominator := ofCounter counter.count
    let average := quotient total.data denominator.data
    let result := difference current.data average.data
    ⟨result.data,mapped.work+active.work+current.work+total.work+counter.work+denominator.work+average.work+result.work+6⟩
  else ⟨zero,mapped.work+active.work+2⟩

theorem chartFeature_value {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (point : Fin charts) :
    (chartFeature feature allowed profile point).data.decode=
      chartFeatureProgram charts colors feature.get (maskSet allowed) (fun index => (profile.get index).decode) point := by
  have htotal : (sumFin colors (chartAllowedTerm feature allowed profile)).data.decode=
      ∑ color∈maskSet allowed,chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color := by
    rw [sumFin_value]
    simp only [chartAllowedTerm_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.sum_filter]
  simp only [chartFeature,readVector_value,chartFeatureProgram]
  split <;> rename_i hactive
  · simp only [difference_value,chartConditional_value,quotient_value,htotal,ofCounter_value,maskCount_value]
    rw [if_pos (by simpa only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]
  · simp only [zero_value]
    rw [if_neg (by simpa only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]

def chartProjectionTerm {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) (index : Fin features) : RationalResult :=
  let row := readVector (Vector.replicate charts 0) feature index
  let mask := readVector (Vector.replicate colors false) allowed index
  let result := chartFeature row.value mask.value profile point
  ⟨result.data,row.work+mask.work+result.work+charts+colors+3⟩

def chartProjection {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let average := chartExpectation charts (fun index =>
    let term := readVector zero profile index
    ⟨term.value,term.work⟩)
  let total := sumFin features (chartProjectionTerm feature allowed profile point)
  let result := add average.data total.data
  ⟨result.data,average.work+total.work+result.work+3⟩

theorem chartProjection_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) :
    (chartProjection feature allowed profile point).data.decode=
      chartProjectionProgram charts colors features (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) (fun index => (profile.get index).decode) point := by
  simp only [chartProjection,add_value,chartExpectation_value,sumFin_value,chartProjectionTerm,
    readVector_value,chartFeature_value,chartProjectionProgram]

end AFT.BinaryArithmetic.RationalBits

import AFT.BinaryChartProjection

/-! Polynomial costs of the literal binary chart projection, including
sequential metadata reads and Boolean-mask cardinality scans. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration

def finiteSumWork (count bits termWork : ℕ) : ℕ :=
  count*(termWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2

def expectationWork (charts bits termWork : ℕ) : ℕ :=
  finiteSumWork charts bits termWork+60*(charts+1)^2+
    2*primitiveWorkBound ((charts+1)*(bits+1)+charts+1)+5

def conditionalWork (charts colors bits : ℕ) : ℕ :=
  expectationWork charts bits (6*charts+6*colors+10)+60*(colors+1)^2+
    primitiveWorkBound (chartConditionalHeight charts colors bits+1)+3

def featureWork (charts colors bits : ℕ) : ℕ :=
  let H := chartConditionalHeight charts colors bits
  conditionalWork charts colors bits+
    finiteSumWork colors H (conditionalWork charts colors bits+3*colors+5)+
    colors*(3*colors+6)+60*(colors+1)^2+3*charts+3*colors+
    2*primitiveWorkBound (colors*(H+1)+colors+1)+
    2*primitiveWorkBound (chartFeatureHeight charts colors bits)+30

def projectionWork (charts colors features bits : ℕ) : ℕ :=
  expectationWork charts bits (3*charts+3)+
    finiteSumWork features (chartFeatureHeight charts colors bits)
      (featureWork charts colors bits+6*features+charts+colors+9)+
    primitiveWorkBound (chartProjectionHeight charts colors features bits)+3

theorem difference_work (first second : RationalBits) (bits : ℕ)
    (hf : HeightBound first.decode bits) (hs : HeightBound second.decode bits) :
    (difference first second).work ≤ 2*primitiveWorkBound bits+2 := by
  have hn := negate_work second bits
  have ha := add_work first (negate second).data bits hf (by rw [negate_value];exact hs.neg)
  simp only [difference]
  omega

theorem chartExpectation_work (charts bits termWork : ℕ) (term : Fin charts → RationalResult)
    (hh : ∀ point,HeightBound (term point).data.decode bits)
    (hw : ∀ point,(term point).work ≤ termWork) :
    (chartExpectation charts term).work ≤ expectationWork charts bits termWork := by
  have hs := sumFin_work charts bits termWork term hh hw
  have hd := ofCounter_work charts
  let B := (charts+1)*(bits+1)+charts+1
  have htotal := (sumFin_height charts bits term hh).mono (show charts*(bits+1) ≤ B by dsimp [B];nlinarith)
  have hden : HeightBound (ofCounter charts).data.decode B := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse charts).mono (by dsimp [B];omega)
  have hq := quotient_work (sumFin charts term).data (ofCounter charts).data B htotal hden
  simp only [chartExpectation,expectationWork,finiteSumWork]
  dsimp only [B] at hq
  omega

theorem chartConditional_work {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts)
    (bits : ℕ) (hh : ∀ point,HeightBound (profile.get point).decode bits) (color : Fin colors) :
    (chartConditional feature profile color).work ≤ conditionalWork charts colors bits := by
  have ht (point : Fin charts) : HeightBound (chartConditionalTerm feature profile color point).data.decode bits := by
    rw [chartConditionalTerm_value]
    split
    · exact hh point
    · exact HeightBound.zero.mono (Nat.zero_le _)
  have hw (point : Fin charts) : (chartConditionalTerm feature profile color point).work ≤ 6*charts+6*colors+10 := by
    have hf := readVector_work (0 : Fin colors) feature point
    have hv := readVector_work zero profile point
    have he := equalCounter_work (readVector 0 feature point).value.val color.val
    have hbound := (readVector 0 feature point).value.isLt
    have hc := color.isLt
    simp only [chartConditionalTerm]
    split <;> dsimp only <;> omega
  have he := chartExpectation_work charts bits (6*charts+6*colors+10) _ ht hw
  have hn := ofCounter_work colors
  let B := chartConditionalHeight charts colors bits+1
  have hcoef : HeightBound (ofCounter colors).data.decode B := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse colors).mono (by dsimp [B,chartConditionalHeight];omega)
  have haverage : HeightBound (chartExpectation charts (chartConditionalTerm feature profile color)).data.decode B := by
    rw [chartExpectation_value]
    exact (chartExpectationProgram_height charts bits _ ht).mono (by dsimp [B,chartConditionalHeight];omega)
  have hm := multiply_work (ofCounter colors).data
    (chartExpectation charts (chartConditionalTerm feature profile color)).data B hcoef haverage
  simp only [chartConditional,conditionalWork]
  dsimp only [B] at hm
  omega

theorem chartFeature_work {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point,HeightBound (profile.get point).decode bits) (point : Fin charts) :
    (chartFeature feature allowed profile point).work ≤ featureWork charts colors bits := by
  let H := chartConditionalHeight charts colors bits
  have hc (color : Fin colors) : HeightBound (chartConditional feature profile color).data.decode H := by
    rw [chartConditional_value]
    exact chartConditionalProgram_height charts colors bits feature.get _ hh color
  have hcw := chartConditional_work feature profile bits hh
  have hat (color : Fin colors) : HeightBound (chartAllowedTerm feature allowed profile color).data.decode H := by
    rw [chartAllowedTerm_value]
    split
    · exact chartConditionalProgram_height charts colors bits feature.get _ hh color
    · exact HeightBound.zero.mono (Nat.zero_le _)
  have haw (color : Fin colors) : (chartAllowedTerm feature allowed profile color).work ≤ conditionalWork charts colors bits+3*colors+5 := by
    have hr := readVector_work false allowed color
    have hw := hcw color
    simp only [chartAllowedTerm]
    split <;> dsimp only <;> omega
  have hsum := sumFin_work colors H (conditionalWork charts colors bits+3*colors+5) _ hat haw
  have hsumheight := sumFin_height colors H _ hat
  have hmapped := readVector_work (0 : Fin colors) feature point
  have hactive := readVector_work false allowed (readVector 0 feature point).value
  have hcount := maskCount_work allowed
  have hcard := maskCount_le allowed
  have hden := ofCounter_work (maskCount allowed).count
  have hden' : (ofCounter (maskCount allowed).count).work ≤ 60*(colors+1)^2 :=
    hden.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  let B := colors*(H+1)+colors+1
  have hdenheight : HeightBound (ofCounter (maskCount allowed).count).data.decode B := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse _).mono (by dsimp [B];omega)
  have hq := quotient_work (sumFin colors (chartAllowedTerm feature allowed profile)).data
    (ofCounter (maskCount allowed).count).data B (hsumheight.mono (by dsimp [B];omega)) hdenheight
  have hquotient : HeightBound (quotient (sumFin colors (chartAllowedTerm feature allowed profile)).data
      (ofCounter (maskCount allowed).count).data).data.decode (chartFeatureHeight charts colors bits) := by
    rw [quotient_value]
    have hnat := HeightBound.nat_coarse (maskCount allowed).count
    rw [← ofCounter_value] at hnat
    exact (hsumheight.div hnat).mono (by dsimp [chartFeatureHeight,H];omega)
  have hdiff := difference_work (chartConditional feature profile (readVector 0 feature point).value).data
    (quotient (sumFin colors (chartAllowedTerm feature allowed profile)).data (ofCounter (maskCount allowed).count).data).data
    (chartFeatureHeight charts colors bits) ((hc _).mono (by dsimp [chartFeatureHeight,H];omega)) hquotient
  have hcurrent := hcw (readVector 0 feature point).value
  simp only [chartFeature]
  split
  · simp only [featureWork,finiteSumWork]
    dsimp only [H,B] at hsum hq
    omega
  · simp only [featureWork,finiteSumWork]
    omega

theorem chartProjection_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (bits : ℕ)
    (hh : ∀ point,HeightBound (profile.get point).decode bits) (point : Fin charts) :
    (chartProjection feature allowed profile point).work ≤ projectionWork charts colors features bits := by
  have ht (index : Fin features) : HeightBound (chartProjectionTerm feature allowed profile point index).data.decode
      (chartFeatureHeight charts colors bits) := by
    simp only [chartProjectionTerm,readVector_value,chartFeature_value]
    exact chartFeatureProgram_height charts colors bits _ _ _ hh point
  have hw (index : Fin features) : (chartProjectionTerm feature allowed profile point index).work ≤
      featureWork charts colors bits+6*features+charts+colors+9 := by
    have hf := readVector_work (Vector.replicate charts (0 : Fin colors)) feature index
    have ha := readVector_work (Vector.replicate colors false) allowed index
    have hv := chartFeature_work (readVector (Vector.replicate charts 0) feature index).value
      (readVector (Vector.replicate colors false) allowed index).value profile bits hh point
    simp only [chartProjectionTerm]
    omega
  have hs := sumFin_work features (chartFeatureHeight charts colors bits)
    (featureWork charts colors bits+6*features+charts+colors+9) _ ht hw
  have hsheight := sumFin_height features (chartFeatureHeight charts colors bits) _ ht
  have he := chartExpectation_work charts bits (3*charts+3) (fun index =>
    ⟨(readVector zero profile index).value,(readVector zero profile index).work⟩)
    (fun index => by simp only [readVector_value];exact hh index) (readVector_work zero profile)
  have heheight : HeightBound (chartExpectation charts (fun index =>
      ⟨(readVector zero profile index).value,(readVector zero profile index).work⟩)).data.decode
      (chartExpectationHeight charts bits) := by
    rw [chartExpectation_value]
    apply chartExpectationProgram_height
    intro index
    simpa only [readVector_value] using hh index
  have ha := add_work _ _ (chartProjectionHeight charts colors features bits)
    (heheight.mono (by dsimp [chartProjectionHeight];omega))
    (hsheight.mono (by dsimp [chartProjectionHeight];omega))
  simp only [chartProjection,projectionWork,finiteSumWork]
  omega

end AFT.BinaryArithmetic.RationalBits

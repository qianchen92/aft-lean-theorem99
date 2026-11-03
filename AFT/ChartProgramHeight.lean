import AFT.MarkedChartProgram

/-! # Polynomial rational operand heights in the cached chart computation -/
namespace AFT.BoundaryCalibration
open RationalNumerics
open scoped BigOperators

 def chartExpectationHeight (charts bits : ℕ) : ℕ := charts*(bits+1)+charts
 def chartConditionalHeight (charts colors bits : ℕ) : ℕ := colors+chartExpectationHeight charts bits
 def chartFeatureHeight (charts colors bits : ℕ) : ℕ :=
   chartConditionalHeight charts colors bits+colors*(chartConditionalHeight charts colors bits+1)+colors+1
 def chartProjectionHeight (charts colors features bits : ℕ) : ℕ :=
   chartExpectationHeight charts bits+features*(chartFeatureHeight charts colors bits+1)+1
 def chartStoredHeight (charts colors features atomBits : ℕ) : ℕ :=
   chartProjectionHeight charts colors features 0+atomBits+features*(chartFeatureHeight charts colors (2*charts)+1)
 def chartIterateHeight (charts colors features atomBits steps : ℕ) : ℕ :=
   steps*((3*(charts^2+charts)+1)*chartStoredHeight charts colors features atomBits+charts+1)
 def chartWeightHeight (charts colors features atomBits steps : ℕ) : ℕ :=
   2*chartIterateHeight charts colors features atomBits steps+2*atomBits+3*charts+3

 theorem chartExpectationProgram_height (charts bits : ℕ) (value : Fin charts → ℚ)
    (hvalue : ∀ point,HeightBound (value point) bits) :
    HeightBound (chartExpectationProgram charts value) (chartExpectationHeight charts bits) := by
   have hs := HeightBound.sum Finset.univ value bits (fun point _ => hvalue point)
   simpa only [chartExpectationProgram,chartExpectationHeight,Finset.card_univ,Fintype.card_fin] using hs.div (HeightBound.nat_coarse charts)

 theorem chartConditionalProgram_height (charts colors bits : ℕ) (feature : Fin charts → Fin colors)
    (value : Fin charts → ℚ) (hvalue : ∀ point,HeightBound (value point) bits) (color : Fin colors) :
    HeightBound (chartConditionalProgram charts colors feature value color) (chartConditionalHeight charts colors bits) := by
   apply (HeightBound.nat_coarse colors).mul
   apply chartExpectationProgram_height
   intro point
   split_ifs
   · exact hvalue point
   · exact HeightBound.zero.mono (Nat.zero_le _)

 theorem chartFeatureProgram_height (charts colors bits : ℕ) (feature : Fin charts → Fin colors)
    (allowed : Finset (Fin colors)) (value : Fin charts → ℚ) (hvalue : ∀ point,HeightBound (value point) bits) (point : Fin charts) :
    HeightBound (chartFeatureProgram charts colors feature allowed value point) (chartFeatureHeight charts colors bits) := by
   unfold chartFeatureProgram
   split_ifs
   · have hc := chartConditionalProgram_height charts colors bits feature value hvalue
     have hs := (HeightBound.sum allowed _ _ (fun color _ => hc color)).div (HeightBound.nat_coarse allowed.card)
     have ht := (hc (feature point)).add hs.neg
     rw [←sub_eq_add_neg] at ht
     apply ht.mono
     have hcard : allowed.card≤colors := (Finset.card_le_univ allowed).trans_eq (Fintype.card_fin _)
     unfold chartFeatureHeight
     nlinarith [Nat.mul_le_mul_right (chartConditionalHeight charts colors bits+1) hcard]
   · exact HeightBound.zero.mono (Nat.zero_le _)

 theorem chartProjectionProgram_height (charts colors features bits : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (value : Fin charts → ℚ) (hvalue : ∀ point,HeightBound (value point) bits) (point : Fin charts) :
    HeightBound (chartProjectionProgram charts colors features feature allowed value point) (chartProjectionHeight charts colors features bits) := by
   have hs := HeightBound.sum Finset.univ (fun index => chartFeatureProgram charts colors (feature index) (allowed index) value point)
     (chartFeatureHeight charts colors bits) (fun index _ => chartFeatureProgram_height charts colors bits (feature index) (allowed index) value hvalue point)
   simpa only [chartProjectionProgram,chartProjectionHeight,Finset.card_univ,Fintype.card_fin] using
     (chartExpectationProgram_height charts bits value hvalue).add hs

 theorem chartDeletionMatrixProgram_height (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (output input : Fin charts) :
    HeightBound (chartDeletionMatrixProgram charts colors features feature allowed safe output input)
      (chartProjectionHeight charts colors features 0) := by
   apply HeightBound.neg
   apply chartProjectionProgram_height
   intro point
   dsimp only
   split_ifs <;> first | exact HeightBound.zero | exact HeightBound.one

 theorem chartSpikeProgram_height (charts : ℕ) (fiber : Finset (Fin charts)) (point : Fin charts) :
    HeightBound (chartSpikeProgram charts fiber point) (2*charts) := by
   unfold chartSpikeProgram
   split_ifs
   · apply ((HeightBound.nat_coarse charts).div (HeightBound.nat_coarse fiber.card)).mono
     have hc := Finset.card_le_univ fiber
     simp only [Fintype.card_fin] at hc
     omega
   · exact HeightBound.zero.mono (Nat.zero_le _)

 theorem chartSpikeDefectProgram_height (charts colors features atomBits : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (marked : Fin features) (atom : ℚ) (hatom : HeightBound atom atomBits) (fiber : Finset (Fin charts)) (point : Fin charts) :
    HeightBound (chartSpikeDefectProgram charts colors features feature allowed marked atom (chartSpikeProgram charts fiber) point)
      (atomBits+features*(chartFeatureHeight charts colors (2*charts)+1)) := by
   have hs := HeightBound.sum Finset.univ
     (fun index => if index=marked then 0 else chartFeatureProgram charts colors (feature index) (allowed index) (chartSpikeProgram charts fiber) point)
     (chartFeatureHeight charts colors (2*charts)) (by
       intro index _
       dsimp only
       split_ifs
       · exact HeightBound.zero.mono (Nat.zero_le _)
       · exact chartFeatureProgram_height charts colors (2*charts) (feature index) (allowed index) _ (chartSpikeProgram_height charts fiber) point)
   simpa only [chartSpikeDefectProgram,Finset.card_univ,Fintype.card_fin] using hatom.mul hs

 theorem markedChartWeightProgram_height (charts colors features atomBits steps : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe fiber : Finset (Fin charts)) (marked : Fin features) (atom : ℚ) (hatom : HeightBound atom atomBits) (point : Fin charts) :
    HeightBound ((markedChartWeightProgram charts colors features feature allowed safe fiber marked atom steps).get point)
      (chartWeightHeight charts colors features atomBits steps) := by
   let bits := chartStoredHeight charts colors features atomBits
   have hm out inp : HeightBound (chartDeletionMatrixProgram charts colors features feature allowed safe out inp) bits :=
     (chartDeletionMatrixProgram_height charts colors features feature allowed safe out inp).mono (by dsimp [bits,chartStoredHeight];omega)
   have hd x : HeightBound (chartSpikeDefectProgram charts colors features feature allowed marked atom (chartSpikeProgram charts fiber) x) bits :=
     (chartSpikeDefectProgram_height charts colors features atomBits feature allowed marked atom hatom fiber x).mono (by dsimp [bits,chartStoredHeight];omega)
   have hb x : HeightBound ((chartNeumannProgram charts colors features feature allowed safe (fun _ => 1) steps).get x)
       (chartIterateHeight charts colors features atomBits steps) :=
     cachedLinearIteration_height charts bits steps _ _ hm (fun _ => HeightBound.one.mono (Nat.zero_le _)) x
   have hr x : HeightBound ((chartNeumannProgram charts colors features feature allowed safe
       (chartSpikeDefectProgram charts colors features feature allowed marked atom (chartSpikeProgram charts fiber)) steps).get x)
       (chartIterateHeight charts colors features atomBits steps) :=
     cachedLinearIteration_height charts bits steps _ _ hm hd x
   have ha : HeightBound (1-atom) (atomBits+1) := by simpa only [sub_eq_add_neg,Nat.zero_add] using HeightBound.one.add hatom.neg
   have hi : HeightBound (if point∈safe then (1-atom)*
       (chartNeumannProgram charts colors features feature allowed safe (fun _ => 1) steps).get point-
       (chartNeumannProgram charts colors features feature allowed safe
         (chartSpikeDefectProgram charts colors features feature allowed marked atom (chartSpikeProgram charts fiber)) steps).get point else 0)
       (2*chartIterateHeight charts colors features atomBits steps+atomBits+2) := by
     split_ifs
     · have hh := (ha.mul (hb point)).add (hr point).neg
       convert hh using 1 <;> first | simp only [sub_eq_add_neg] | ring
     · exact HeightBound.zero.mono (Nat.zero_le _)
   have hh := (hi.add (hatom.mul (chartSpikeProgram_height charts fiber point))).div (HeightBound.nat_coarse charts)
   convert hh using 1
   · simp only [markedChartWeightProgram,markedChartDensityProgram,Vector.get_ofFn]
   · unfold chartWeightHeight
     ring

end AFT.BoundaryCalibration

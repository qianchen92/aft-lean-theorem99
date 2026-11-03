import AFT.SignedConditioning

/-! # Conditioning finite mixtures with almost constant event probabilities -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source State Output : Type*} [Fintype Source] [Fintype State] [Fintype Output]

omit [Fintype Output] in
theorem eventMass_mix (source : FiniteDist Source) (law : Source → FiniteDist State) (event : State → Prop) :
    (source.mix law).eventMass event=∑ index,source.weight index*(law index).eventMass event := by
  unfold eventMass
  simp only [FiniteDist.mix_weight,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  split_ifs <;> simp

omit [Fintype Source] in
theorem eventMass_map (law : FiniteDist State) (map : State → Output) (event : Output → Prop) :
    (law.map map).eventMass event=law.eventMass (fun point => event (map point)) := by
  unfold eventMass
  simp only [map_weight]
  calc
    _ = ∑ output,∑ point,if map point=output then (if event output then law.weight point else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro output _
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_comm]; simp

omit [Fintype Source] in
theorem condition_map (law : FiniteDist State) (map : State → Output) (event : Output → Prop)
    (hpos : 0<law.eventMass (fun point => event (map point))) :
    (law.condition (fun point => event (map point)) hpos).map map=
      (law.map map).condition event (by rwa [eventMass_map]) := by
  ext output
  simp only [map_weight,condition,eventMass_map]
  by_cases hout : event output
  · simp only [hout,if_true,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro point _
    by_cases he : map point=output <;> simp [he,hout]
  · simp only [hout,if_false,zero_div]
    apply Finset.sum_eq_zero
    intro point _
    by_cases he : map point=output <;> simp [he,hout]

omit [Fintype Source] [Fintype Output] in
/-- Conditioning costs only the reciprocal of the target event probability.
The reference and the perturbed event are both actual finite laws. -/
theorem TVBound.condition {first second : FiniteDist State} {error lower : ℝ}
    (h : TVBound first second error) (event : State → Prop)
    (hlower : 0<lower) (hevent : lower≤second.eventMass event) (hsmall : 2*error≤lower/2) :
    ∃ hfirst : 0<first.eventMass event,
      TVBound (first.condition event hfirst) (second.condition event (hlower.trans_le hevent)) (4*error/lower) := by
  have hl1 : (∑ point,|first.weight point-second.weight point|)≤2*error := by
    have hh := (tvBound_iff_totalVariation_le first second error).mp h
    rw [totalVariation_eq_half_l1] at hh
    linarith
  obtain ⟨hp,hbound⟩ := SignedConditioning.conditional_signed_l1 first.weight second event lower (2*error) hlower hevent hl1 hsmall
  refine ⟨hp,?_⟩
  apply (tvBound_iff_totalVariation_le _ _ _).mpr
  rw [totalVariation_eq_half_l1]
  change (∑ point,|SignedConditioning.conditionalMass first.weight event point-
    SignedConditioning.conditionalMass second.weight event point|)/2≤_
  exact (div_le_div_of_nonneg_right hbound (by norm_num)).trans_eq (by ring)

omit [Fintype Output] in
/-- The posterior source law after conditioning. -/
def conditionalSource (source : FiniteDist Source) (law : Source → FiniteDist State) (event : State → Prop)
    (hpos : 0<(source.mix law).eventMass event) : FiniteDist Source where
  weight index := source.weight index*(law index).eventMass event/(source.mix law).eventMass event
  nonneg index := div_nonneg (mul_nonneg (source.nonneg index) ((law index).eventMass_nonneg event)) hpos.le
  sum_one := by rw [← Finset.sum_div,← eventMass_mix,div_self hpos.ne']

omit [Fintype Output] in
theorem condition_mix (source : FiniteDist Source) (law : Source → FiniteDist State) (event : State → Prop)
    (hpos : 0<(source.mix law).eventMass event) (hlaw : ∀ index,0<(law index).eventMass event) :
    (source.mix law).condition event hpos=
      (conditionalSource source law event hpos).mix (fun index => (law index).condition event (hlaw index)) := by
  ext point
  simp only [condition,mix_weight,conditionalSource]
  by_cases he : event point
  · simp only [he,if_true,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro index _
    have hh := (hlaw index).ne'
    field_simp
  · simp only [he,if_false,zero_div,mul_zero,Finset.sum_const_zero]

omit [Fintype Output] in
/-- Mixing already conditioned kernels differs negligibly from conditioning
the mixture when every event probability has the same relative estimate. -/
theorem mix_condition_l1 (source : FiniteDist Source) (law : Source → FiniteDist State)
    (event : State → Prop) (reference error : ℝ) (href : 0<reference) (herror : 0≤error) (hsmall : error≤1/2)
    (hflat : ∀ index,|(law index).eventMass event/reference-1|≤error) :
    ∃ hpos : 0<(source.mix law).eventMass event,∃ hlaw : ∀ index,0<(law index).eventMass event,
      (∑ point,|((source.mix (fun index => (law index).condition event (hlaw index))).weight point)-
        ((source.mix law).condition event hpos).weight point|)≤4*error := by
  have ha (index) : reference/2≤(law index).eventMass event := by
    have hh := (abs_le.mp (hflat index)).1
    have hb : 1/2≤(law index).eventMass event/reference := by linarith
    have hh' := (le_div_iff₀ href).mp hb
    linarith
  have hlaw (index) : 0<(law index).eventMass event := (by positivity : 0<reference/2).trans_le (ha index)
  have havg : reference/2≤(source.mix law).eventMass event := by
    rw [eventMass_mix]
    calc
      _ = ∑ index,source.weight index*(reference/2) := by rw [← Finset.sum_mul,source.sum_one,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (ha index) (source.nonneg index)
  have hpos : 0<(source.mix law).eventMass event := (by positivity : 0<reference/2).trans_le havg
  let scaled : Source → ℝ := fun index => source.weight index*((law index).eventMass event/reference)
  have hs : ∑ index,scaled index=(source.mix law).eventMass event/reference := by
    simp only [scaled,← mul_div_assoc,← Finset.sum_div,eventMass_mix]
  have hspos : 0<∑ index,scaled index := by rw [hs]; positivity
  have herr : (∑ index,|scaled index-source.weight index|)≤error := by
    calc
      _ = ∑ index,source.weight index*|(law index).eventMass event/reference-1| := by
        apply Finset.sum_congr rfl
        intro index _
        dsimp only [scaled]
        rw [← mul_sub_one,abs_mul,abs_of_nonneg (source.nonneg index)]
      _ ≤ ∑ index,source.weight index*error := Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hflat index) (source.nonneg index)
      _ = error := by rw [← Finset.sum_mul,source.sum_one,one_mul]
  have hpost := SignedConditioning.normalized_signed_l1 scaled source.weight source.nonneg hspos (by rw [source.sum_one]; norm_num)
  have hhalf : (1/2 : ℝ)≤∑ index,scaled index := by rw [hs]; apply (le_div_iff₀ href).mpr; linarith
  have hpostbound : (∑ index,|(conditionalSource source law event hpos).weight index-source.weight index|)≤4*error := by
    have heq (index) : scaled index/(∑ j,scaled j)=(conditionalSource source law event hpos).weight index := by
      rw [hs]
      unfold scaled conditionalSource
      field_simp
    simp only [heq,source.sum_one,div_one] at hpost
    apply hpost.trans
    calc
      _ ≤ (2*error)/(1/2) := div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left herr (by norm_num)) (by norm_num) hhalf
      _ = _ := by ring
  refine ⟨hpos,hlaw,?_⟩
  rw [condition_mix source law event hpos hlaw]
  simp only [mix_weight,← Finset.sum_sub_distrib,← sub_mul]
  apply (signed_kernel_l1_contraction (fun index => source.weight index-(conditionalSource source law event hpos).weight index)
    (fun index => (law index).condition event (hlaw index))).trans
  simpa only [abs_sub_comm] using hpostbound

end
end AFT.FiniteDist

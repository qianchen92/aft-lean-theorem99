import CurrentAFT.GaussianWindowProtection
import AFT.DependentTensorChannel

/-! # One joint comparison for all actual protected Gaussian scalars -/
namespace CurrentAFT.GaussianProductProtection
open AFT GaussianSource GaussianWindowProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def fullMass (width : ℝ) (count : ℕ) (word : Fin count → ℤ) : ℝ :=
  ∏ index, integerMass width (word index)

def protectedMass (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ) (word : Fin count → ℤ) : ℝ :=
  ∏ index, GaussianWindowProtection.protectedMass width (cutoff index) (word index)

theorem fullMass_nonneg (width : ℝ) (hwidth : 0 < width) (count : ℕ) (word : Fin count → ℤ) :
    0 ≤ fullMass width count word := Finset.prod_nonneg (fun _ _ => integerMass_nonneg width hwidth _)

theorem protectedMass_nonneg (width : ℝ) (hwidth : 0 < width) {count : ℕ}
    (cutoff : Fin count → ℕ) (word : Fin count → ℤ) : 0 ≤ protectedMass width cutoff word :=
  Finset.prod_nonneg (fun index _ => GaussianWindowProtection.protectedMass_nonneg width (cutoff index) hwidth _)

theorem fullMass_summable (width : ℝ) (hwidth : 0 < width) (count : ℕ) :
    Summable (fullMass width count) :=
  (countableFiniteProduct_summable_sum count (fun _ => integerMass width)
    (fun _ => integerMass_nonneg width hwidth) (fun _ => summable_integerMass width hwidth)).1

theorem protectedMass_summable (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    Summable (protectedMass width cutoff) :=
  (countableFiniteProduct_summable_sum count (fun index => GaussianWindowProtection.protectedMass width (cutoff index))
    (fun index => GaussianWindowProtection.protectedMass_nonneg width (cutoff index) hwidth)
    (fun index => GaussianWindowProtection.protectedMass_summable width (cutoff index) hwidth)).1

theorem fullMass_sum (width : ℝ) (hwidth : 0 < width) (count : ℕ) :
    (∑' word, fullMass width count word) = 1 := by
  unfold fullMass
  rw [(countableFiniteProduct_summable_sum count (fun _ => integerMass width)
    (fun _ => integerMass_nonneg width hwidth) (fun _ => summable_integerMass width hwidth)).2]
  simp only [integerMass_sum width hwidth, Finset.prod_const_one]

theorem protectedMass_sum (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    (∑' word, protectedMass width cutoff word) = 1 := by
  unfold protectedMass
  rw [(countableFiniteProduct_summable_sum count (fun index => GaussianWindowProtection.protectedMass width (cutoff index))
    (fun index => GaussianWindowProtection.protectedMass_nonneg width (cutoff index) hwidth)
    (fun index => GaussianWindowProtection.protectedMass_summable width (cutoff index) hwidth)).2]
  simp only [GaussianWindowProtection.protectedMass_sum width _ hwidth, Finset.prod_const_one]

/-- The entire joint Gaussian source pays the sum of its scalar clipping
probabilities. No independence of the eventual endpoint increments is used. -/
theorem joint_tv (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    (∑' word, |fullMass width count word - protectedMass width cutoff word|) / 2 ≤
      ∑ index, clippingProbability width (cutoff index + 1 : ℕ) hwidth := by
  have hproduct := countableFiniteProduct_l1_le count (fun _ => integerMass width)
    (fun index => GaussianWindowProtection.protectedMass width (cutoff index))
    (fun _ => integerMass_nonneg width hwidth)
    (fun index => GaussianWindowProtection.protectedMass_nonneg width (cutoff index) hwidth)
    (fun _ => summable_integerMass width hwidth)
    (fun index => GaussianWindowProtection.protectedMass_summable width (cutoff index) hwidth)
    (fun _ => integerMass_sum width hwidth)
    (fun index => GaussianWindowProtection.protectedMass_sum width (cutoff index) hwidth)
  apply (div_le_div_of_nonneg_right hproduct (by norm_num : (0 : ℝ) ≤ 2)).trans
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun index _ => scalar_tv width (cutoff index) hwidth)

abbrev ProtectedWord {count : ℕ} (cutoff : Fin count → ℕ) := (index : Fin count) → Window (cutoff index)

def sourceEmbedding {count : ℕ} (cutoff : Fin count → ℕ) : ProtectedWord cutoff ↪ (Fin count → ℤ) where
  toFun word index := (word index).val
  inj' := by
    intro first second hequal
    funext index
    exact Subtype.ext (congrFun hequal index)

def protectedLaw (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ) : FiniteDist (ProtectedWord cutoff) :=
  FiniteDist.dependentIndependent (fun index => windowGaussian width (cutoff index))

theorem protectedMass_on_word (width : ℝ) (hwidth : 0 < width) {count : ℕ}
    (cutoff : Fin count → ℕ) (word : ProtectedWord cutoff) :
    protectedMass width cutoff (sourceEmbedding cutoff word) = (protectedLaw width cutoff).weight word := by
  apply Finset.prod_congr rfl
  intro index _
  change GaussianWindowProtection.protectedMass width (cutoff index) (word index).val = _
  rw [GaussianWindowProtection.protectedMass_window width (cutoff index) hwidth (word index).val,
    dif_pos (word index).property]

theorem protectedMass_zero_off_image (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ)
    (word : Fin count → ℤ) (hword : word ∉ Finset.univ.image (sourceEmbedding cutoff)) :
    protectedMass width cutoff word = 0 := by
  have hsome : ∃ index, word index ∉ Finset.Icc (-(cutoff index : ℤ)) (cutoff index : ℤ) := by
    by_contra hnone
    have hinside (index : Fin count) : word index ∈ Finset.Icc (-(cutoff index : ℤ)) (cutoff index : ℤ) :=
      not_not.mp (not_exists.mp hnone index)
    apply hword
    exact Finset.mem_image.mpr ⟨(fun index => ⟨word index, hinside index⟩), Finset.mem_univ _, rfl⟩
  obtain ⟨index, hindex⟩ := hsome
  exact Finset.prod_eq_zero (Finset.mem_univ index)
    (GaussianWindowProtection.protectedMass_zero width (cutoff index) (word index) hindex)

theorem protectedMix_eq_finite {Output : Type*} [Fintype Output]
    (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ)
    (channel : (Fin count → ℤ) → FiniteDist Output) :
    FiniteDist.countableMix (protectedMass width cutoff) (protectedMass_nonneg width hwidth cutoff)
      (protectedMass_summable width hwidth cutoff) (protectedMass_sum width hwidth cutoff) channel =
        (protectedLaw width cutoff).mix (fun word => channel (sourceEmbedding cutoff word)) := by
  apply FiniteDist.ext
  intro output
  change (∑' word, protectedMass width cutoff word * (channel word).weight output) = _
  rw [tsum_eq_sum (s := Finset.univ.image (sourceEmbedding cutoff))
    (fun word hword => by rw [protectedMass_zero_off_image width cutoff word hword, zero_mul])]
  rw [Finset.sum_image (fun first _ second _ hequal => (sourceEmbedding cutoff).injective hequal)]
  apply Finset.sum_congr rfl
  intro word _
  rw [protectedMass_on_word width hwidth cutoff word]

/-- All public data can be sampled inside the same channel for the two
sources; the one joint source error is incurred once. -/
theorem joint_channel_tv {Output : Type*} [Fintype Output]
    (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ)
    (channel : (Fin count → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound
      (FiniteDist.countableMix (fullMass width count) (fullMass_nonneg width hwidth count)
        (fullMass_summable width hwidth count) (fullMass_sum width hwidth count) channel)
      ((protectedLaw width cutoff).mix (fun word => channel (sourceEmbedding cutoff word)))
      (∑ index, clippingProbability width (cutoff index + 1 : ℕ) hwidth) := by
  rw [← protectedMix_eq_finite width hwidth cutoff channel]
  exact FiniteDist.countableMix_tvBound _ _ (fullMass_nonneg width hwidth count)
    (protectedMass_nonneg width hwidth cutoff) (fullMass_summable width hwidth count)
    (protectedMass_summable width hwidth cutoff) (fullMass_sum width hwidth count)
    (protectedMass_sum width hwidth cutoff) channel _ (joint_tv width hwidth cutoff)

end
end CurrentAFT.GaussianProductProtection

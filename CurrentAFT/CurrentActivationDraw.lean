import CurrentAFT.CurrentReferenceDraw
import CurrentAFT.ActualPublicLegSeed

/-! The auxiliary public activation bit is sampled from the executed cached
Gaussian zero mass; its two rational entries are an exact probability vector. -/
namespace CurrentAFT.CurrentActivationDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000

def table (security tableBits : ℕ) (cache : Cache security tableBits) : CountedValue (ProbabilityArray 2) :=
  let negative := negate cache.activation
  let difference := add one negative.data
  let data := Vector.ofFn (fun index : Fin 2 => if index = 0 then difference.data else cache.activation)
  have hb : 0 ≤ cache.activation.decode ∧ cache.activation.decode ≤ 1 := by
    rw [cache.activation_value]
    have h := LocalPairProgram.activationApprox_bounds security tableBits
    constructor
    · exact_mod_cast h.1
    · apply (Rat.cast_le (K := ℝ)).mp
      exact h.2.trans (by norm_num)
  have he (index : Fin 2) : (data.get index).decode =
      if index = 0 then 1 - cache.activation.decode else cache.activation.decode := by
    simp only [data, Vector.get_ofFn]
    split_ifs <;> simp only [difference, negative, RationalBits.add_value, one_value, negate_value, sub_eq_add_neg]
  ⟨⟨data, by intro index; rw [he]; split_ifs <;> linarith, by
      simp [he, Fin.sum_univ_two]⟩,
    negative.work + difference.work + 4⟩

def draw (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + 2 + 1) → Fin 2) : CountedValue Bool :=
  let probabilities := table security tableBits cache
  let selected := positiveDraw 2 (by decide) probabilities.value drawBits word
  ⟨finTwoEquiv selected.value, probabilities.work + selected.work + 2⟩


theorem table_get (security tableBits : ℕ) (cache : Cache security tableBits) (index : Fin 2) :
    ((table security tableBits cache).value.data.get index).decode =
      if index = 0 then 1 - cache.activation.decode else cache.activation.decode := by
  simp only [table, Vector.get_ofFn]
  split_ifs <;> simp only [RationalBits.add_value, one_value, negate_value, sub_eq_add_neg]

theorem table_height (security tableBits height : ℕ) (cache : Cache security tableBits)
    (hh : AFT.RationalNumerics.HeightBound cache.activation.decode height) (index : Fin 2) :
    AFT.RationalNumerics.HeightBound ((table security tableBits cache).value.data.get index).decode (height + 1) := by
  rw [table_get]
  split_ifs
  · simpa only [zero_add, sub_eq_add_neg] using AFT.RationalNumerics.HeightBound.one.add hh.neg
  · exact hh.mono (by omega)

theorem table_work (security tableBits height : ℕ) (cache : Cache security tableBits)
    (hh : AFT.RationalNumerics.HeightBound cache.activation.decode height) :
    (table security tableBits cache).work ≤ 2 * primitiveWorkBound height + 4 := by
  have hn := negate_work cache.activation height
  have ha := RationalBits.add_work one (negate cache.activation).data height
    (by simpa only [one_value] using AFT.RationalNumerics.HeightBound.one.mono (Nat.zero_le height))
    (by rw [negate_value]; exact hh.neg)
  change (negate cache.activation).work + (RationalBits.add one (negate cache.activation).data).work + 4 ≤ _
  omega

def workBound (height bits : ℕ) : ℕ :=
  2 * primitiveWorkBound height + CurrentProbabilityArrayDraw.workBound 2 (height + 1) bits + 6

theorem draw_work (security tableBits drawBits height : ℕ) (cache : Cache security tableBits)
    (hh : AFT.RationalNumerics.HeightBound cache.activation.decode height)
    (word : Fin (drawBits + 2 + 1) → Fin 2) :
    (draw security tableBits drawBits cache word).work ≤ workBound height drawBits := by
  have ht := table_work security tableBits height cache hh
  have hs := positiveDraw_work 2 (by decide) (table security tableBits cache).value (height + 1) drawBits
    (table_height security tableBits height cache hh) word
  change (table security tableBits cache).work + (positiveDraw 2 _ _ _ word).work + 2 ≤ _
  unfold workBound
  omega

noncomputable section
open scoped Classical

def approximateLaw (security tableBits : ℕ) : FiniteDist Bool where
  weight flag := if flag then (LocalPairProgram.activationApprox security tableBits : ℝ)
    else 1 - LocalPairProgram.activationApprox security tableBits
  nonneg flag := by
    have h := LocalPairProgram.activationApprox_bounds security tableBits
    cases flag <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith
  sum_one := by simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]; ring

theorem table_law (security tableBits : ℕ) (cache : Cache security tableBits) :
    (law (table security tableBits cache).value).map finTwoEquiv = approximateLaw security tableBits := by
  ext flag
  rw [FiniteDist.map_equiv_weight]
  cases flag <;>
    norm_num [law, table, Vector.get_ofFn, finTwoEquiv, RationalBits.add_value, negate_value, one_value,
      cache.activation_value, approximateLaw, sub_eq_add_neg]

def drawLaw (security tableBits drawBits : ℕ) (cache : Cache security tableBits) : FiniteDist Bool :=
  (FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2)).map
    (fun word => (draw security tableBits drawBits cache word).value)

theorem rounding_l1 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ flag, |(drawLaw security tableBits drawBits cache).weight flag -
      (approximateLaw security tableBits).weight flag|) ≤ 1 / (2 : ℝ)^drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2)).map
      (fun word => (positiveDraw 2 (by decide) (table security tableBits cache).value drawBits word).value))
    (law (table security tableBits cache).value) finTwoEquiv
  rw [table_law] at h
  simp only [FiniteDist.map_map] at h
  exact h.trans (positiveDraw_l1 2 (by decide) (table security tableBits cache).value drawBits)

theorem approximate_l1 (security tableBits : ℕ) :
    (∑ flag, |(approximateLaw security tableBits).weight flag -
      (ActualPublicLegCharge.activationLaw security).weight flag|) ≤ 1 / (2 : ℝ)^tableBits := by
  have h := LocalPairProgram.activationApprox_error security tableBits
  simp only [Fintype.sum_bool, approximateLaw, ActualPublicLegCharge.activationLaw,
    Bool.false_eq_true, if_false, if_true]
  have he : |(1 - (LocalPairProgram.activationApprox security tableBits : ℝ)) -
      (1 - DiffuseProfiles.activation security)| =
      |(LocalPairProgram.activationApprox security tableBits : ℝ) - DiffuseProfiles.activation security| := by
    rw [show (1 - (LocalPairProgram.activationApprox security tableBits : ℝ)) -
      (1 - DiffuseProfiles.activation security) = -((LocalPairProgram.activationApprox security tableBits : ℝ) -
      DiffuseProfiles.activation security) by ring, abs_neg]
  rw [he]
  linarith

theorem draw_l1 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ flag, |(drawLaw security tableBits drawBits cache).weight flag -
      (ActualPublicLegCharge.activationLaw security).weight flag|) ≤
      1 / (2 : ℝ)^drawBits + 1 / (2 : ℝ)^tableBits := by
  apply le_trans _ (add_le_add (rounding_l1 security tableBits drawBits cache) (approximate_l1 security tableBits))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun flag _ => abs_sub_le _ ((approximateLaw security tableBits).weight flag) _)

end
end CurrentAFT.CurrentActivationDraw

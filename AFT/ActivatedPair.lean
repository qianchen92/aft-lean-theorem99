import AFT.PhysicalBlockTensors

/-! # Actual marked and unmarked source probabilities retain the same source -/

namespace AFT.BlockDensity

open scoped BigOperators Classical

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Source Color : Type*} [Fintype Source] [Fintype Color]

/-- The exact unmarked source sublaw after activating mass at one atom. -/
def unmarkedSourceWeight (source : FiniteDist Source) (atom : Source) (activation : ℝ) (sample : Source) : ℝ :=
  source.weight sample - if sample = atom then activation else 0

theorem unmarkedSourceWeight_nonneg (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (hactivation : activation ≤ source.weight atom) (sample : Source) :
    0 ≤ unmarkedSourceWeight source atom activation sample := by
  unfold unmarkedSourceWeight
  split_ifs with h
  · subst sample
    exact sub_nonneg.mpr hactivation
  · simpa only [sub_zero] using source.nonneg sample

theorem unmarkedSourceWeight_le (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (hactivation : 0 ≤ activation) (sample : Source) :
    unmarkedSourceWeight source atom activation sample ≤ source.weight sample := by
  unfold unmarkedSourceWeight
  split_ifs <;> linarith

theorem unmarkedSourceWeight_sum (source : FiniteDist Source) (atom : Source) (activation : ℝ) :
    (∑ sample, unmarkedSourceWeight source atom activation sample) = 1 - activation := by
  simp [unmarkedSourceWeight, Finset.sum_sub_distrib, source.sum_one]

/-- The actual activation flag and retained unmarked source, jointly sampled. -/
def activatedSource (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom) : FiniteDist (Unit ⊕ Source) where
  weight := Sum.elim (fun _ => activation) (unmarkedSourceWeight source atom activation)
  nonneg sample := by cases sample with
    | inl _ => exact ha0
    | inr sample => exact unmarkedSourceWeight_nonneg source atom activation ha sample
  sum_one := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, unmarkedSourceWeight_sum]
    ring

/-- The exact physical endpoint pair with its flagged source retained. -/
def activatedPairLaw (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (marked : FiniteDist (Color × Color)) (pair : Source → FiniteDist (Color × Color)) :
    FiniteDist (Color × Color) :=
  (activatedSource source atom activation ha0 ha).mix (Sum.elim (fun _ => marked) pair)

def unmarkedPairMass (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (pair : Source → FiniteDist (Color × Color)) (first second : Color) : ℝ :=
  ∑ sample, unmarkedSourceWeight source atom activation sample * (pair sample).weight (first, second)

theorem activatedPairLaw_weight (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (marked : FiniteDist (Color × Color)) (pair : Source → FiniteDist (Color × Color)) (first second : Color) :
    (activatedPairLaw source atom activation ha0 ha marked pair).weight (first, second) =
      activation * marked.weight (first, second) + unmarkedPairMass source atom activation pair first second := by
  simp only [activatedPairLaw, FiniteDist.mix_weight, activatedSource, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, unmarkedPairMass]

theorem unmarkedPairMass_bounds (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (pair : Source → FiniteDist (Color × Color)) (first second : Color) :
    0 ≤ unmarkedPairMass source atom activation pair first second ∧
      unmarkedPairMass source atom activation pair first second ≤ (source.mix pair).weight (first, second) := by
  constructor
  · exact Finset.sum_nonneg fun sample _ => mul_nonneg
      (unmarkedSourceWeight_nonneg source atom activation ha sample) ((pair sample).nonneg _)
  · exact Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_right
      (unmarkedSourceWeight_le source atom activation ha0 sample) ((pair sample).nonneg _)

/-- Adding two actual endpoint masses retains their squared amplitudes. -/
theorem pairEnergy_add_le (reference : Color → ℝ) (href : ∀ color, 0 ≤ reference color)
    (first second : Color → Color → ℝ) :
    pairEnergy reference reference (fun a b => first a b + second a b) ≤
      2 * pairEnergy reference reference first + 2 * pairEnergy reference reference second := by
  unfold pairEnergy
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have h : (first a b + second a b) ^ 2 ≤ 2 * first a b ^ 2 + 2 * second a b ^ 2 := by
    nlinarith [sq_nonneg (first a b - second a b)]
  convert div_le_div_of_nonneg_right h (mul_nonneg (href a) (href b)) using 1
  ring

/-- Full endpoint energy of the actual activation experiment, with the
activation squared in its marked component and the true source mixture in
its diffuse component. -/
theorem activatedPairLaw_energy_le (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (marked : FiniteDist (Color × Color)) (pair : Source → FiniteDist (Color × Color))
    (reference : Color → ℝ) (href : ∀ color, 0 ≤ reference color) :
    pairEnergy reference reference
      (fun first second => (activatedPairLaw source atom activation ha0 ha marked pair).weight (first, second)) ≤
      2 * pairEnergy reference reference (fun first second => activation * marked.weight (first, second)) +
        2 * pairEnergy reference reference (fun first second => (source.mix pair).weight (first, second)) := by
  simp only [activatedPairLaw_weight]
  apply (pairEnergy_add_le reference href _ _).trans
  gcongr
  apply Finset.sum_le_sum
  intro first _
  apply Finset.sum_le_sum
  intro second _
  have h := unmarkedPairMass_bounds source atom activation ha0 ha pair first second
  exact div_le_div_of_nonneg_right ((sq_le_sq₀ h.1 ((source.mix pair).nonneg _)).mpr h.2)
    (mul_nonneg (href first) (href second))

/-- The actual marked endpoint distribution, including the primary-dependent
companion channel. -/
def markedPairLaw (primary : FiniteDist Color) (companion : Color → FiniteDist Color) :
    FiniteDist (Color × Color) where
  weight point := primary.weight point.1 * (companion point.1).weight point.2
  nonneg point := mul_nonneg (primary.nonneg point.1) ((companion point.1).nonneg point.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one]

/-- The complete endpoint budget of the actual marked/unmarked experiment
uses only point heights of its genuine companion and diffuse mixture. -/
theorem activated_pair_physical_energy_le (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (primary : FiniteDist Color) (companion : Color → FiniteDist Color)
    (pair : Source → FiniteDist (Color × Color))
    (reference : FiniteDist Color) (lower companionUpper diffuseUpper : ℝ)
    (hlower : 0 < lower) (_hcompanionUpper : 0 ≤ companionUpper) (hdiffuseUpper : 0 ≤ diffuseUpper)
    (href : ∀ color, lower ≤ reference.weight color)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper)
    (hdiffuse : ∀ first second, (source.mix pair).weight (first, second) ≤ diffuseUpper) :
    pairEnergy reference.weight reference.weight
      (fun first second => (activatedPairLaw source atom activation ha0 ha (markedPairLaw primary companion) pair).weight (first, second)) ≤
      2 * (activation ^ 2 * companionUpper / (lower * lower)) * (∑ color, primary.weight color ^ 2) +
        2 * diffuseUpper / (lower * lower) := by
  have h := activatedPairLaw_energy_le source atom activation ha0 ha (markedPairLaw primary companion) pair
    reference.weight reference.nonneg
  have hm := marked_pair_energy_le reference.weight reference.weight primary.weight companion activation lower lower companionUpper
    hlower hlower href href hcompanion
  have hd := diffuse_pair_energy_le reference.weight reference.weight
    (fun first second => (source.mix pair).weight (first, second)) lower lower diffuseUpper
    hlower hlower hdiffuseUpper href href (fun first second => (source.mix pair).nonneg _) hdiffuse
    (by rw [← Fintype.sum_prod_type]; exact (source.mix pair).sum_one.le)
  change _ ≤ 2 * pairEnergy reference.weight reference.weight
    (fun first second => activation * (primary.weight first * (companion first).weight second)) + _ at h
  have hm' : pairEnergy reference.weight reference.weight
      (fun first second => activation * (primary.weight first * (companion first).weight second)) ≤
      (activation ^ 2 * companionUpper / (lower * lower)) * (∑ color, primary.weight color ^ 2) := by
    simpa only [mul_assoc] using hm
  calc
    _ ≤ 2 * ((activation ^ 2 * companionUpper / (lower * lower)) * (∑ color, primary.weight color ^ 2)) +
        2 * (diffuseUpper / (lower * lower)) :=
      h.trans (add_le_add (mul_le_mul_of_nonneg_left hm' (by norm_num))
        (mul_le_mul_of_nonneg_left hd (by norm_num)))
    _ = _ := by ring

/-- Every actual local degree of the activated shared-source triple has the
proved physical pair budget. No fresh copy of its source is introduced. -/
theorem activated_triple_physical_degree_energy_le (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom)
    (primary : FiniteDist Color) (companion : Color → FiniteDist Color)
    (pair : Source → FiniteDist (Color × Color))
    (body : Unit ⊕ Source → Color → Color → FiniteDist Color)
    (reference : FiniteDist Color) (lower bodyUpper companionUpper diffuseUpper : ℝ)
    (hlower : 0 < lower) (hbodyUpper : 0 ≤ bodyUpper)
    (hcompanionUpper : 0 ≤ companionUpper) (hdiffuseUpper : 0 ≤ diffuseUpper)
    (href : ∀ color, lower ≤ reference.weight color)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper)
    (hdiffuse : ∀ first second, (source.mix pair).weight (first, second) ≤ diffuseUpper)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ bodyUpper)
    (degree : ℕ) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 3 => reference)
      (PhysicalBlockTensors.sharedSourceTriple (activatedSource source atom activation ha0 ha)
        (Sum.elim (fun _ => markedPairLaw primary companion) pair) body).weight degree) ≤
      8 * (bodyUpper / lower) *
        (2 * (activation ^ 2 * companionUpper / (lower * lower)) * (∑ color, primary.weight color ^ 2) +
          2 * diffuseUpper / (lower * lower)) := by
  apply (PhysicalBlockTensors.shared_source_degree_energy_le
    (activatedSource source atom activation ha0 ha) (Sum.elim (fun _ => markedPairLaw primary companion) pair) body
    reference lower bodyUpper hlower hbodyUpper href hbody degree).trans
  exact mul_le_mul_of_nonneg_left
    (activated_pair_physical_energy_le source atom activation ha0 ha primary companion pair reference
      lower companionUpper diffuseUpper hlower hcompanionUpper hdiffuseUpper href hcompanion hdiffuse)
    (by positivity)

end

end AFT.BlockDensity

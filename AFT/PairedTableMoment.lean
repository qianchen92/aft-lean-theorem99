import AFT.PairedPublicKernel
import AFT.RepresentedTableMoment
import AFT.RepresentedInputMean

/-! # Complete paired public control weights and all fixed even moments -/
namespace AFT.RepresentedPolynomial
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedTableMomentSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

/-- Apply all primary/compensator scores to the actual disjoint seed product. -/
def twoPoolPairedKernel (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (seeds : List (InputSeed Color)) :
    ((ControlPrimarySlot seeds ⊕ ControlBodySlot seeds) → Color × Color) → ℝ :=
  pairedPublicKernel primary body anchor activation (Sum.elim (fun _ => true) (fun _ => false))
    (twoPoolControlKernel seeds)

def monomialPairedStatistic (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) :
    ((Fin primaryPool ⊕ Fin bodyPool) → Color × Color) → ℝ :=
  twoPoolStatistic (twoPoolPairedKernel primary body anchor activation (monomialOccurrences powers))

/-- The original coefficients, including cancellation, are retained in the
complete public score rather than replaced by an absolute term sum. -/
def tablePairedStatistic (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color)) :
    ((Fin primaryPool ⊕ Fin bodyPool) → Color × Color) → ℝ :=
  fun word => table.sum fun powers coefficient => coefficient *
    monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word

theorem twoPoolPairedKernel_canonical (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (seeds : List (InputSeed Color))
    (hc : ∀ seed ∈ seeds, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical
      (Sum.elim (fun _ : ControlPrimarySlot seeds => primary.prod body) (fun _ : ControlBodySlot seeds => primary.prod body))
      Finset.univ (twoPoolPairedKernel primary body anchor activation seeds) := by
  have hi : (fun slot : ControlPrimarySlot seeds ⊕ ControlBodySlot seeds =>
      if Sum.elim (fun _ => true) (fun _ => false) slot then primary else body) =
      Sum.elim (fun _ => primary) (fun _ => body) := by funext slot; cases slot <;> rfl
  have ho : (fun _ : ControlPrimarySlot seeds ⊕ ControlBodySlot seeds => primary.prod body) =
      Sum.elim (fun _ => primary.prod body) (fun _ => primary.prod body) := by funext slot; cases slot <;> rfl
  have hh := pairedPublicKernel_canonical primary body anchor activation
    (Sum.elim (fun _ : ControlPrimarySlot seeds => true) (fun _ : ControlBodySlot seeds => false))
    hmass hsupport (twoPoolControlKernel seeds)
  rw [hi] at hh
  simpa only [twoPoolPairedKernel, ho] using hh (twoPoolControlKernel_canonical primary body seeds hc)

theorem twoPoolPairedKernel_activity_le (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation comparison : ℝ) (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (primaryPool bodyPool radius : ℝ) (hradius : 1 ≤ radius) (seeds : List (InputSeed Color)) :
    MixedKernel.activity
      (Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt primaryPool) (fun _ : ControlBodySlot seeds => 1 / Real.sqrt bodyPool))
      (Sum.elim (fun _ : ControlPrimarySlot seeds => primary.prod body) (fun _ : ControlBodySlot seeds => primary.prod body))
      (twoPoolPairedKernel primary body anchor activation seeds) ≤
      (comparison+2)^(2 * finiteControlCount seeds) * (seeds.map (inputWeight primary body primaryPool bodyPool radius)).prod := by
  let rates := Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt primaryPool)
    (fun _ : ControlBodySlot seeds => 1 / Real.sqrt bodyPool)
  have hi : (fun slot : ControlPrimarySlot seeds ⊕ ControlBodySlot seeds =>
      if Sum.elim (fun _ => true) (fun _ => false) slot then primary else body) =
      Sum.elim (fun _ => primary) (fun _ => body) := by funext slot; cases slot <;> rfl
  have ho : (fun _ : ControlPrimarySlot seeds ⊕ ControlBodySlot seeds => primary.prod body) =
      Sum.elim (fun _ => primary.prod body) (fun _ => primary.prod body) := by funext slot; cases slot <;> rfl
  have hcard : Fintype.card (ControlPrimarySlot seeds ⊕ ControlBodySlot seeds) = finiteControlCount seeds :=
    Fintype.card_congr (controlPoolEquiv seeds)
  have hh := pairedPublicKernel_activity_le primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare
    (Sum.elim (fun _ : ControlPrimarySlot seeds => true) (fun _ : ControlBodySlot seeds => false)) rates
    (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _)) (twoPoolControlKernel seeds)
  rw [hi, ho, hcard] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (twoPoolControlKernel_activity_le primary body primaryPool bodyPool radius hradius seeds) (by positivity))

def representedPairedMomentConstant (comparison : ℝ) (order moment : ℕ) : ℝ :=
  representedInputMomentConstant order moment * (comparison + 2)^(2 * order)

theorem representedPairedMomentConstant_nonneg (comparison : ℝ) (order moment : ℕ) :
    0 ≤ representedPairedMomentConstant comparison order moment :=
  mul_nonneg (representedInputMomentConstant_nonneg _ _) (Even.pow_nonneg (⟨order, by omega⟩ : Even (2 * order)) _)

/-- All even moments of the genuine paired monomial use its original
input activity and the actual distinct-index normalizers of both pools. -/
theorem monomialPairedStatistic_even_moment (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation comparison : ℝ)
    (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel)
    (order : ℕ) (horder : finiteControlCount (monomialOccurrences powers) ≤ order)
    (hprimaryLarge : 2 * order ≤ primaryPool) (hbodyLarge : 2 * order ≤ bodyPool)
    (moment : ℕ) (hmoment : 0 < moment) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary.prod body) (fun _ : Fin bodyPool => primary.prod body))).expectation
      (fun word => |monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word| ^ (2 * moment)) ≤
      (representedPairedMomentConstant comparison order moment * monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers) ^ (2 * moment) := by
  let seeds := monomialOccurrences powers
  have hpc : Fintype.card (ControlPrimarySlot seeds) ≤ order := (controlPrimarySlot_card_le seeds).trans horder
  have hbc : Fintype.card (ControlBodySlot seeds) ≤ order := (controlBodySlot_card_le seeds).trans horder
  have hk := twoPoolPairedKernel_canonical primary body anchor activation hmass hsupport seeds
    (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))
  have hh := twoPoolStatistic_even_moment_le_activity (PP := Fin primaryPool) (BP := Fin bodyPool)
    (primary.prod body) (primary.prod body) (twoPoolPairedKernel primary body anchor activation seeds) hk moment
    (by simpa using hprimary) (by simpa using hbody)
    (by simpa using (Nat.mul_le_mul_left 2 hpc).trans hprimaryLarge)
    (by simpa using (Nat.mul_le_mul_left 2 hbc).trans hbodyLarge)
  simp only [Fintype.card_fin] at hh
  have ha0 := twoPoolPairedKernel_activity_le primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare
    primaryPool bodyPool radius hradius seeds
  rw [monomialOccurrences_weight] at ha0
  have ha' := ha0.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ comparison+2) (Nat.mul_le_mul_left 2 horder))
    (monomialWeight_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed (le_trans zero_le_one hradius)) _))
  have hc1 := momentConstant_le_inputMomentEnvelope (Fintype.card (ControlPrimarySlot seeds)) order (2 * moment) hpc
  have hc2 := momentConstant_le_inputMomentEnvelope (Fintype.card (ControlBodySlot seeds)) order (2 * moment) hbc
  have hconst : momentConstant (Fintype.card (ControlPrimarySlot seeds)) (2 * moment) *
      momentConstant (Fintype.card (ControlBodySlot seeds)) (2 * moment) ≤
      representedInputMomentConstant order moment ^ (2 * moment) := by
    calc
      _ ≤ max 1 (inputMomentEnvelope order (2 * moment)) * max 1 (inputMomentEnvelope order (2 * moment)) :=
        mul_le_mul (hc1.trans (le_max_right ..)) (hc2.trans (le_max_right ..))
          (by unfold momentConstant; positivity) (le_trans zero_le_one (le_max_left ..))
      _ = representedInputMomentConstant order moment := by unfold representedInputMomentConstant; ring
      _ ≤ _ := le_self_pow₀ (representedInputMomentConstant_ge_one order moment) (by omega)
  have han : 0 ≤ MixedKernel.activity (Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt (primaryPool : ℝ))
      (fun _ : ControlBodySlot seeds => 1 / Real.sqrt (bodyPool : ℝ)))
      (Sum.elim (fun _ : ControlPrimarySlot seeds => primary.prod body) (fun _ : ControlBodySlot seeds => primary.prod body))
      (twoPoolPairedKernel primary body anchor activation seeds) :=
    MixedKernel.activity_nonneg _ _ _ (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  apply hh.trans
  have ht := mul_le_mul hconst (pow_le_pow_left₀ han ha' (2 * moment)) (pow_nonneg han (2 * moment)) (pow_nonneg (representedInputMomentConstant_nonneg order moment) (2 * moment))
  exact ht.trans_eq (by unfold representedPairedMomentConstant; ring)
/-- Every fixed even moment is controlled by the original represented
activity. There is no constant depending on the number of monomials. -/
theorem tablePairedStatistic_even_moment (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation comparison : ℝ)
    (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (hsupport : ∀ point center, body.weight center = 0 → anchor point center = 0)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table)
    (order : ℕ) (horder : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hprimaryLarge : 2 * order ≤ primaryPool) (hbodyLarge : 2 * order ≤ bodyPool)
    (moment : ℕ) (hmoment : 0 < moment) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary.prod body) (fun _ : Fin bodyPool => primary.prod body))).expectation
      (fun word => |tablePairedStatistic primary body anchor activation primaryPool bodyPool table word| ^ (2 * moment)) ≤
      (representedPairedMomentConstant comparison order moment * activity (inputWeight primary body primaryPool bodyPool radius) table) ^ (2 * moment) := by
  let law := FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary.prod body) (fun _ : Fin bodyPool => primary.prod body))
  let weight := inputWeight primary body primaryPool bodyPool radius
  let value (term : table.support) (word) := MvPolynomial.coeff term.val table * monomialPairedStatistic primary body anchor activation primaryPool bodyPool term.val word
  let bound (term : table.support) := |MvPolynomial.coeff term.val table| *
    (representedPairedMomentConstant comparison order moment * monomialWeight weight term.val)
  have hn (term : table.support) : 0 ≤ bound term := mul_nonneg (abs_nonneg _)
    (mul_nonneg (representedPairedMomentConstant_nonneg comparison order moment)
      (monomialWeight_nonneg weight (fun seed => inputWeight_nonneg _ _ _ _ _ seed (le_trans zero_le_one hradius)) _))
  have hm (term : table.support) : law.expectation (fun word => |value term word| ^ (2 * moment)) ≤ bound term ^ (2 * moment) := by
    have ht := monomialPairedStatistic_even_moment primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare hsupport primaryPool bodyPool hprimary hbody radius hradius term.val
      (hc term.val term.property) order (horder term.val term.property) hprimaryLarge hbodyLarge moment hmoment
    dsimp only [value, bound]
    simp only [abs_mul, mul_pow]
    rw [FiniteDist.expectation_const_mul]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg (MvPolynomial.coeff term.val table)) (2 * moment))
  have hh := FiniteDist.expectation_abs_sum_pow_le law value bound hn (2 * moment) (by omega) hm
  have hvalue (word) : (∑ term : table.support, value term word) = tablePairedStatistic primary body anchor activation primaryPool bodyPool table word := by
    exact Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table * monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word)
  have hbound : (∑ term : table.support, bound term) =
      representedPairedMomentConstant comparison order moment * activity weight table := by
    calc
      _ = ∑ powers ∈ table.support, |MvPolynomial.coeff powers table| *
          (representedPairedMomentConstant comparison order moment * monomialWeight weight powers) :=
        Finset.sum_coe_sort table.support _
      _ = _ := by
        unfold activity Finsupp.sum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro powers _
        simp only [MvPolynomial.coeff]
        ring
  simpa only [hvalue, hbound] using hh

end
end AFT.RepresentedPolynomial

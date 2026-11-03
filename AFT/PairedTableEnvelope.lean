import AFT.PairedTableMoment
import AFT.RepresentedLocalSum

/-! # Polynomial envelopes and actual local scopes of the complete paired table -/
namespace AFT.RepresentedPolynomial
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedTableEnvelopeSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

theorem monomial_paired_kernel_pointwise_envelope (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation comparison : ℝ)
    (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (powers : InputSeed Color →₀ ℕ) (order : ℕ) (ho : finiteControlCount (monomialOccurrences powers) ≤ order)
    (word : (ControlPrimarySlot (monomialOccurrences powers) ⊕ ControlBodySlot (monomialOccurrences powers)) → Color × Color) :
    |twoPoolPairedKernel primary body anchor activation (monomialOccurrences powers) word| ≤
      (comparison+2)^(2*order) * ((max (primaryPool : ℝ) (bodyPool : ℝ))^(2*order) *
        monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers) := by
  let seeds := monomialOccurrences powers
  have hh := pairedPublicKernel_fiberNorm_le primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare
    (Sum.elim (fun _ : ControlPrimarySlot seeds => true) (fun _ : ControlBodySlot seeds => false)) Finset.univ
    (twoPoolControlKernel seeds)
  simp only [MixedKernel.fiberNorm_univ] at hh
  have hcard : Fintype.card (ControlPrimarySlot seeds ⊕ ControlBodySlot seeds) = finiteControlCount seeds :=
    Fintype.card_congr (controlPoolEquiv seeds)
  rw [hcard] at hh
  have hn := twoPoolControlKernel_norm_le primary body primaryPool bodyPool hp hb radius hradius seeds order ho
  rw [monomialOccurrences_weight] at hn
  have hcost := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ comparison+2) (Nat.mul_le_mul_left 2 ho)
  have hout := hh.trans (mul_le_mul hcost hn (norm_nonneg _) (by positivity))
  have hvalue := norm_le_pi_norm (twoPoolPairedKernel primary body anchor activation seeds) word
  have hv : |twoPoolPairedKernel primary body anchor activation seeds word| ≤
      ‖twoPoolPairedKernel primary body anchor activation seeds‖ := by simpa only [Real.norm_eq_abs] using hvalue
  exact hv.trans hout

def tablePairedLocalTerm (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (index : TableLocalIndex primaryPool bodyPool table) (word : (Fin primaryPool ⊕ Fin bodyPool) → Color × Color) : ℝ :=
  MvPolynomial.coeff index.1.val table / monomialPlacementCount primaryPool bodyPool index.1.val *
    placedKernel (twoPoolPairedKernel primary body anchor activation (monomialOccurrences index.1.val))
      (index.2.1.sumMap index.2.2) word

theorem tablePairedStatistic_local_sum (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (word : (Fin primaryPool ⊕ Fin bodyPool) → Color × Color) :
    tablePairedStatistic primary body anchor activation primaryPool bodyPool table word =
      ∑ index : TableLocalIndex primaryPool bodyPool table,
        tablePairedLocalTerm primary body anchor activation primaryPool bodyPool table index word := by
  rw [Fintype.sum_sigma]
  have he := Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table *
    monomialPairedStatistic primary body anchor activation primaryPool bodyPool powers word)
  apply he.symm.trans
  apply Finset.sum_congr rfl
  intro term _
  simp only [monomialPairedStatistic, twoPoolStatistic, tablePairedLocalTerm, monomialPlacementCount_eq, Fintype.card_fin, ← Finset.mul_sum]
  ring

def tablePairedEnvelope (comparison : ℝ) (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (radius : ℝ) (table : Table (InputSeed Color)) (order : ℕ) : ℝ :=
  (comparison+2)^(2*order) * tableInputEnvelope primary body primaryPool bodyPool radius table order

theorem tablePairedLocalTerm_bound (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation comparison : ℝ) (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (index : TableLocalIndex primaryPool bodyPool table) (word : (Fin primaryPool ⊕ Fin bodyPool) → Color × Color) :
    |tablePairedLocalTerm primary body anchor activation primaryPool bodyPool table index word| ≤
      (comparison+2)^(2*order) * tableLocalBound primary body primaryPool bodyPool radius table order index := by
  unfold tablePairedLocalTerm tableLocalBound placedKernel
  rw [abs_mul, abs_div, abs_of_nonneg (show 0 ≤ monomialPlacementCount primaryPool bodyPool index.1.val by unfold monomialPlacementCount; positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (monomial_paired_kernel_pointwise_envelope primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare
      primaryPool bodyPool hp hb radius hradius index.1.val order (ho index.1.val index.1.property) (word ∘ (index.2.1.sumMap index.2.2)))
    (div_nonneg (abs_nonneg (MvPolynomial.coeff index.1.val table)) (show 0 ≤ monomialPlacementCount primaryPool bodyPool index.1.val by unfold monomialPlacementCount; positivity))
  exact hh.trans_eq (by ring)

theorem tablePairedStatistic_abs_le_envelope (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation comparison : ℝ) (ha : 0 ≤ activation) (ha1 : activation ≤ 1) (hK : 0 ≤ comparison)
    (hanchor : ∀ color center, 0 ≤ anchor color center) (hmass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, activation * applyAnchor anchor primary.weight center ≤ comparison * body.weight center)
    (primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hpl : order ≤ primaryPool) (hbl : order ≤ bodyPool)
    (word : (Fin primaryPool ⊕ Fin bodyPool) → Color × Color) :
    |tablePairedStatistic primary body anchor activation primaryPool bodyPool table word| ≤
      tablePairedEnvelope comparison primary body primaryPool bodyPool radius table order := by
  rw [tablePairedStatistic_local_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun index _ => tablePairedLocalTerm_bound primary body anchor activation comparison ha ha1 hK hanchor hmass hcompare
    primaryPool bodyPool hp hb radius hradius table order ho index word).trans_eq
  rw [← Finset.mul_sum, tableLocalBound_sum primary body primaryPool bodyPool radius table order ho hpl hbl]
  rfl

variable {FullBody : Type*} [Fintype FullBody]

/-- Both primary compensators and ordinary body centers lie in the same
full charged body word, with a single injective retained-pool embedding. -/
def pairedRetainedWord (primaryPool bodyPool : ℕ)
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ FullBody)
    (marks : (Fin primaryPool ⊕ Fin bodyPool) → Color) (centers : FullBody → Color) :
    (Fin primaryPool ⊕ Fin bodyPool) → Color × Color := fun slot => (marks slot, centers (embedding slot))

def tablePairedBodyScope (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ FullBody)
    (index : TableLocalIndex primaryPool bodyPool table) : Finset FullBody :=
  Finset.univ.map ((index.2.1.sumMap index.2.2).trans embedding)

omit [Fintype Color] [Fintype FullBody] in
theorem tablePairedBodyScope_card_le (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ FullBody)
    (index : TableLocalIndex primaryPool bodyPool table) (order : ℕ)
    (ho : finiteControlCount (monomialOccurrences index.1.val) ≤ order) :
    (tablePairedBodyScope primaryPool bodyPool table embedding index).card ≤ order := by
  simp only [tablePairedBodyScope, Finset.card_map, Finset.card_univ]
  exact (Fintype.card_congr (controlPoolEquiv (monomialOccurrences index.1.val))).trans_le ho

omit [Fintype FullBody] in
theorem tablePairedLocalTerm_body_depends (primary body : FiniteDist Color) (anchor : Color → Color → ℝ)
    (activation : ℝ) (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ FullBody)
    (marks : (Fin primaryPool ⊕ Fin bodyPool) → Color) (index : TableLocalIndex primaryPool bodyPool table) :
    Hoeffding.DependsOn (tablePairedBodyScope primaryPool bodyPool table embedding index)
      (fun centers : FullBody → Color => tablePairedLocalTerm primary body anchor activation primaryPool bodyPool table index
        (pairedRetainedWord primaryPool bodyPool embedding marks centers)) := by
  intro first second he
  unfold tablePairedLocalTerm placedKernel
  apply congrArg (MvPolynomial.coeff index.1.val table / monomialPlacementCount primaryPool bodyPool index.1.val * ·)
  apply congrArg (twoPoolPairedKernel primary body anchor activation (monomialOccurrences index.1.val))
  funext slot
  apply Prod.ext
  · rfl
  · exact he _ (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
end
end AFT.RepresentedPolynomial

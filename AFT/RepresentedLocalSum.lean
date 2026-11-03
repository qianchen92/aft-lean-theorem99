import AFT.RepresentedInputEnvelope

/-! # Actual local injection expansion and polynomial envelope of a table -/
namespace AFT.RepresentedPolynomial
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedLocalSumSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

abbrev MonomialPlacement (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) :=
  (ControlPrimarySlot (monomialOccurrences powers) ↪ Fin primaryPool) ×
    (ControlBodySlot (monomialOccurrences powers) ↪ Fin bodyPool)

abbrev TableLocalIndex (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color)) :=
  (term : table.support) × MonomialPlacement primaryPool bodyPool term.val

def monomialPlacementCount (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) : ℝ :=
  Fintype.card (MonomialPlacement primaryPool bodyPool powers)

omit [Fintype Color] in
theorem monomialPlacementCount_eq (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) :
    monomialPlacementCount primaryPool bodyPool powers =
      (primaryPool.descFactorial (Fintype.card (ControlPrimarySlot (monomialOccurrences powers))) : ℝ) *
      (bodyPool.descFactorial (Fintype.card (ControlBodySlot (monomialOccurrences powers))) : ℝ) := by
  simp [monomialPlacementCount, Fintype.card_prod, Fintype.card_embedding_eq]

omit [Fintype Color] in
theorem monomialPlacementCount_pos (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ)
    (order : ℕ) (ho : finiteControlCount (monomialOccurrences powers) ≤ order)
    (hp : order ≤ primaryPool) (hb : order ≤ bodyPool) :
    0 < monomialPlacementCount primaryPool bodyPool powers := by
  rw [monomialPlacementCount_eq]
  exact mul_pos
    (by exact_mod_cast Nat.descFactorial_pos.mpr ((controlPrimarySlot_card_le _).trans (ho.trans hp)))
    (by exact_mod_cast Nat.descFactorial_pos.mpr ((controlBodySlot_card_le _).trans (ho.trans hb)))

def tableLocalTerm (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (index : TableLocalIndex primaryPool bodyPool table) (word : (Fin primaryPool ⊕ Fin bodyPool) → Color) : ℝ :=
  MvPolynomial.coeff index.1.val table / monomialPlacementCount primaryPool bodyPool index.1.val *
    placedKernel (twoPoolControlKernel (monomialOccurrences index.1.val)) (index.2.1.sumMap index.2.2) word

omit [Fintype Color] in
theorem tableInputStatistic_local_sum (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (word : (Fin primaryPool ⊕ Fin bodyPool) → Color) :
    tableInputStatistic primaryPool bodyPool table word =
      ∑ index : TableLocalIndex primaryPool bodyPool table, tableLocalTerm primaryPool bodyPool table index word := by
  rw [Fintype.sum_sigma]
  have he := Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table * monomialInputStatistic primaryPool bodyPool powers word)
  apply he.symm.trans
  apply Finset.sum_congr rfl
  intro term _
  simp only [monomialInputStatistic, twoPoolStatistic, tableLocalTerm, monomialPlacementCount_eq, Fintype.card_fin, ← Finset.mul_sum]
  ring

def tableLocalBound (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ) (radius : ℝ)
    (table : Table (InputSeed Color)) (order : ℕ) (index : TableLocalIndex primaryPool bodyPool table) : ℝ :=
  |MvPolynomial.coeff index.1.val table| / monomialPlacementCount primaryPool bodyPool index.1.val *
    ((max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
      monomialWeight (inputWeight primary body primaryPool bodyPool radius) index.1.val)

theorem tableLocalBound_nonneg (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (radius : ℝ) (hradius : 0 ≤ radius) (table : Table (InputSeed Color)) (order : ℕ)
    (index : TableLocalIndex primaryPool bodyPool table) :
    0 ≤ tableLocalBound primary body primaryPool bodyPool radius table order index := by
  apply mul_nonneg (div_nonneg (abs_nonneg _) (by unfold monomialPlacementCount; positivity))
  exact mul_nonneg (by positivity) (monomialWeight_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _)

theorem tableLocalTerm_bound (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (index : TableLocalIndex primaryPool bodyPool table) (word : (Fin primaryPool ⊕ Fin bodyPool) → Color) :
    |tableLocalTerm primaryPool bodyPool table index word| ≤
      tableLocalBound primary body primaryPool bodyPool radius table order index := by
  unfold tableLocalTerm tableLocalBound placedKernel
  rw [abs_mul, abs_div]
  rw [abs_of_nonneg (show 0 ≤ monomialPlacementCount primaryPool bodyPool index.1.val by unfold monomialPlacementCount; positivity)]
  exact mul_le_mul_of_nonneg_left (monomial_kernel_pointwise_envelope primary body primaryPool bodyPool hp hb
    radius hradius index.1.val order (ho index.1.val index.1.property) _)
    (div_nonneg (abs_nonneg _) (by unfold monomialPlacementCount; positivity))

theorem tableLocalBound_sum (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (radius : ℝ) (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hp : order ≤ primaryPool) (hb : order ≤ bodyPool) :
    (∑ index : TableLocalIndex primaryPool bodyPool table, tableLocalBound primary body primaryPool bodyPool radius table order index) =
      (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
        activity (inputWeight primary body primaryPool bodyPool radius) table := by
  rw [Fintype.sum_sigma]
  have ht (term : table.support) : (∑ placement : MonomialPlacement primaryPool bodyPool term.val,
      tableLocalBound primary body primaryPool bodyPool radius table order ⟨term, placement⟩) =
      (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
        (|MvPolynomial.coeff term.val table| * monomialWeight (inputWeight primary body primaryPool bodyPool radius) term.val) := by
    simp only [tableLocalBound, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change monomialPlacementCount primaryPool bodyPool term.val * _ = _
    have hn := (monomialPlacementCount_pos primaryPool bodyPool term.val order (ho term.val term.property) hp hb).ne'
    field_simp
  simp only [ht, ← Finset.mul_sum]
  exact congrArg (fun total : ℝ => (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) * total)
    (Finset.sum_coe_sort table.support (fun powers => |MvPolynomial.coeff powers table| * monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers))

/-- The explicit rejection envelope is polynomial in the retained pool sizes
at every fixed input-order cutoff. -/
def tableInputEnvelope (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (radius : ℝ) (table : Table (InputSeed Color)) (order : ℕ) : ℝ :=
  (max (primaryPool : ℝ) (bodyPool : ℝ)) ^ (2 * order) *
    activity (inputWeight primary body primaryPool bodyPool radius) table

theorem tableInputStatistic_abs_le_envelope (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hpl : order ≤ primaryPool) (hbl : order ≤ bodyPool)
    (word : (Fin primaryPool ⊕ Fin bodyPool) → Color) :
    |tableInputStatistic primaryPool bodyPool table word| ≤
      tableInputEnvelope primary body primaryPool bodyPool radius table order := by
  rw [tableInputStatistic_local_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun index _ => tableLocalTerm_bound primary body primaryPool bodyPool hp hb radius hradius table order ho index word).trans_eq
  exact tableLocalBound_sum primary body primaryPool bodyPool radius table order ho hpl hbl

theorem table_positive_weight_envelope (primary body : FiniteDist Color) (primaryPool bodyPool : ℕ)
    (hp : 0 < primaryPool) (hb : 0 < bodyPool) (radius : ℝ) (hradius : 1 ≤ radius)
    (table : Table (InputSeed Color)) (order : ℕ)
    (ho : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hpl : order ≤ primaryPool) (hbl : order ≤ bodyPool)
    (word : (Fin primaryPool ⊕ Fin bodyPool) → Color) :
    max (1 + tableInputStatistic primaryPool bodyPool table word) 0 ≤
      1 + tableInputEnvelope primary body primaryPool bodyPool radius table order := by
  have hh := tableInputStatistic_abs_le_envelope primary body primaryPool bodyPool hp hb radius hradius table order ho hpl hbl word
  apply max_le
  · linarith [le_abs_self (tableInputStatistic primaryPool bodyPool table word)]
  · linarith [abs_nonneg (tableInputStatistic primaryPool bodyPool table word)]

variable {FullBody : Type*} [Fintype FullBody]

def tableBodyScope (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (bodyEmbedding : Fin bodyPool ↪ FullBody) (index : TableLocalIndex primaryPool bodyPool table) : Finset FullBody :=
  Finset.univ.map (index.2.2.trans bodyEmbedding)

omit [Fintype Color] [Fintype FullBody] in
theorem tableBodyScope_card_le (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (bodyEmbedding : Fin bodyPool ↪ FullBody) (index : TableLocalIndex primaryPool bodyPool table)
    (order : ℕ) (ho : finiteControlCount (monomialOccurrences index.1.val) ≤ order) :
    (tableBodyScope primaryPool bodyPool table bodyEmbedding index).card ≤ order := by
  simpa only [tableBodyScope, Finset.card_map, Finset.card_univ] using (controlBodySlot_card_le _).trans ho

omit [Fintype Color] [Fintype FullBody] in
theorem tableLocalTerm_body_depends (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color))
    (bodyEmbedding : Fin bodyPool ↪ FullBody) (primaryWord : Fin primaryPool → Color)
    (index : TableLocalIndex primaryPool bodyPool table) :
    Hoeffding.DependsOn (tableBodyScope primaryPool bodyPool table bodyEmbedding index)
      (fun word : FullBody → Color => tableLocalTerm primaryPool bodyPool table index
        (Sum.elim primaryWord (word ∘ bodyEmbedding))) := by
  intro first second he
  unfold tableLocalTerm placedKernel
  apply congrArg (MvPolynomial.coeff index.1.val table / monomialPlacementCount primaryPool bodyPool index.1.val * ·)
  apply congrArg (twoPoolControlKernel (monomialOccurrences index.1.val))
  funext slot
  cases slot with
  | inl slot => rfl
  | inr slot => exact he _ (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)

end
end AFT.RepresentedPolynomial

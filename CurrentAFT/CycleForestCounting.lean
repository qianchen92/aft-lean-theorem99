import CurrentAFT.CycleSelections

/-!
# Counting non-isolated selections by their oriented path forests

For each selected vertex, record its selected predecessor, if one exists.
A proper selected subset of one cycle cannot contain a directed cycle.
Consequently this predecessor pattern is a union of directed paths, and
its root positions determine the complete embedding. A non-isolated
pattern has at most half as many roots as vertices. The finite encoding
therefore counts rare selections with the required full-order exponent.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Every selected vertex has another selected cyclic neighbor. -/
def NoIsolated {body order : ℕ} (sites : Selection body order) : Prop :=
  ∀ slot, ∃ other, other ≠ slot ∧ Adjacent body (sites slot) (sites other)

/-- The oriented selected predecessor, with `none` at the start of each path. -/
def predecessorPattern {body order : ℕ} (sites : Selection body order) (slot : Fin order) : Option (Fin order) :=
  if h : ∃ previous, sites previous = (finRotate body).symm (sites slot) then
    some (Classical.choose h) else none

theorem predecessorPattern_some {body order : ℕ} (sites : Selection body order)
    (slot previous : Fin order) :
    predecessorPattern sites slot = some previous ↔
      sites previous = (finRotate body).symm (sites slot) := by
  unfold predecessorPattern
  split_ifs with h
  · constructor
    · intro hequal
      have hlabels := Option.some.inj hequal
      rw [← hlabels]
      exact Classical.choose_spec h
    · intro hprevious
      apply congrArg some
      exact sites.injective ((Classical.choose_spec h).trans hprevious.symm)
  · constructor
    · intro hnone
      cases hnone
    · intro hprevious
      exact False.elim (h ⟨previous, hprevious⟩)

theorem predecessorPattern_none {body order : ℕ} (sites : Selection body order) (slot : Fin order) :
    predecessorPattern sites slot = none ↔
      ¬∃ previous, sites previous = (finRotate body).symm (sites slot) := by
  unfold predecessorPattern
  split_ifs with h <;> simp [h]

abbrev PatternRoots {order : ℕ} (pattern : Fin order → Option (Fin order)) :=
  {slot : Fin order // pattern slot = none}

/-- A path root in a non-isolated selection has a selected successor. -/
theorem root_has_child {body order : ℕ} (sites : Selection body order)
    (hno : NoIsolated sites) (slot : Fin order) (hroot : predecessorPattern sites slot = none) :
    ∃ child, predecessorPattern sites child = some slot := by
  obtain ⟨other, _, hadjacent⟩ := hno slot
  rcases hadjacent with hnext | hprevious
  · refine ⟨other, (predecessorPattern_some sites other slot).2 ?_⟩
    rw [hnext, Equiv.symm_apply_apply]
  · have hforbidden := (predecessorPattern_none sites slot).1 hroot
    apply False.elim
    apply hforbidden
    refine ⟨other, ?_⟩
    apply (finRotate body).injective
    simpa only [Equiv.apply_symm_apply] using hprevious.symm

/-- Different roots inject into different non-root successors. -/
theorem noIsolated_roots_card {body order : ℕ} (sites : Selection body order) (hno : NoIsolated sites) :
    Fintype.card (PatternRoots (predecessorPattern sites)) ≤ order / 2 := by
  let child := fun root : PatternRoots (predecessorPattern sites) =>
    Classical.choose (root_has_child sites hno root root.property)
  have hchild (root : PatternRoots (predecessorPattern sites)) :
      predecessorPattern sites (child root) = some root.val :=
    Classical.choose_spec (root_has_child sites hno root root.property)
  let map : PatternRoots (predecessorPattern sites) →
      {slot : Fin order // predecessorPattern sites slot ≠ none} :=
    fun root => ⟨child root, by rw [hchild]; simp⟩
  have hinjective : Function.Injective map := by
    intro first second hequal
    have hvalues := congrArg Subtype.val hequal
    have hfirst := hchild first
    have hsecond := hchild second
    change child first = child second at hvalues
    rw [hvalues] at hfirst
    apply Subtype.ext
    exact Option.some.inj (hfirst.symm.trans hsecond)
  have hcount := Fintype.card_le_of_injective map hinjective
  rw [Fintype.card_subtype_compl, Fintype.card_fin] at hcount
  dsimp only [PatternRoots] at hcount ⊢
  omega

/-- A nonempty subset closed under cyclic predecessor is the whole body.
This proves that proper selected subsets have no directed cycle. -/
theorem predecessor_closed_eq_univ (body : ℕ) (hbody : 2 ≤ body)
    (vertices : Finset (Fin body)) (hnonempty : vertices.Nonempty)
    (hclosed : ∀ vertex ∈ vertices, (finRotate body).symm vertex ∈ vertices) :
    vertices = Finset.univ := by
  obtain ⟨start, hstart⟩ := hnonempty
  apply Finset.eq_univ_of_forall
  intro target
  have hcycle := (isCycle_finRotate_of_le hbody).inv
  obtain ⟨steps, hsteps⟩ := hcycle.exists_pow_eq
    (ProtectedCycle.cycle_predecessor_ne body hbody start)
    (ProtectedCycle.cycle_predecessor_ne body hbody target)
  have hpowers : ∀ steps : ℕ, ((finRotate body)⁻¹ ^ steps) start ∈ vertices := by
    intro steps
    induction steps with
    | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using hstart
    | succ steps ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hclosed _ ih
  simpa only [hsteps] using hpowers steps

/-- For proper selections the selected predecessor pattern and the positions
of its roots determine every selected body position. -/
theorem embedding_eq_of_pattern_roots {body order : ℕ} (hbody : 2 ≤ body) (hproper : order < body)
    (first second : Selection body order)
    (hpattern : predecessorPattern first = predecessorPattern second)
    (hroots : ∀ slot, predecessorPattern first slot = none → first slot = second slot) :
    first = second := by
  by_contra hne
  have hlabel : ∃ slot, first slot ≠ second slot := by
    by_contra hnone
    apply hne
    apply DFunLike.ext
    intro slot
    exact not_not.mp (not_exists.mp hnone slot)
  let bad := Finset.univ.filter (fun slot : Fin order => first slot ≠ second slot)
  let vertices := bad.image first
  have hnonempty : vertices.Nonempty := by
    obtain ⟨slot, hslot⟩ := hlabel
    exact ⟨first slot, Finset.mem_image.mpr ⟨slot, by simp [bad, hslot], rfl⟩⟩
  have hclosed : ∀ vertex ∈ vertices, (finRotate body).symm vertex ∈ vertices := by
    intro vertex hvertex
    obtain ⟨slot, hbad, rfl⟩ := Finset.mem_image.mp hvertex
    have hbad' : first slot ≠ second slot := (Finset.mem_filter.mp hbad).2
    cases hparent : predecessorPattern first slot with
    | none => exact False.elim (hbad' (hroots slot hparent))
    | some previous =>
      have hfirst := (predecessorPattern_some first slot previous).1 hparent
      have hsecond : second previous = (finRotate body).symm (second slot) := by
        apply (predecessorPattern_some second slot previous).1
        rw [← hpattern]
        exact hparent
      have hpreviousBad : previous ∈ bad := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hagree
        apply hbad'
        apply (finRotate body).symm.injective
        exact hfirst.symm.trans (hagree.trans hsecond)
      exact Finset.mem_image.mpr ⟨previous, hpreviousBad, hfirst⟩
  have huniv := predecessor_closed_eq_univ body hbody vertices hnonempty hclosed
  have hcardImage : vertices.card ≤ bad.card := Finset.card_image_le
  have hbadCard : bad.card ≤ order := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcardImage
  omega

/-- Counting the actual predecessor-pattern fibers. Every path contributes
one free root position, and all remaining positions are forced successors. -/
theorem noIsolated_selection_card_le (body order : ℕ) (hbody : 2 ≤ body) (hproper : order < body) :
    Fintype.card {sites : Selection body order // NoIsolated sites} ≤
      (order + 1) ^ order * body ^ (order / 2) := by
  let Good := {sites : Selection body order // NoIsolated sites}
  let Patterns := Fin order → Option (Fin order)
  let parent : Good → Patterns := fun sites => predecessorPattern sites.val
  have hfiber (pattern : Patterns) :
      Fintype.card {sites : Good // parent sites = pattern} ≤ body ^ (order / 2) := by
    by_cases hnonempty : Nonempty {sites : Good // parent sites = pattern}
    · let witness := Classical.choice hnonempty
      have hwitness : predecessorPattern witness.val.val = pattern := witness.property
      have hrootsCount : Fintype.card (PatternRoots pattern) ≤ order / 2 := by
        rw [← hwitness]
        exact noIsolated_roots_card witness.val.val witness.val.property
      let rootPositions : {sites : Good // parent sites = pattern} →
          (PatternRoots pattern → Fin body) := fun sites root => sites.val.val root.val
      have hinjective : Function.Injective rootPositions := by
        intro first second hequal
        apply Subtype.ext
        apply Subtype.ext
        have hfirst : predecessorPattern first.val.val = pattern := first.property
        have hsecond : predecessorPattern second.val.val = pattern := second.property
        apply embedding_eq_of_pattern_roots hbody hproper first.val.val second.val.val
          (hfirst.trans hsecond.symm)
        intro slot hroot
        have hpatternRoot : pattern slot = none := by rw [← hfirst]; exact hroot
        exact congrFun hequal ⟨slot, hpatternRoot⟩
      have hcount := Fintype.card_le_of_injective rootPositions hinjective
      rw [Fintype.card_fun, Fintype.card_fin] at hcount
      exact hcount.trans (pow_le_pow_right₀ (by omega : 1 ≤ body) hrootsCount)
    · haveI : IsEmpty {sites : Good // parent sites = pattern} := not_nonempty_iff.mp hnonempty
      simp
  have hdecompose : Fintype.card Good =
      ∑ pattern : Patterns, Fintype.card {sites : Good // parent sites = pattern} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv parent)).symm
  change Fintype.card Good ≤ _
  rw [hdecompose]
  calc
    _ ≤ ∑ _pattern : Patterns, body ^ (order / 2) :=
      Finset.sum_le_sum (fun pattern _ => hfiber pattern)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Patterns, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Nat.cast_id]

/-- Exact finite uniform normalization for the no-isolated event. -/
theorem selectionLaw_noIsolated_mass (body order : ℕ) (horder : order ≤ body) :
    (selectionLaw body order horder).eventMass NoIsolated =
      (Fintype.card {sites : Selection body order // NoIsolated sites} : ℝ) /
        (body.descFactorial order : ℝ) := by
  change (∑ sites : Selection body order, if NoIsolated sites then
    (Fintype.card (Selection body order) : ℝ)⁻¹ else 0) = _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, selection_card]
  rfl

/-- Uniformly selected distinct roots have the full fixed-order rare-event
exponent. Its constant depends only on the selected order. -/
theorem selectionLaw_noIsolated_probability (body order : ℕ) (horder : 1 ≤ order)
    (hbody : 2 * order ≤ body) :
    (selectionLaw body order (by omega)).eventMass NoIsolated ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2) := by
  have hbodyTwo : 2 ≤ body := by omega
  have hproper : order < body := by omega
  have hbodyPositive : (0 : ℝ) < body := by exact_mod_cast (by omega : 0 < body)
  have hcount :
      (Fintype.card {sites : Selection body order // NoIsolated sites} : ℝ) ≤
        ((order + 1 : ℕ) : ℝ) ^ order * (body : ℝ) ^ (order / 2) := by
    exact_mod_cast noIsolated_selection_card_le body order hbodyTwo hproper
  have hfactorLower : (body : ℝ) / 2 ≤ ((body + 1 - order : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : order ≤ body + 1), Nat.cast_add, Nat.cast_one]
    have htwice : 2 * (order : ℝ) ≤ body := by exact_mod_cast hbody
    linarith
  have hdenominatorLower : ((body : ℝ) / 2) ^ order ≤ (body.descFactorial order : ℝ) := by
    apply (pow_le_pow_left₀ (by positivity) hfactorLower order).trans
    exact_mod_cast Nat.pow_sub_le_descFactorial body order
  have hdenominatorPositive : 0 < (body.descFactorial order : ℝ) :=
    lt_of_lt_of_le (pow_pos (by positivity) order) hdenominatorLower
  rw [selectionLaw_noIsolated_mass]
  calc
    _ ≤ (((order + 1 : ℕ) : ℝ) ^ order * (body : ℝ) ^ (order / 2)) /
        ((body : ℝ) / 2) ^ order := by
      exact (div_le_div_of_nonneg_right hcount hdenominatorPositive.le).trans
        (div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) order) hdenominatorLower)
    _ = _ := by
      have hexponents : order / 2 + (order + 1) / 2 = order := by omega
      have hpowers : (body : ℝ) ^ order =
          (body : ℝ) ^ (order / 2) * (body : ℝ) ^ ((order + 1) / 2) := by
        rw [← pow_add, hexponents]
      push_cast
      rw [div_pow, mul_pow, hpowers]
      field_simp [hbodyPositive.ne']

end

end CurrentAFT.CycleSelections

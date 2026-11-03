import CurrentAFT.PathLikelihood
import CurrentAFT.ProtectedCycleResponse

/-!
# Actual distinct body selections

Selections are finite embeddings and are sampled uniformly before the
latent cycle. Fixed selected coordinates retain their genuine joint law.
This file begins the centered-cycle analysis with the exact singleton
identity and actual two-position adjacency counting. The all-order forest
counting and centered-density norm estimates are separate obligations.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

abbrev Selection (body order : ℕ) := Fin order ↪ Fin body

def initialSelection (body order : ℕ) (horder : order ≤ body) : Selection body order where
  toFun index := ⟨index.val, lt_of_lt_of_le index.isLt horder⟩
  inj' _ _ hequal := Fin.ext (congrArg (fun index : Fin body => index.val) hequal)

def selectionLaw (body order : ℕ) (horder : order ≤ body) : FiniteDist (Selection body order) := by
  letI : Nonempty (Selection body order) := ⟨initialSelection body order horder⟩
  exact FiniteDist.uniform (Selection body order)

theorem selection_card (body order : ℕ) :
    Fintype.card (Selection body order) = body.descFactorial order := by
  simp only [Selection, Fintype.card_embedding_eq, Fintype.card_fin]

/-- The selected roots are a deterministic projection of the whole cycle. -/
def selectedLaw {Scalar : Type*} [Fintype Scalar] (body order modulus : ℕ) [NeZero modulus]
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (sites : Selection body order) :
    FiniteDist (Fin order → ZMod modulus) :=
  (ProtectedCycle.cycleLaw body modulus source value).map (fun root slot => root (sites slot))

/-- Uniform distinct placements are sampled independently of the latent cycle. -/
def averagedSelectedLaw {Scalar : Type*} [Fintype Scalar] (body order modulus : ℕ) [NeZero modulus]
    (horder : order ≤ body) (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) :
    FiniteDist (Fin order → ZMod modulus) :=
  (selectionLaw body order horder).mix (selectedLaw body order modulus source value)

/-- Every selected coordinate has the same true two-edge convolution marginal. -/
theorem selectedLaw_coordinate {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) :
    (selectedLaw body order modulus source value sites).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [selectedLaw, FiniteDist.map_map]
  exact ProtectedCycle.cycleLaw_marginal_of_two_le body modulus source value hbody (sites slot)

theorem averagedSelectedLaw_coordinate {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body) (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (slot : Fin order) :
    (averagedSelectedLaw body order modulus horder source value).map (fun root => root slot) =
      ProtectedCycle.differenceLaw source value := by
  rw [averagedSelectedLaw, FiniteDist.map_mix]
  simp_rw [selectedLaw_coordinate body order modulus hbody source value]
  exact FiniteDist.mix_const _ _

/-- The exact singleton likelihood, set to zero outside reference support. -/
def singletonDensity {Color : Type*} [Fintype Color]
    (joint reference : FiniteDist Color) (color : Color) : ℝ :=
  joint.weight color / reference.weight color

/-- Center on reference support and extend by zero outside that support. -/
def centeredSingletonDensity {Color : Type*} [Fintype Color]
    (joint reference : FiniteDist Color) (color : Color) : ℝ :=
  if reference.weight color = 0 then 0 else
    singletonDensity joint reference color -
      ∑ other, reference.weight other * singletonDensity joint reference other

theorem selfDensity_mean_one {Color : Type*} [Fintype Color] (reference : FiniteDist Color) :
    (∑ color, reference.weight color * singletonDensity reference reference color) = 1 := by
  convert reference.sum_one using 1
  apply Finset.sum_congr rfl
  intro color _
  unfold singletonDensity
  by_cases hzero : reference.weight color = 0
  · simp [hzero]
  · rw [div_self hzero, mul_one]

/-- The first centered cycle likelihood is exactly zero on its specified
support, including the chosen zero extension. This uses the proved marginal. -/
theorem centered_selected_singleton_zero {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body 1) (color : ZMod modulus) :
    centeredSingletonDensity
      ((selectedLaw body 1 modulus source value sites).map (fun root => root 0))
      (ProtectedCycle.differenceLaw source value) color = 0 := by
  rw [selectedLaw_coordinate body 1 modulus hbody source value sites 0]
  unfold centeredSingletonDensity
  rw [selfDensity_mean_one]
  split_ifs with hzero
  · rfl
  · simp [singletonDensity, hzero]

/-- The singleton identity also holds under actual uniform distinct placement. -/
theorem centered_averaged_singleton_zero {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (color : ZMod modulus) :
    centeredSingletonDensity
      ((averagedSelectedLaw body 1 modulus (by omega) source value).map (fun root => root 0))
      (ProtectedCycle.differenceLaw source value) color = 0 := by
  rw [averagedSelectedLaw_coordinate body 1 modulus (by omega) hbody source value 0]
  unfold centeredSingletonDensity
  rw [selfDensity_mean_one]
  split_ifs with hzero
  · rfl
  · simp [singletonDensity, hzero]

/-- Cycle adjacency in the underlying body, before random placement. -/
def Adjacent (body : ℕ) (first second : Fin body) : Prop :=
  second = finRotate body first ∨ first = finRotate body second

/-- A selected site is isolated among the selected vertices. -/
def Isolated {body order : ℕ} (sites : Selection body order) (slot : Fin order) : Prop :=
  ∀ other, other ≠ slot → ¬Adjacent body (sites slot) (sites other)

/-- The two latent edges used by a body root. -/
def latentSupport {body : ℕ} (vertex : Fin body) : Finset (Fin body) :=
  {vertex, (finRotate body).symm vertex}

/-- Isolated selected roots share no latent scalar with any other selected root. -/
theorem isolated_latentSupport_disjoint {body order : ℕ}
    (sites : Selection body order) (slot other : Fin order) (hne : other ≠ slot)
    (hisolated : Isolated sites slot) :
    Disjoint (latentSupport (sites slot)) (latentSupport (sites other)) := by
  have hsites : sites other ≠ sites slot := fun h => hne (sites.injective h)
  have hnotAdjacent := hisolated other hne
  apply Finset.disjoint_left.mpr
  intro vertex hfirst hsecond
  simp only [latentSupport, Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact hsites (hsecond.symm.trans hfirst)
  · apply hnotAdjacent
    left
    have h := congrArg (finRotate body) (hfirst.symm.trans hsecond)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · apply hnotAdjacent
    right
    have h := congrArg (finRotate body) (hsecond.symm.trans hfirst)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · apply hsites
    exact (finRotate body).symm.injective (hsecond.symm.trans hfirst)

/-- Changing the two latent edges of an isolated selected root leaves all
other selected roots unchanged. This preserves their full joint dependence. -/
theorem isolated_other_roots_unchanged {Group : Type*} [AddCommGroup Group]
    {body order : ℕ} (sites : Selection body order) (slot other : Fin order) (hne : other ≠ slot)
    (hisolated : Isolated sites slot) (first second : Fin body → Group)
    (hagree : ∀ vertex ∉ latentSupport (sites slot), first vertex = second vertex) :
    PublicCharge.cycleDifference first (sites other) =
      PublicCharge.cycleDifference second (sites other) := by
  have hdisjoint := isolated_latentSupport_disjoint sites slot other hne hisolated
  have hsite : sites other ∉ latentSupport (sites slot) := by
    intro hmem
    exact Finset.disjoint_left.mp hdisjoint hmem (by simp [latentSupport])
  have hprevious : (finRotate body).symm (sites other) ∉ latentSupport (sites slot) := by
    intro hmem
    exact Finset.disjoint_left.mp hdisjoint hmem (by simp [latentSupport])
  simp only [PublicCharge.cycleDifference, hagree _ hsite, hagree _ hprevious]

/-- Actual ordered distinct body positions for two labeled selections. -/
abbrev DistinctPair (body : ℕ) := {pair : Fin body × Fin body // pair.1 ≠ pair.2}

def pairSelectionEquiv (body : ℕ) : Selection body 2 ≃ DistinctPair body where
  toFun sites := ⟨(sites 0, sites 1), by
    intro h
    have hindices := sites.injective h
    exact (by decide : (0 : Fin 2) ≠ 1) hindices⟩
  invFun pair :=
    { toFun := ![pair.val.1, pair.val.2]
      inj' := by
        intro first second hequal
        fin_cases first <;> fin_cases second
        · rfl
        · exact False.elim (pair.property (by simpa using hequal))
        · exact False.elim (pair.property (by simpa using hequal.symm))
        · rfl }
  left_inv sites := by ext index; fin_cases index <;> rfl
  right_inv pair := by apply Subtype.ext; rfl

theorem distinctPair_card (body : ℕ) : Fintype.card (DistinctPair body) = body * (body - 1) := by
  rw [← Fintype.card_congr (pairSelectionEquiv body), selection_card]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
  ring

theorem cycle_next_ne (body : ℕ) (hbody : 2 ≤ body) (vertex : Fin body) :
    finRotate body vertex ≠ vertex := by
  intro hfixed
  apply ProtectedCycle.cycle_predecessor_ne body hbody vertex
  apply (finRotate body).injective
  simp only [Equiv.apply_symm_apply]
  exact hfixed.symm

/-- Every ordered forward-adjacent pair is uniquely determined by its first site. -/
def forwardPairEquiv (body : ℕ) (hbody : 2 ≤ body) : Fin body ≃
    {pair : DistinctPair body // pair.val.2 = finRotate body pair.val.1} where
  toFun vertex := ⟨⟨(vertex, finRotate body vertex), (cycle_next_ne body hbody vertex).symm⟩, rfl⟩
  invFun pair := pair.val.val.1
  left_inv vertex := rfl
  right_inv pair := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl pair.property.symm

/-- Every ordered backward-adjacent pair is uniquely determined by its second site. -/
def backwardPairEquiv (body : ℕ) (hbody : 2 ≤ body) : Fin body ≃
    {pair : DistinctPair body // pair.val.1 = finRotate body pair.val.2} where
  toFun vertex := ⟨⟨(finRotate body vertex, vertex), cycle_next_ne body hbody vertex⟩, rfl⟩
  invFun pair := pair.val.val.2
  left_inv vertex := rfl
  right_inv pair := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext pair.property.symm rfl

/-- Both cyclic orientations are counted. In the two-vertex case they
coincide, and the union bound remains valid. -/
theorem adjacentPair_card_le (body : ℕ) (hbody : 2 ≤ body) :
    Fintype.card {pair : DistinctPair body // Adjacent body pair.val.1 pair.val.2} ≤ 2 * body := by
  have hforward : Fintype.card
      {pair : DistinctPair body // pair.val.2 = finRotate body pair.val.1} = body := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (forwardPairEquiv body hbody)).symm
  have hbackward : Fintype.card
      {pair : DistinctPair body // pair.val.1 = finRotate body pair.val.2} = body := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (backwardPairEquiv body hbody)).symm
  rw [Fintype.card_subtype]
  have hunion : (Finset.univ.filter (fun pair : DistinctPair body =>
      Adjacent body pair.val.1 pair.val.2)) =
      (Finset.univ.filter (fun pair : DistinctPair body => pair.val.2 = finRotate body pair.val.1)) ∪
        (Finset.univ.filter (fun pair : DistinctPair body => pair.val.1 = finRotate body pair.val.2)) := by
    ext pair
    simp [Adjacent]
  rw [hunion]
  apply (Finset.card_union_le _ _).trans
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, hforward, hbackward]
  omega

/-- The finite uniform two-position law is the embedding law reindexed by
its two actual body positions. -/
def pairLaw (body : ℕ) (hbody : 2 ≤ body) : FiniteDist (DistinctPair body) :=
  (selectionLaw body 2 hbody).map (pairSelectionEquiv body)

theorem pairLaw_uniform_weight (body : ℕ) (hbody : 2 ≤ body) (pair : DistinctPair body) :
    (pairLaw body hbody).weight pair = (Fintype.card (DistinctPair body) : ℝ)⁻¹ := by
  rw [pairLaw, FiniteDist.map_equiv_weight]
  change (Fintype.card (Selection body 2) : ℝ)⁻¹ = _
  rw [Fintype.card_congr (pairSelectionEquiv body)]

/-- The actual adjacency probability pays only `O(1/body)` under uniform
distinct labeled placement. The full uniform-law denominator is explicit. -/
theorem pairLaw_adjacency_le (body : ℕ) (hbody : 2 ≤ body) :
    (pairLaw body hbody).eventMass (fun pair => Adjacent body pair.val.1 pair.val.2) ≤
      4 / (body : ℝ) := by
  have hbodypos : (0 : ℝ) < body := by exact_mod_cast (by omega : 0 < body)
  have hpredpos : (0 : ℝ) < (body : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ body := by exact_mod_cast hbody
    linarith
  have hcount :
      (Fintype.card {pair : DistinctPair body // Adjacent body pair.val.1 pair.val.2} : ℝ) ≤
        2 * body := by exact_mod_cast adjacentPair_card_le body hbody
  have hmass :
      (pairLaw body hbody).eventMass (fun pair => Adjacent body pair.val.1 pair.val.2) =
      (Fintype.card {pair : DistinctPair body // Adjacent body pair.val.1 pair.val.2} : ℝ) /
        ((body : ℝ) * ((body : ℝ) - 1)) := by
    unfold FiniteDist.eventMass
    simp only [pairLaw_uniform_weight]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
      distinctPair_card, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ body), Nat.cast_one]
    rfl
  rw [hmass]
  calc
    _ ≤ (2 * (body : ℝ)) / ((body : ℝ) * ((body : ℝ) - 1)) :=
      div_le_div_of_nonneg_right hcount (mul_nonneg hbodypos.le hpredpos.le)
    _ = 2 / ((body : ℝ) - 1) := by field_simp
    _ ≤ 4 / (body : ℝ) := by
      apply (div_le_div_iff₀ hpredpos hbodypos).mpr
      have htwo : (2 : ℝ) ≤ body := by exact_mod_cast hbody
      nlinarith

end

end CurrentAFT.CycleSelections

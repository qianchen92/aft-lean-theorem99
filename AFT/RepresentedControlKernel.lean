import AFT.RepresentedPolynomial
import AFT.CanonicalTensor

/-! # Literal finite seed monomials as disjoint joint input kernels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- Every seed occurrence has its own distinct input coordinates. -/
def ControlProductSlot : List (InputSeed Color) → Type
  | [] => PEmpty
  | seed :: rest => Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest

instance controlProductSlotFintype (seeds : List (InputSeed Color)) : Fintype (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (Fintype PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))

instance controlProductSlotDecEq (seeds : List (InputSeed Color)) : DecidableEq (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (DecidableEq PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))

def controlProductKernel : (seeds : List (InputSeed Color)) → (ControlProductSlot seeds → Color) → ℝ
  | [], _ => 1
  | seed :: rest, word => MixedKernel.tensor seed.kernel (controlProductKernel rest) word

def controlProductReference (primary body : FiniteDist Color) :
    (seeds : List (InputSeed Color)) → ControlProductSlot seeds → FiniteDist Color
  | [], slot => PEmpty.elim slot
  | seed :: rest, slot => Sum.elim (inputReference primary body seed) (controlProductReference primary body rest) slot

def controlProductRate (primaryPool bodyPool : ℝ) :
    (seeds : List (InputSeed Color)) → ControlProductSlot seeds → ℝ
  | [], slot => PEmpty.elim slot
  | seed :: rest, slot => Sum.elim (inputRate primaryPool bodyPool seed) (controlProductRate primaryPool bodyPool rest) slot

def controlProductBodyOrder (seeds : List (InputSeed Color)) : ℕ := (seeds.map InputSeed.bodyOrder).sum

def controlProductActivity (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seeds : List (InputSeed Color)) : ℝ :=
  radius ^ controlProductBodyOrder seeds *
    MixedKernel.activity (controlProductRate primaryPool bodyPool seeds)
      (controlProductReference primary body seeds) (controlProductKernel seeds)

omit [Fintype Color] in
theorem controlProductRate_nonneg (primaryPool bodyPool : ℝ) (seeds : List (InputSeed Color))
    (slot : ControlProductSlot seeds) : 0 ≤ controlProductRate primaryPool bodyPool seeds slot := by
  induction seeds with
  | nil => exact PEmpty.elim slot
  | cons seed rest ih =>
    cases slot with
    | inr slot => exact ih slot
    | inl slot =>
      change 0 ≤ inputRate primaryPool bodyPool seed slot
      unfold inputRate
      cases slot using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right]
      all_goals exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- No coordinate of a canonical seed is reused in a disjoint monomial;
the full joint input therefore remains genuinely canonical. -/
theorem controlProductKernel_canonical (primary body : FiniteDist Color) (seeds : List (InputSeed Color))
    (hc : ∀ seed ∈ seeds, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (controlProductReference primary body seeds) Finset.univ (controlProductKernel seeds) := by
  induction seeds with
  | nil =>
    constructor
    · intro x y h; rfl
    · intro slot; exact PEmpty.elim slot
  | cons seed rest ih =>
    exact MixedKernel.tensor_canonical _ _ _ _ (hc seed (List.mem_cons_self ..))
      (ih (fun other hother => hc other (List.mem_cons_of_mem _ hother)))

/-- The exact disjoint tensor kernel costs at most the product of the
actual seed activities, retaining every fixed-coordinate fiber. -/
theorem controlProductActivity_le (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 0 ≤ radius) (seeds : List (InputSeed Color)) :
    controlProductActivity primary body primaryPool bodyPool radius seeds ≤
      (seeds.map (inputWeight primary body primaryPool bodyPool radius)).prod := by
  induction seeds with
  | nil =>
    simp [controlProductActivity, controlProductBodyOrder, MixedKernel.activity, MixedKernel.fiberNorm,
      MixedKernel.fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.independent,
      controlProductKernel, controlProductReference, controlProductRate, ControlProductSlot]
    rw [show (default : Finset PEmpty) = ∅ from Subsingleton.elim _ _]
    simp
  | cons seed rest ih =>
    have ht := MixedKernel.activity_tensor_le
      (inputRate primaryPool bodyPool seed) (controlProductRate primaryPool bodyPool rest)
      (inputReference primary body seed) (controlProductReference primary body rest)
      seed.kernel (controlProductKernel rest)
      (fun slot => by
        unfold inputRate
        cases slot using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right]
        all_goals exact inv_nonneg.mpr (Real.sqrt_nonneg _))
      (controlProductRate_nonneg primaryPool bodyPool rest)
    calc
      _ ≤ inputWeight primary body primaryPool bodyPool radius seed *
          controlProductActivity primary body primaryPool bodyPool radius rest := by
        have hh := mul_le_mul_of_nonneg_left ht (pow_nonneg hradius (seed.bodyOrder + controlProductBodyOrder rest))
        simpa only [controlProductActivity, controlProductBodyOrder, List.map_cons, List.sum_cons,
          controlProductRate, controlProductReference, controlProductKernel,
          inputWeight, MixedKernel.analyticActivity, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ _ := by
        simpa only [List.map_cons, List.prod_cons] using
          mul_le_mul_of_nonneg_left ih (inputWeight_nonneg _ _ _ _ _ _ hradius)

/-- Literal seed occurrences in a formal monomial; repeated labels remain
distinct copies rather than being identified by their output images. -/
def monomialOccurrences (powers : InputSeed Color →₀ ℕ) : List (InputSeed Color) :=
  powers.support.toList.flatMap (fun seed => List.replicate (powers seed) seed)

omit [Fintype Color] in
theorem monomialOccurrences_weight (weight : InputSeed Color → ℝ) (powers : InputSeed Color →₀ ℕ) :
    ((monomialOccurrences powers).map weight).prod = monomialWeight weight powers := by
  unfold monomialOccurrences monomialWeight Finsupp.prod
  rw [List.map_flatMap]
  have hh (seeds : List (InputSeed Color)) :
      ((seeds.flatMap fun seed => List.replicate (powers seed) (weight seed)).prod) =
        (seeds.map fun seed => weight seed ^ powers seed).prod := by
    induction seeds with
    | nil => simp
    | cons seed seeds ih => simp [List.flatMap_cons, ih]
  simpa using hh powers.support.toList

theorem monomial_control_activity_le (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 0 ≤ radius) (powers : InputSeed Color →₀ ℕ) :
    controlProductActivity primary body primaryPool bodyPool radius (monomialOccurrences powers) ≤
      monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers := by
  exact (controlProductActivity_le _ _ _ _ _ hradius _).trans_eq (monomialOccurrences_weight _ _)

omit [Fintype Color] in
theorem mem_monomialOccurrences_support (powers : InputSeed Color →₀ ℕ) (seed : InputSeed Color)
    (h : seed ∈ monomialOccurrences powers) : seed ∈ powers.support := by
  obtain ⟨other, hother, hseed⟩ := List.mem_flatMap.mp h
  have heq : seed = other := (List.mem_replicate.mp hseed).2
  subst seed
  exact Finset.mem_toList.mp hother

/-- Actual canonicality of every formal monomial follows from the exact
canonicality of its constituent input seeds. -/
theorem monomial_control_canonical (primary body : FiniteDist Color) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support,
      Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (controlProductReference primary body (monomialOccurrences powers)) Finset.univ
      (controlProductKernel (monomialOccurrences powers)) :=
  controlProductKernel_canonical primary body _ (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))

/-- The explicit expanded joint-kernel representation, measured before
physical output and without identifying equal output images. -/
def representedControlActivity (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (table : Table (InputSeed Color)) : ℝ :=
  table.sum fun powers coefficient => |coefficient| *
    controlProductActivity primary body primaryPool bodyPool radius (monomialOccurrences powers)

/-- The formal weighted coefficient norm bounds the actual finite family
of disjoint joint kernels, including all their mixed fixed fibers. -/
theorem representedControlActivity_le (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 0 ≤ radius) (table : Table (InputSeed Color)) :
    representedControlActivity primary body primaryPool bodyPool radius table ≤
      activity (inputWeight primary body primaryPool bodyPool radius) table := by
  unfold representedControlActivity activity Finsupp.sum
  apply Finset.sum_le_sum
  intro powers _
  exact mul_le_mul_of_nonneg_left (monomial_control_activity_le _ _ _ _ _ hradius powers) (abs_nonneg _)

end
end AFT.RepresentedPolynomial

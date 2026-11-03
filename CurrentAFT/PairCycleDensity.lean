import CurrentAFT.CenteredCycleDensity
import CurrentAFT.RareMixture
import CurrentAFT.ChargedEndpoint

/-!
# A genuine two-root likelihood bound

Any finite coupling of a reference law with itself has likelihood energy
at most the number of reference-support atoms. This gives a stronger
second-order bound than the length-two path estimate, while higher orders
still require the path and forest analysis.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

/-- Positive reference support, counted before any norm bound. -/
def referenceSupport (reference : FiniteDist Color) : Finset Color :=
  Finset.univ.filter (fun color => 0 < reference.weight color)

def pairLikelihoodEnergy (joint : FiniteDist (Color × Color)) (reference : FiniteDist Color) : ℝ :=
  ∑ first, ∑ second, joint.weight (first, second) ^ 2 /
    (reference.weight first * reference.weight second)

theorem pair_marginal_sums (joint : FiniteDist (Color × Color)) (reference : FiniteDist Color)
    (hfirst : joint.map Prod.fst = reference) (hsecond : joint.map Prod.snd = reference) :
    (∀ first, (∑ second, joint.weight (first, second)) = reference.weight first) ∧
      (∀ second, (∑ first, joint.weight (first, second)) = reference.weight second) := by
  constructor
  · intro first
    have h := congrArg (fun law : FiniteDist Color => law.weight first) hfirst
    simp only [FiniteDist.map_weight, Fintype.sum_prod_type] at h
    rw [Finset.sum_comm] at h
    simpa only [FiniteDist.map_weight, Fintype.sum_prod_type, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using h
  · intro second
    have h := congrArg (fun law : FiniteDist Color => law.weight second) hsecond
    simpa only [FiniteDist.map_weight, Fintype.sum_prod_type, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using h

theorem pair_atom_le_references (joint : FiniteDist (Color × Color)) (reference : FiniteDist Color)
    (hfirst : joint.map Prod.fst = reference) (hsecond : joint.map Prod.snd = reference)
    (first second : Color) :
    joint.weight (first, second) ≤ reference.weight first ∧
      joint.weight (first, second) ≤ reference.weight second := by
  obtain ⟨hrows, hcolumns⟩ := pair_marginal_sums joint reference hfirst hsecond
  constructor
  · rw [← hrows first]
    exact Finset.single_le_sum (fun color _ => joint.nonneg (first, color)) (Finset.mem_univ second)
  · rw [← hcolumns second]
    exact Finset.single_le_sum (fun color _ => joint.nonneg (color, second)) (Finset.mem_univ first)

/-- The second-order coupling energy is bounded without a smallest-atom
loss. Zero reference atoms contribute zero and need no inverse bound. -/
theorem pairLikelihoodEnergy_le_support (joint : FiniteDist (Color × Color))
    (reference : FiniteDist Color) (hfirst : joint.map Prod.fst = reference)
    (hsecond : joint.map Prod.snd = reference) :
    pairLikelihoodEnergy joint reference ≤ (referenceSupport reference).card := by
  obtain ⟨hrows, _⟩ := pair_marginal_sums joint reference hfirst hsecond
  have hrow (first : Color) :
      (∑ second, joint.weight (first, second) ^ 2 /
        (reference.weight first * reference.weight second)) ≤
          if 0 < reference.weight first then 1 else 0 := by
    by_cases hpositive : 0 < reference.weight first
    · rw [if_pos hpositive]
      calc
        _ ≤ ∑ second, joint.weight (first, second) / reference.weight first := by
          apply Finset.sum_le_sum
          intro second _
          by_cases hzero : reference.weight second = 0
          · simp only [hzero, mul_zero, div_zero]
            exact div_nonneg (joint.nonneg _) hpositive.le
          · have hsecondPositive : 0 < reference.weight second :=
              lt_of_le_of_ne (reference.nonneg second) (Ne.symm hzero)
            have hatom := (pair_atom_le_references joint reference hfirst hsecond first second).2
            have hsquare : joint.weight (first, second) ^ 2 ≤
                joint.weight (first, second) * reference.weight second := by
              nlinarith [mul_le_mul_of_nonneg_left hatom (joint.nonneg (first, second))]
            calc
              _ ≤ (joint.weight (first, second) * reference.weight second) /
                  (reference.weight first * reference.weight second) :=
                div_le_div_of_nonneg_right hsquare (mul_nonneg hpositive.le hsecondPositive.le)
              _ = _ := by field_simp
        _ = 1 := by rw [← Finset.sum_div, hrows first, div_self hpositive.ne']
    · have hzero : reference.weight first = 0 := le_antisymm (le_of_not_gt hpositive) (reference.nonneg first)
      simp [hzero]
  unfold pairLikelihoodEnergy
  calc
    _ ≤ ∑ first, if 0 < reference.weight first then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun first _ => hrow first)
    _ = (referenceSupport reference).card := by
      simp only [referenceSupport, Finset.card_filter]
      push_cast
      rfl

/-- Pair form of the full centered-density atom formula. -/
def pairCenteredDensity (joint : FiniteDist (Color × Color)) (reference : FiniteDist Color)
    (output : Color × Color) : ℝ :=
  joint.expectation (fun input => centeredRootAtom reference input.1 output.1 *
    centeredRootAtom reference input.2 output.2)

/-- Both exact marginals remove the two first-order components. -/
theorem pairCenteredDensity_formula (joint : FiniteDist (Color × Color))
    (reference : FiniteDist Color) (hfirst : joint.map Prod.fst = reference)
    (hsecond : joint.map Prod.snd = reference) (output : Color × Color)
    (houtputFirst : reference.weight output.1 ≠ 0) (houtputSecond : reference.weight output.2 ≠ 0) :
    pairCenteredDensity joint reference output =
      joint.weight output / (reference.weight output.1 * reference.weight output.2) - 1 := by
  obtain ⟨hrows, hcolumns⟩ := pair_marginal_sums joint reference hfirst hsecond
  have hdeltaFirst :
      (∑ input, joint.weight input * (if input.1 = output.1 then (1 : ℝ) else 0)) =
        reference.weight output.1 := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hrows _
  have hdeltaSecond :
      (∑ input, joint.weight input * (if input.2 = output.2 then (1 : ℝ) else 0)) =
        reference.weight output.2 := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hcolumns _
  have hdeltaPair :
      (∑ input, joint.weight input * (if input.1 = output.1 then (1 : ℝ) else 0) *
        (if input.2 = output.2 then (1 : ℝ) else 0)) = joint.weight output := by
    rcases output with ⟨first, second⟩
    simp [Fintype.sum_prod_type, mul_ite]
  have hpoint (input : Color × Color) :
      joint.weight input * (centeredRootAtom reference input.1 output.1 *
        centeredRootAtom reference input.2 output.2) =
      (joint.weight input * (if input.1 = output.1 then 1 else 0) *
        (if input.2 = output.2 then 1 else 0)) /
          (reference.weight output.1 * reference.weight output.2) -
      (joint.weight input * (if input.1 = output.1 then 1 else 0)) / reference.weight output.1 -
      (joint.weight input * (if input.2 = output.2 then 1 else 0)) / reference.weight output.2 +
        joint.weight input := by
    unfold centeredRootAtom
    field_simp
    ring
  unfold pairCenteredDensity FiniteDist.expectation
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div,
    hdeltaPair, hdeltaFirst, hdeltaSecond, joint.sum_one,
    div_self houtputFirst, div_self houtputSecond]
  ring

def pairCenteredEnergy (joint : FiniteDist (Color × Color)) (reference : FiniteDist Color) : ℝ :=
  (reference.prod reference).l2Sq (pairCenteredDensity joint reference)

/-- In second order the centering contraction is exact: its energy is the
full likelihood energy minus the constant component one. -/
theorem pairCenteredEnergy_eq (joint : FiniteDist (Color × Color))
    (reference : FiniteDist Color) (hfirst : joint.map Prod.fst = reference)
    (hsecond : joint.map Prod.snd = reference) :
    pairCenteredEnergy joint reference = pairLikelihoodEnergy joint reference - 1 := by
  have hpoint (output : Color × Color) :
      (reference.prod reference).weight output * pairCenteredDensity joint reference output ^ 2 =
      joint.weight output ^ 2 / (reference.prod reference).weight output -
        2 * joint.weight output + (reference.prod reference).weight output := by
    by_cases hzero : (reference.prod reference).weight output = 0
    · have hjointZero : joint.weight output = 0 := by
        have hb := pair_atom_le_references joint reference hfirst hsecond output.1 output.2
        change reference.weight output.1 * reference.weight output.2 = 0 at hzero
        rcases mul_eq_zero.mp hzero with h | h <;>
          nlinarith [joint.nonneg output]
      rw [hzero, hjointZero]
      norm_num
    · have hfirstNonzero : reference.weight output.1 ≠ 0 := fun h =>
        hzero (by simp [FiniteDist.prod_weight, h])
      have hsecondNonzero : reference.weight output.2 ≠ 0 := fun h =>
        hzero (by simp [FiniteDist.prod_weight, h])
      rw [pairCenteredDensity_formula joint reference hfirst hsecond output hfirstNonzero hsecondNonzero]
      simp only [FiniteDist.prod_weight]
      field_simp
      ring
  unfold pairCenteredEnergy FiniteDist.l2Sq FiniteDist.expectation
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, joint.sum_one,
    FiniteDist.sum_one]
  unfold pairLikelihoodEnergy
  rw [Fintype.sum_prod_type]
  simp only [FiniteDist.prod_weight]
  ring

theorem pairCenteredEnergy_le_support (joint : FiniteDist (Color × Color))
    (reference : FiniteDist Color) (hfirst : joint.map Prod.fst = reference)
    (hsecond : joint.map Prod.snd = reference) :
    pairCenteredEnergy joint reference ≤ (referenceSupport reference).card := by
  rw [pairCenteredEnergy_eq joint reference hfirst hsecond]
  linarith [pairLikelihoodEnergy_le_support joint reference hfirst hsecond]

/-- Coordinates and ordered pairs are exactly equivalent in second order. -/
def pairVectorEquiv : (Color × Color) ≃ (Fin 2 → Color) where
  toFun pair := ![pair.1, pair.2]
  invFun vector := (vector 0, vector 1)
  left_inv pair := rfl
  right_inv vector := by ext index; fin_cases index <;> rfl

def pairOfVectorLaw (joint : FiniteDist (Fin 2 → Color)) : FiniteDist (Color × Color) :=
  joint.map pairVectorEquiv.symm

theorem vectorReference_eq_pair_map (reference : FiniteDist Color) :
    FiniteDist.independent (fun _ : Fin 2 => reference) =
      (reference.prod reference).map pairVectorEquiv := by
  ext vector
  rw [FiniteDist.map_equiv_weight]
  change (∏ index : Fin 2, reference.weight (vector index)) =
    reference.weight (vector 0) * reference.weight (vector 1)
  exact Fin.prod_univ_two _

/-- The new centered-atom convention is exactly the two-coordinate
centering formula already analyzed above. -/
theorem centeredRootDensity_pair (joint : FiniteDist (Fin 2 → Color))
    (reference : FiniteDist Color) (output : Fin 2 → Color) :
    centeredRootDensity joint (fun _ => reference) output =
      pairCenteredDensity (pairOfVectorLaw joint) reference (output 0, output 1) := by
  unfold centeredRootDensity pairCenteredDensity pairOfVectorLaw
  rw [FiniteDist.expectation_map]
  apply congrArg joint.expectation
  funext input
  simp only [Fin.prod_univ_two, Function.comp_apply]
  rfl

theorem centeredRootDensity_pair_energy (joint : FiniteDist (Fin 2 → Color))
    (reference : FiniteDist Color) :
    (FiniteDist.independent (fun _ : Fin 2 => reference)).l2Sq
      (centeredRootDensity joint (fun _ => reference)) =
        pairCenteredEnergy (pairOfVectorLaw joint) reference := by
  rw [vectorReference_eq_pair_map, FiniteDist.l2Sq_map]
  unfold pairCenteredEnergy
  apply congrArg (reference.prod reference).l2Sq
  funext output
  rw [Function.comp_apply, centeredRootDensity_pair]
  rfl

/-- Actual residue root reference from the protected finite Gaussian. -/
def gaussianRootReference (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    FiniteDist (ZMod modulus) :=
  ProtectedCycle.differenceLaw (GaussianSource.windowGaussian width cutoff)
    (fun scalar => ((scalar : ℤ) : ZMod modulus))

/-- Reducing integer differences modulo the modulus cannot create more
support atoms than the actual integer difference interval. -/
theorem gaussianRootReference_support_card (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    (referenceSupport (gaussianRootReference width cutoff modulus)).card ≤ 4 * cutoff + 1 := by
  let possible := Finset.univ.image
    (fun difference : GaussianSource.Window (2 * cutoff) => ((difference : ℤ) : ZMod modulus))
  have hsubset : referenceSupport (gaussianRootReference width cutoff modulus) ⊆ possible := by
    intro color hcolor
    by_contra hnot
    have hzero : (gaussianRootReference width cutoff modulus).weight color = 0 := by
      unfold gaussianRootReference ProtectedCycle.differenceLaw
      simp only [FiniteDist.map_weight, Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro first _
      apply Finset.sum_eq_zero
      intro second _
      have hne : ((first : ℤ) : ZMod modulus) - ((second : ℤ) : ZMod modulus) ≠ color := by
        intro hequal
        apply hnot
        change color ∈ Finset.univ.image
          (fun difference : GaussianSource.Window (2 * cutoff) => ((difference : ℤ) : ZMod modulus))
        refine Finset.mem_image.mpr ⟨PathLikelihood.windowDifference cutoff second first, Finset.mem_univ _, ?_⟩
        simpa only [PathLikelihood.windowDifference_val, Int.cast_sub] using hequal
      simp [hne]
    have hpositive := (Finset.mem_filter.mp hcolor).2
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  calc
    _ ≤ possible.card := Finset.card_le_card hsubset
    _ ≤ Fintype.card (GaussianSource.Window (2 * cutoff)) := by
      exact (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := PathLikelihood.windowDifference_card cutoff

/-- A concrete two-root conditional law has the complete centered L2 bound,
with its real zero atoms and actual window-Gaussian reference. -/
theorem selected_two_centered_energy_le (body modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (hbody : 2 ≤ body) (sites : Selection body 2) :
    (FiniteDist.independent (fun _ : Fin 2 => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (selectedLaw body 2 modulus (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites)
        (fun _ => gaussianRootReference width cutoff modulus)) ≤ (4 * cutoff + 1 : ℕ) := by
  rw [centeredRootDensity_pair_energy]
  let joint := selectedLaw body 2 modulus (GaussianSource.windowGaussian width cutoff)
    (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites
  have hfirst : (pairOfVectorLaw joint).map Prod.fst = gaussianRootReference width cutoff modulus := by
    rw [pairOfVectorLaw, FiniteDist.map_map]
    exact selectedLaw_coordinate body 2 modulus hbody _ _ sites 0
  have hsecond : (pairOfVectorLaw joint).map Prod.snd = gaussianRootReference width cutoff modulus := by
    rw [pairOfVectorLaw, FiniteDist.map_map]
    exact selectedLaw_coordinate body 2 modulus hbody _ _ sites 1
  apply (pairCenteredEnergy_le_support (pairOfVectorLaw joint) _ hfirst hsecond).trans
  exact_mod_cast gaussianRootReference_support_card width cutoff modulus

/-- Full centered-density coefficients are linear in the actual joint law. -/
theorem centeredRootDensity_mix {Choice Index Color : Type*}
    [Fintype Choice] [Fintype Index] [DecidableEq Index] [Fintype Color]
    (law : FiniteDist Choice) (channel : Choice → FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (output : Index → Color) :
    centeredRootDensity (law.mix channel) reference output =
      law.expectation (fun choice => centeredRootDensity (channel choice) reference output) := by
  unfold centeredRootDensity FiniteDist.expectation
  simp only [FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  apply Finset.sum_congr rfl
  intro input _
  ring

/-- The adjacency event for the literal uniform embedding law. -/
theorem selectionLaw_two_adjacency_le (body : ℕ) (hbody : 2 ≤ body) :
    (selectionLaw body 2 hbody).eventMass
      (fun sites => Adjacent body (sites 0) (sites 1)) ≤ 4 / (body : ℝ) := by
  have h := pairLaw_adjacency_le body hbody
  rw [pairLaw, CurrentAFT.eventMass_map] at h
  exact h

/-- Complete genuine second-order centered-root estimate. It uses the
actual Gaussian-window root reference, actual uniform distinct placements,
all their zero atoms, and the full joint law for every conditional cycle.
The rare-event multiplier is `4/body`, not its square root. -/
theorem averaged_two_centered_norm_le (body modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (hbody : 2 ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin 2 => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body 2 modulus hbody (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      4 * ((4 * cutoff + 1 : ℕ) : ℝ) / (body : ℝ) := by
  let rootReference := gaussianRootReference width cutoff modulus
  let reference := FiniteDist.independent (fun _ : Fin 2 => rootReference)
  let placements := selectionLaw body 2 hbody
  let event := fun sites : Selection body 2 => Adjacent body (sites 0) (sites 1)
  let coefficient := fun (sites : Selection body 2) (output : Fin 2 → ZMod modulus) =>
    centeredRootDensity
      (selectedLaw body 2 modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites)
      (fun _ => rootReference) output
  let bound : ℝ := ((4 * cutoff + 1 : ℕ) : ℝ)
  have hboundNonneg : 0 ≤ bound := by positivity
  have hboundOne : 1 ≤ bound := by dsimp [bound]; exact_mod_cast (by omega : 1 ≤ 4 * cutoff + 1)
  have henergy (sites : Selection body 2) : reference.l2Sq (coefficient sites) ≤ bound ^ 2 := by
    have h := selected_two_centered_energy_le body modulus cutoff width hbody sites
    change reference.l2Sq (coefficient sites) ≤ bound at h
    apply h.trans
    nlinarith
  have hzero (sites : Selection body 2) (hnonadjacent : ¬event sites)
      (output : Fin 2 → ZMod modulus) (houtput : reference.weight output ≠ 0) :
      coefficient sites output = 0 := by
    have hfirst : rootReference.weight (output 0) ≠ 0 := by
      intro hfirstZero
      apply houtput
      change (∏ index : Fin 2, rootReference.weight (output index)) = 0
      rw [Fin.prod_univ_two, hfirstZero, zero_mul]
    have hisolated : Isolated sites (0 : Fin 2) := by
      intro other hne
      fin_cases other
      · exact False.elim (hne rfl)
      · exact hnonadjacent
    exact isolated_centeredRootDensity_zero body 2 modulus hbody
      (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites 0 hisolated output hfirst
  have haverage := CurrentAFT.rare_mixture_l2Sq placements reference event coefficient bound hzero henergy
  let average := centeredRootDensity
    (averagedSelectedLaw body 2 modulus hbody (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus)))
    (fun _ => rootReference)
  have havg : average = fun output => placements.expectation (fun sites => coefficient sites output) := by
    funext output
    exact centeredRootDensity_mix placements
      (selectedLaw body 2 modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus))) (fun _ => rootReference) output
  have haverageEnergy : reference.l2Sq average ≤ placements.eventMass event ^ 2 * bound ^ 2 := by
    rw [havg]
    exact haverage
  have hprobability : 0 ≤ placements.eventMass event := placements.eventMass_nonneg event
  have hprobabilityBound : placements.eventMass event ≤ 4 / (body : ℝ) :=
    selectionLaw_two_adjacency_le body hbody
  have hrootSquare := Real.sq_sqrt (reference.l2Sq_nonneg average)
  have hrootNonneg := Real.sqrt_nonneg (reference.l2Sq average)
  have hproductNonneg : 0 ≤ placements.eventMass event * bound :=
    mul_nonneg hprobability hboundNonneg
  have hrootBound : Real.sqrt (reference.l2Sq average) ≤ placements.eventMass event * bound := by
    nlinarith
  change Real.sqrt (reference.l2Sq average) ≤ 4 * bound / (body : ℝ)
  calc
    _ ≤ placements.eventMass event * bound := hrootBound
    _ ≤ (4 / (body : ℝ)) * bound := mul_le_mul_of_nonneg_right hprobabilityBound hboundNonneg
    _ = _ := by ring

end

end CurrentAFT.CycleSelections

import CurrentAFT.CycleSelections

/-!
# Isolated selected cycle roots cancel under centering

The proof splits the actual independent latent edge product into the two
edges used by one isolated root and all remaining edges. Other selected
roots retain their full joint dependence. A centered test at the isolated
root therefore has zero expectation against every joint test of the others.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Assemble selected and complementary latent coordinates. -/
def assemble {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) : Scalar :=
  if h : index ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩

@[simp] theorem assemble_selected {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) (hindex : index ∈ selected) :
    assemble selected chosen rest index = chosen ⟨index, hindex⟩ := by
  simp only [assemble, dif_pos hindex]

@[simp] theorem assemble_rest {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) (hindex : index ∉ selected) :
    assemble selected chosen rest index = rest ⟨index, hindex⟩ := by
  simp only [assemble, dif_neg hindex]

/-- Exact finite Fubini for a coordinate partition of the independent latent
product. The outer average fixes all unselected coordinates. -/
theorem product_partition_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (source : Index → FiniteDist Scalar) (selected : Finset Index)
    (test : (Index → Scalar) → ℝ) :
    (FiniteDist.independent source).expectation test =
      ∑ rest : {index : Index // index ∉ selected} → Scalar,
        (∏ index : {index : Index // index ∉ selected}, (source index).weight (rest index)) *
          ∑ chosen : selected → Scalar,
            (∏ index : selected, (source index).weight (chosen index)) *
              test (assemble selected chosen rest) := by
  let split := Equiv.piEquivPiSubtypeProd (fun index => index ∈ selected) (fun _ : Index => Scalar)
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← split.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chosen _
  have hweight : (∏ index, (source index).weight (split.symm (chosen, rest) index)) =
      (∏ index : selected, (source index).weight (chosen index)) *
        ∏ index : {index : Index // index ∉ selected}, (source index).weight (rest index) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun index => index ∈ selected)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro index _
      change (source index).weight (if h : (index : Index) ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩) = _
      simp only [dif_pos index.property]
    · apply Finset.prod_congr (by ext; simp)
      intro index _
      change (source index).weight (if h : (index : Index) ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩) = _
      simp only [dif_neg index.property]
  change (∏ index, (source index).weight (split.symm (chosen, rest) index)) *
    test (assemble selected chosen rest) = _
  rw [hweight]
  ring

abbrev OtherSlots {order : ℕ} (slot : Fin order) := {other : Fin order // other ≠ slot}

/-- An isolated root is independent of the complete tuple of remaining
selected roots, in the exact centered-test formulation. -/
theorem isolated_centered_test_zero {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) (hisolated : Isolated sites slot)
    (test : ZMod modulus → ℝ)
    (hcentered : (ProtectedCycle.differenceLaw source value).expectation test = 0)
    (otherTest : (OtherSlots slot → ZMod modulus) → ℝ) :
    (selectedLaw body order modulus source value sites).expectation
      (fun root => test (root slot) * otherTest (fun other => root other)) = 0 := by
  haveI : Nonempty Scalar := by
    by_contra hnonempty
    haveI : IsEmpty Scalar := not_nonempty_iff.mp hnonempty
    have h := source.sum_one
    simp at h
  let support := latentSupport (sites slot)
  let first : support := ⟨sites slot, Finset.mem_insert_self _ _⟩
  let second : support := ⟨(finRotate body).symm (sites slot),
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have hdistinct : second ≠ first := by
    intro hequal
    have hvalues := congrArg Subtype.val hequal
    exact ProtectedCycle.cycle_predecessor_ne body hbody (sites slot) hvalues
  have hpair := ProtectedCycle.independent_pair_expectation
    (fun _ : support => source) first second hdistinct
    (fun firstValue secondValue => test (value firstValue - value secondValue))
  have hdifference :
      (ProtectedCycle.differenceLaw source value).expectation test =
        ∑ firstValue, ∑ secondValue, source.weight firstValue * source.weight secondValue *
          test (value firstValue - value secondValue) := by
    rw [ProtectedCycle.differenceLaw, FiniteDist.expectation_map]
    simp only [FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type, Function.comp_apply]
  have hselected :
      (∑ chosen : support → Scalar, (∏ index : support, source.weight (chosen index)) *
        test (value (chosen first) - value (chosen second))) = 0 := by
    simpa only [FiniteDist.expectation, FiniteDist.independent] using
      (hpair.trans hdifference.symm).trans hcentered
  unfold selectedLaw ProtectedCycle.cycleLaw
  rw [FiniteDist.expectation_map, FiniteDist.expectation_map]
  change (FiniteDist.independent (fun _ : Fin body => source)).expectation
    (fun latent => test (PublicCharge.cycleDifference (fun vertex => value (latent vertex)) (sites slot)) *
      otherTest (fun other => PublicCharge.cycleDifference
        (fun vertex => value (latent vertex)) (sites other))) = 0
  rw [product_partition_expectation (fun _ : Fin body => source) support]
  apply Finset.sum_eq_zero
  intro rest _
  let defaultChosen : support → Scalar := fun _ => Classical.choice inferInstance
  let otherValue := otherTest (fun other : OtherSlots slot => PublicCharge.cycleDifference
    (fun vertex => value (assemble support defaultChosen rest vertex)) (sites other))
  have hother (chosen : support → Scalar) :
      otherTest (fun other : OtherSlots slot => PublicCharge.cycleDifference
        (fun vertex => value (assemble support chosen rest vertex)) (sites other)) = otherValue := by
    apply congrArg otherTest
    funext other
    apply isolated_other_roots_unchanged sites slot other other.property hisolated
    intro vertex hnot
    have hnot' : vertex ∉ support := hnot
    rw [assemble_rest support chosen rest vertex hnot',
      assemble_rest support defaultChosen rest vertex hnot']
  have hroot (chosen : support → Scalar) :
      PublicCharge.cycleDifference (fun vertex => value (assemble support chosen rest vertex))
        (sites slot) = value (chosen first) - value (chosen second) := by
    dsimp only [PublicCharge.cycleDifference]
    rw [assemble_selected support chosen rest (sites slot) first.property,
      assemble_selected support chosen rest ((finRotate body).symm (sites slot)) second.property]
  simp_rw [hother, hroot, ← mul_assoc]
  rw [← Finset.sum_mul, hselected, zero_mul, mul_zero]

/-- Full real-test factorization, proving independence of the isolated root
from the joint tuple of all other selected roots. -/
theorem isolated_root_factorization {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) (hisolated : Isolated sites slot)
    (test : ZMod modulus → ℝ) (otherTest : (OtherSlots slot → ZMod modulus) → ℝ) :
    (selectedLaw body order modulus source value sites).expectation
        (fun root => test (root slot) * otherTest (fun other => root other)) =
      (ProtectedCycle.differenceLaw source value).expectation test *
        (selectedLaw body order modulus source value sites).expectation
          (fun root => otherTest (fun other => root other)) := by
  let mean := (ProtectedCycle.differenceLaw source value).expectation test
  have hmean : (ProtectedCycle.differenceLaw source value).expectation (fun color => test color - mean) = 0 := by
    unfold FiniteDist.expectation
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
    change mean - mean = 0
    ring
  have hzero := isolated_centered_test_zero body order modulus hbody source value sites slot hisolated
    (fun color => test color - mean) hmean otherTest
  have hexpand :
      (selectedLaw body order modulus source value sites).expectation
          (fun root => (test (root slot) - mean) * otherTest (fun other => root other)) =
      (selectedLaw body order modulus source value sites).expectation
          (fun root => test (root slot) * otherTest (fun other => root other)) -
        mean * (selectedLaw body order modulus source value sites).expectation
          (fun root => otherTest (fun other => root other)) := by
    unfold FiniteDist.expectation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro root _
    ring
  rw [hexpand] at hzero
  linarith

/-- The exact centered atom used to express a joint likelihood's full
coordinate-centering projection on product-reference support. -/
def centeredRootAtom {Color : Type*} [Fintype Color] (reference : FiniteDist Color)
    (input output : Color) : ℝ :=
  (if input = output then 1 else 0) / reference.weight output - 1

theorem centeredRootAtom_mean_zero {Color : Type*} [Fintype Color]
    (reference : FiniteDist Color) (output : Color) (houtput : reference.weight output ≠ 0) :
    reference.expectation (fun input => centeredRootAtom reference input output) = 0 := by
  unfold FiniteDist.expectation centeredRootAtom
  calc
    _ = (∑ input, if input = output then reference.weight input else 0) / reference.weight output -
        ∑ input, reference.weight input := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro input _
      by_cases h : input = output <;> simp only [h, if_true, if_false] <;> ring
    _ = 0 := by simp [reference.sum_one, houtput]

/-- The actual fully centered joint-density response, as its finite centered
atom formula. It keeps the complete selected-root joint law. -/
def centeredRootDensity {Index Color : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (output : Index → Color) : ℝ :=
  joint.expectation (fun input => ∏ index, centeredRootAtom (reference index) (input index) (output index))

/-- Any isolated selected site annihilates the whole centered joint-root
coefficient. The others may remain arbitrarily dependent through the cycle. -/
theorem isolated_centeredRootDensity_zero {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) (hisolated : Isolated sites slot)
    (output : Fin order → ZMod modulus)
    (houtput : (ProtectedCycle.differenceLaw source value).weight (output slot) ≠ 0) :
    centeredRootDensity (selectedLaw body order modulus source value sites)
      (fun _ => ProtectedCycle.differenceLaw source value) output = 0 := by
  have hzero := isolated_centered_test_zero body order modulus hbody source value sites slot hisolated
    (fun color => centeredRootAtom (ProtectedCycle.differenceLaw source value) color (output slot))
    (centeredRootAtom_mean_zero _ _ houtput)
    (fun other => ∏ index : OtherSlots slot,
      centeredRootAtom (ProtectedCycle.differenceLaw source value) (other index) (output index))
  unfold centeredRootDensity
  convert hzero using 1
  apply congrArg (selectedLaw body order modulus source value sites).expectation
  funext input
  exact Fintype.prod_eq_mul_prod_subtype_ne _ slot

end

end CurrentAFT.CycleSelections

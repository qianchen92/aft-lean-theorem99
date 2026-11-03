import CurrentAFT.CycleSelections
import AFT.CompatibleFibers

/-! # Actual independent latent pairs on a cyclic matching -/

namespace CurrentAFT.CycleMatching

open AFT CurrentAFT.CycleSelections
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def IsMatching {body : ℕ} (selected : Finset (Fin body)) : Prop :=
  ∀ first second : selected, first ≠ second → ¬Adjacent body first.val second.val

def pairPosition {body : ℕ} (selected : Finset (Fin body)) (point : selected × Fin 2) : Fin body :=
  if point.2 = 0 then (finRotate body).symm point.1.val else point.1.val

theorem pairPosition_injective (body : ℕ) (hbody : 2 ≤ body)
    (selected : Finset (Fin body)) (hmatching : IsMatching selected) :
    Function.Injective (pairPosition selected) := by
  rintro ⟨first, firstSlot⟩ ⟨second, secondSlot⟩ hequal
  fin_cases firstSlot <;> fin_cases secondSlot
  · have h : (finRotate body).symm first.val = (finRotate body).symm second.val := by simpa [pairPosition] using hequal
    exact Prod.ext (Subtype.ext ((finRotate body).symm.injective h)) rfl
  · have h : (finRotate body).symm first.val = second.val := by simpa [pairPosition] using hequal
    by_cases hsame : first = second
    · subst second
      exact False.elim ((ProtectedCycle.cycle_predecessor_ne body hbody first.val) h)
    · exact False.elim (hmatching first second hsame (Or.inr (by
        have hh := congrArg (finRotate body) h
        simpa only [Equiv.apply_symm_apply] using hh)))
  · have h : first.val = (finRotate body).symm second.val := by simpa [pairPosition] using hequal
    by_cases hsame : first = second
    · subst second
      exact False.elim ((ProtectedCycle.cycle_predecessor_ne body hbody first.val) h.symm)
    · exact False.elim (hmatching first second hsame (Or.inl (by
        have hh := congrArg (finRotate body) h
        simpa only [Equiv.apply_symm_apply] using hh.symm)))
  · have h : first.val = second.val := by simpa [pairPosition] using hequal
    exact Prod.ext (Subtype.ext h) rfl

def pairEmbedding (body : ℕ) (hbody : 2 ≤ body) (selected : Finset (Fin body))
    (hmatching : IsMatching selected) : (selected × Fin 2) ↪ Fin body :=
  ⟨pairPosition selected, pairPosition_injective body hbody selected hmatching⟩

def pairGrouping {Selected Scalar : Type*} : ((Selected × Fin 2) → Scalar) ≃ (Selected → Scalar × Scalar) where
  toFun word := fun selected => (word (selected, 0), word (selected, 1))
  invFun word := fun point => if point.2 = 0 then (word point.1).1 else (word point.1).2
  left_inv word := by funext point; rcases point with ⟨selected, slot⟩; fin_cases slot <;> simp
  right_inv word := by funext selected; simp

theorem grouped_product_law {Selected Scalar : Type*} [Fintype Selected] [DecidableEq Selected] [Fintype Scalar]
    (source : FiniteDist Scalar) :
    (FiniteDist.independent (fun _ : Selected × Fin 2 => source)).map pairGrouping =
      FiniteDist.independent (fun _ : Selected => source.prod source) := by
  ext word
  rw [FiniteDist.map_equiv_weight]
  change (∏ point : Selected × Fin 2, source.weight (pairGrouping.symm word point)) =
    ∏ selected : Selected, source.weight (word selected).1 * source.weight (word selected).2
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro selected _
  rw [Fin.prod_univ_two]
  simp [pairGrouping]

/-- Every cyclic matching sees a genuine product of iid latent pairs.
The latent table is sampled once; the closing edge is retained in `pred`. -/
theorem matching_expectation {Scalar : Type*} [Fintype Scalar]
    (body : ℕ) (hbody : 2 ≤ body) (source : FiniteDist Scalar)
    (selected : Finset (Fin body)) (hmatching : IsMatching selected)
    (test : (selected → Scalar × Scalar) → ℝ) :
    (FiniteDist.independent (fun _ : Fin body => source)).expectation
      (fun latent => test (fun vertex =>
        (latent ((finRotate body).symm vertex.val), latent vertex.val))) =
      (FiniteDist.independent (fun _ : selected => source.prod source)).expectation test := by
  have h := CanonicalMoments.independent_embedding_expectation_general
    (fun _ : Fin body => source) (pairEmbedding body hbody selected hmatching)
    (fun word => test (pairGrouping word))
  have hleft : (fun latent : Fin body → Scalar => test
      (pairGrouping (latent ∘ pairEmbedding body hbody selected hmatching))) =
      (fun latent => test (fun vertex => (latent ((finRotate body).symm vertex.val), latent vertex.val))) := by
    funext latent
    congr 1
    funext vertex
    simp [pairGrouping, pairEmbedding, pairPosition]
  rw [hleft] at h
  apply h.trans
  have hmap := FiniteDist.expectation_map
    (FiniteDist.independent (fun _ : selected × Fin 2 => source)) pairGrouping test
  rw [grouped_product_law (Selected := selected) source] at hmap
  convert hmap.symm using 1
  unfold FiniteDist.expectation FiniteDist.independent
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- One vertex breaks the parity coloring into three genuine matchings,
for odd and even cycle lengths alike. -/
def cycleColor {body : ℕ} (vertex : Fin body) : Fin 3 :=
  if vertex.val = 0 then 2 else if vertex.val % 2 = 0 then 0 else 1

theorem cycleColor_next_ne (body : ℕ) (hbody : 2 ≤ body) (vertex : Fin body) :
    cycleColor (finRotate body vertex) ≠ cycleColor vertex := by
  cases body with
  | zero => omega
  | succ size =>
    by_cases hlast : vertex = Fin.last size
    · subst vertex
      rw [finRotate_last]
      have hsize : size ≠ 0 := by omega
      simp only [cycleColor, Fin.val_zero, Fin.val_last, if_neg hsize]
      split_ifs <;> omega
    · have hnext := coe_finRotate_of_ne_last hlast
      have hnextPositive : (finRotate (size + 1) vertex).val ≠ 0 := by omega
      by_cases hzero : vertex.val = 0
      · simp only [cycleColor, if_neg hnextPositive, if_pos hzero]
        split_ifs <;> omega
      · simp only [cycleColor, if_neg hzero, hnext]
        split_ifs <;> norm_num at * <;> omega

def colorClass (body : ℕ) (color : Fin 3) : Finset (Fin body) :=
  Finset.univ.filter (fun vertex => cycleColor vertex = color)

theorem colorClass_matching (body : ℕ) (hbody : 2 ≤ body) (color : Fin 3) :
    IsMatching (colorClass body color) := by
  intro first second _ hadjacent
  have hfirst := (Finset.mem_filter.mp first.property).2
  have hsecond := (Finset.mem_filter.mp second.property).2
  rcases hadjacent with hnext | hnext
  · exact cycleColor_next_ne body hbody first.val (by rw [← hnext]; exact hsecond.trans hfirst.symm)
  · exact cycleColor_next_ne body hbody second.val (by rw [← hnext]; exact hfirst.trans hsecond.symm)

theorem sum_colorClasses {Value : Type*} [AddCommMonoid Value] (body : ℕ) (value : Fin body → Value) :
    (∑ color : Fin 3, ∑ vertex : colorClass body color, value vertex.val) = ∑ vertex : Fin body, value vertex := by
  simp only [colorClass, Finset.sum_coe_sort]
  exact Finset.sum_fiberwise Finset.univ cycleColor value

end

end CurrentAFT.CycleMatching

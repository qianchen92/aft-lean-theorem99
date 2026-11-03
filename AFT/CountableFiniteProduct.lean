import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Reflection

/-! # Exact finite products of countable nonnegative summable masses -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem countableFiniteProduct_summable_sum {State : Type*} (count : ℕ)
    (mass : Fin count → State → ℝ)
    (hnonneg : ∀ i state,0≤mass i state) (hsum : ∀ i,Summable (mass i)) :
    Summable (fun word : Fin count → State => ∏ i,mass i (word i)) ∧
      (∑' word : Fin count → State,∏ i,mass i (word i))=∏ i,∑' state,mass i state := by
  induction count with
  | zero =>
    letI : Fintype (Fin 0 → State) := Fintype.ofFinite _
    exact ⟨(hasSum_fintype _).summable,by simp⟩
  | succ count ih =>
    obtain ⟨htail,hvalue⟩ := ih (fun i => mass i.succ) (fun i => hnonneg i.succ) (fun i => hsum i.succ)
    have hp := (hsum 0).mul_of_nonneg htail (hnonneg 0)
      (fun word => Finset.prod_nonneg (fun i _ => hnonneg i.succ (word i)))
    let equiv : State × (Fin count → State) ≃ (Fin (count+1) → State) := Fin.consEquiv (fun _ => State)
    have hword (point : State × (Fin count → State)) :
        (∏ i,mass i (equiv point i))=mass 0 point.1*∏ i : Fin count,mass i.succ (point.2 i) := by
      simp only [Fin.prod_univ_succ,equiv,Fin.consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.cons_succ]
    constructor
    · apply equiv.summable_iff.mp
      change Summable (fun point : State × (Fin count → State) => ∏ i,mass i (equiv point i))
      simpa only [hword] using hp
    · rw [← equiv.tsum_eq]
      simp only [hword]
      rw [← (hsum 0).tsum_mul_tsum htail hp,hvalue,Fin.prod_univ_succ]

end
end AFT

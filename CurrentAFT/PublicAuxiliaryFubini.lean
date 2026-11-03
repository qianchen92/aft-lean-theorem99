import AFT.RootTensorActivity
import AFT.FiniteChannelIdentities

/-! # Finite Fubini for exposing independent public seeds -/
namespace CurrentAFT.PublicAuxiliaryFubini
open AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def enumeration {State : Type*} {source : Fintype State} (_law : @FiniteDist State source) : Fintype State := source

theorem sum_erase_le_enumeration {State : Type*} {source : Fintype State} [target : Fintype State]
    [DecidableEq State] (zero : State) (value : State → ℝ) (bound : ℝ)
    (hbound : (∑ point ∈ (@Finset.univ State source).erase zero, value point) ≤ bound) :
    (∑ point ∈ (@Finset.univ State target).erase zero, value point) ≤ bound := by
  cases Subsingleton.elim source target
  exact hbound

theorem uniform_expectation_enumeration {State : Type*} {source : Fintype State} [target : Fintype State]
    [Nonempty State] (test : State → ℝ) :
    @FiniteDist.expectation State source (@FiniteDist.uniform State source inferInstance) test =
      (FiniteDist.uniform State).expectation test := by
  cases Subsingleton.elim source target
  rfl

theorem retype_uniform {State : Type*} {source : Fintype State} [target : Fintype State]
    [Nonempty State] : FiniteDist.retype (@FiniteDist.uniform State source inferInstance) = FiniteDist.uniform State := by
  cases Subsingleton.elim source target
  rfl

theorem expectation_retype_prod {First Second : Type*} {firstSource : Fintype First}
    {secondSource : Fintype Second} [Fintype First] [Fintype Second]
    (first : @FiniteDist First firstSource) (second : @FiniteDist Second secondSource)
    (test : First × Second → ℝ) :
    (FiniteDist.retype (@FiniteDist.prod First Second firstSource secondSource first second)).expectation test =
      (FiniteDist.retype first).expectation (fun left => (FiniteDist.retype second).expectation
        (fun right => test (left, right))) := by
  cases Subsingleton.elim firstSource (inferInstance : Fintype First)
  cases Subsingleton.elim secondSource (inferInstance : Fintype Second)
  exact FiniteDist.expectation_prod first second test

theorem independent_product {Index Color : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
    (law : Index → FiniteDist Color) (factor : Index → Color → ℝ) :
    (FiniteDist.independent law).expectation (fun word => ∏ index, factor index (word index)) =
      ∏ index, (law index).expectation (factor index) := by
  unfold FiniteDist.expectation FiniteDist.independent
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

theorem independent_pair_product {Left Right First Second : Type*}
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    [Fintype First] [Fintype Second]
    (first : Left → FiniteDist First) (second : Right → FiniteDist Second)
    (left : Left → First → ℝ) (right : Right → Second → ℝ) (fixed : ℝ) :
    (FiniteDist.independent first).expectation (fun leftWord =>
      (FiniteDist.independent second).expectation (fun rightWord =>
        (∏ index, left index (leftWord index)) * (fixed * ∏ index, right index (rightWord index)))) =
      (∏ index, (first index).expectation (left index)) *
        (fixed * ∏ index, (second index).expectation (right index)) := by
  simp_rw [FiniteDist.expectation_const_mul]
  rw [FiniteDist.expectation_mul_const, independent_product, independent_product]

theorem expectation_mix {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : FiniteDist Source) (channel : Source → FiniteDist Output) (test : Output → ℝ) :
    (law.mix channel).expectation test =
      law.expectation (fun source => (channel source).expectation test) := by
  unfold FiniteDist.expectation
  simp only [FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro output _
  ring

theorem mix_assoc {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (law : FiniteDist First) (channel : First → FiniteDist Second) (last : Second → FiniteDist Output) :
    (law.mix channel).mix last = law.mix (fun first => (channel first).mix last) := by
  ext output
  simp only [FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem five_expectation_interchange {A B C Q L : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype Q] [Fintype L]
    (a : FiniteDist A) (b : FiniteDist B) (c : FiniteDist C)
    (q : FiniteDist Q) (l : FiniteDist L) (test : A → B → C → Q → L → ℝ) :
    a.expectation (fun av => b.expectation (fun bv => c.expectation (fun cv =>
      q.expectation (fun qv => l.expectation (test av bv cv qv))))) =
      c.expectation (fun cv => q.expectation (fun qv => b.expectation (fun bv =>
        l.expectation (fun lv => a.expectation (fun av => test av bv cv qv lv))))) := by
  rw [FiniteDist.expectation_comm a b]
  simp_rw [FiniteDist.expectation_comm a c]
  simp_rw [FiniteDist.expectation_comm a q]
  simp_rw [FiniteDist.expectation_comm a l]
  rw [FiniteDist.expectation_comm b c]
  simp_rw [FiniteDist.expectation_comm b q]

theorem average_map {Core Input Output : Type*} [Fintype Core] [Fintype Input] [Fintype Output]
    (proposal : FiniteDist Core) (channel : Core → FiniteDist Input) (law : FiniteDist Input)
    (haverage : ∀ input, proposal.expectation (fun core => (channel core).weight input) = law.weight input)
    (record : Input → Output) (output : Output) :
    proposal.expectation (fun core => ((channel core).map record).weight output) = (law.map record).weight output := by
  simp only [FiniteDist.map_weight]
  rw [FiniteDist.expectation_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hequal : record input = output
  · simp only [if_pos hequal]
    exact haverage input
  · simp only [if_neg hequal, FiniteDist.expectation_const]

end
end CurrentAFT.PublicAuxiliaryFubini

import AFT.TotalVariation

/-! # Support-preserving identities for finite physical channels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source Inner Output : Type*} [Fintype Source] [Fintype Inner] [Fintype Output]

omit [Fintype Inner] in
theorem mix_congr_support (law : FiniteDist Source) (first second : Source → FiniteDist Output)
    (heq : ∀ source,law.weight source≠0 → first source=second source) : law.mix first=law.mix second := by
  apply FiniteDist.ext
  intro output
  apply Finset.sum_congr rfl
  intro source _
  by_cases hs : law.weight source=0
  · simp only [hs,zero_mul]
  · rw [heq source hs]

 theorem mix_comm (first : FiniteDist Source) (second : FiniteDist Inner)
    (channel : Source → Inner → FiniteDist Output) :
    first.mix (fun source => second.mix (channel source))=
      second.mix (fun inner => first.mix (fun source => channel source inner)) := by
  apply FiniteDist.ext
  intro output
  simp only [mix_weight,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inner _
  apply Finset.sum_congr rfl
  intro source _
  ring

omit [Fintype Inner] in
theorem TVBound.mix_right (law : FiniteDist Source) {first second : Source → FiniteDist Output}
    {error : ℝ} (hbound : ∀ source,TVBound (first source) (second source) error) :
    TVBound (law.mix first) (law.mix second) error := by
  intro event
  simp only [event_mix,← Finset.sum_sub_distrib,← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (law.nonneg _)]
  calc
    _ ≤ ∑ source,law.weight source*error :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hbound source event) (law.nonneg source)
    _ = error := by rw [← Finset.sum_mul,law.sum_one,one_mul]

end
end AFT.FiniteDist

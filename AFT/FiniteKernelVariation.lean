import AFT.BetaReference
import AFT.MixtureConditioning

/-! # Finite exceptional-input replacement and probability conditioning -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source State : Type*} [Fintype Source] [Fintype State]

theorem eventMass_complement (law : FiniteDist Source) (event : Source → Prop) :
    law.eventMass (fun source => ¬event source)=1-law.eventMass event := by
  have he : law.eventMass (fun source => ¬event source)+law.eventMass event=1 := by
    rw [eventMass,eventMass,← Finset.sum_add_distrib,← law.sum_one]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> simp_all
  linarith

/-- Replacing the output kernel only on an exceptional source event costs
at most that event's true probability. -/
theorem mix_exception_tv (source : FiniteDist Source) (first second : Source → FiniteDist State)
    (good : Source → Prop) (hagree : ∀ index,good index → first index=second index) :
    TVBound (source.mix first) (source.mix second) (source.eventMass fun index => ¬good index) := by
  intro event
  rw [event_mix,event_mix,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases hg : good index
  · simp only [hagree index hg,sub_self,abs_zero,hg,not_true_eq_false,if_false,le_refl]
  · have hfirst := (first index).event_nonneg event
    have hsecond := (second index).event_nonneg event
    have hf1 := (first index).event_le_one event
    have hs1 := (second index).event_le_one event
    have hb : |(first index).event event-(second index).event event| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    simp only [hg,not_false_eq_true,if_true,← mul_sub,abs_mul,abs_of_nonneg (source.nonneg index)]
    exact (mul_le_mul_of_nonneg_left hb (source.nonneg index)).trans_eq (mul_one _)

/-- Conditioning a genuine probability deletes at most its rejected mass. -/
theorem condition_self_tv (law : FiniteDist Source) (event : Source → Prop) (hpos : 0 < law.eventMass event) :
    TVBound (law.condition event hpos) law (law.eventMass fun source => ¬event source) := by
  obtain ⟨p,hp,htv⟩ := BetaReference.normalized_dominated_tv law
    (fun source => if event source then law.weight source else 0) (law.eventMass event)
    (fun source => by dsimp only; split_ifs; exact law.nonneg source; rfl)
    (fun source => by dsimp only; split_ifs; rfl; exact law.nonneg source) rfl hpos
  have he : p=law.condition event hpos := by
    ext source
    exact hp source
  rw [he] at htv
  simpa only [eventMass_complement] using htv

end
end AFT.FiniteDist

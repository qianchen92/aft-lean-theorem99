import AFT.FiniteProbability

/-!
# Eventwise total variation bounds and the endpoint/carry reduction

On finite spaces, `TVBound p q error` is precisely the assertion that the
maximum absolute difference on an event is at most `error`, the convention
used in reference V7. No probability estimate is assumed by the definition.
-/

namespace AFT
namespace FiniteDist

open scoped BigOperators
open scoped Classical

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]

/-- Probability of an event. -/
noncomputable def event (p : FiniteDist α) (s : Finset α) : ℝ :=
  ∑ a ∈ s, p.weight a

/-- Statistical distance at most `error`, in its eventwise definition. -/
def TVBound (p q : FiniteDist α) (error : ℝ) : Prop :=
  ∀ s : Finset α, |p.event s - q.event s| ≤ error

theorem event_nonneg (p : FiniteDist α) (s : Finset α) : 0 ≤ p.event s :=
  Finset.sum_nonneg (fun a _ => p.nonneg a)

theorem tvBound_refl (p : FiniteDist α) : TVBound p p 0 := by
  intro s
  simp

theorem TVBound.symm {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) : TVBound q p error := by
  intro s
  rw [abs_sub_comm]
  exact h s

theorem TVBound.mono {p q : FiniteDist α} {error largerError : ℝ}
    (h : TVBound p q error) (hle : error ≤ largerError) :
    TVBound p q largerError := fun s => (h s).trans hle

theorem TVBound.triangle {p q r : FiniteDist α} {firstError secondError : ℝ}
    (hfirst : TVBound p q firstError) (hsecond : TVBound q r secondError) :
    TVBound p r (firstError + secondError) := by
  intro s
  calc
    |p.event s - r.event s| ≤ |p.event s - q.event s| + |q.event s - r.event s| :=
      abs_sub_le _ _ _
    _ ≤ firstError + secondError := add_le_add (hfirst s) (hsecond s)

theorem event_map (p : FiniteDist α) (f : α → β) (s : Finset β) :
    (p.map f).event s = ∑ a, if f a ∈ s then p.weight a else 0 := by
  classical
  simp only [event, map_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

/-- Deterministic data processing, including a canonical endpoint pullback. -/
theorem TVBound.map {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) (f : α → β) : TVBound (p.map f) (q.map f) error := by
  classical
  intro s
  rw [event_map, event_map]
  simpa only [event, Finset.sum_filter] using
    h (Finset.univ.filter (fun a => f a ∈ s))

/-- Disagreement probability for two outputs defined on the same randomness. -/
noncomputable def disagreement (p : FiniteDist Ω) (left right : Ω → α) : ℝ :=
  ∑ sample, if left sample = right sample then 0 else p.weight sample

/-- The coupling inequality, without independence assumptions on the outputs. -/
theorem coupling_bound (p : FiniteDist Ω) (left right : Ω → α) :
    TVBound (p.map left) (p.map right) (p.disagreement left right) := by
  classical
  intro s
  rw [event_map, event_map, ← Finset.sum_sub_distrib]
  calc
    |∑ sample, ((if left sample ∈ s then p.weight sample else 0) -
        (if right sample ∈ s then p.weight sample else 0))|
      ≤ ∑ sample, |(if left sample ∈ s then p.weight sample else 0) -
        (if right sample ∈ s then p.weight sample else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ p.disagreement left right := by
      apply Finset.sum_le_sum
      intro sample _
      by_cases heq : left sample = right sample
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        split_ifs <;> simp [abs_of_nonneg (p.nonneg sample), p.nonneg sample]

/-- The probability-theoretic part of V7 Lemma 6.12. The target is the
pushforward of the endpoint reference under its pullback. The geometric
proof identifying this law with uniform on the zero fiber is separate. -/
theorem endpoint_carry_bound (p : FiniteDist Ω) (output : Ω → α)
    (endpoint : Ω → β) (pullback : β → α) (endpointReference : FiniteDist β)
    (badCarry : Ω → Prop) [DecidablePred badCarry]
    (hgood : ∀ sample, ¬ badCarry sample → output sample = pullback (endpoint sample))
    {endpointError carryError : ℝ}
    (hendpoint : TVBound (p.map endpoint) endpointReference endpointError)
    (hcarry : (∑ sample, if badCarry sample then p.weight sample else 0) ≤ carryError) :
    TVBound (p.map output) (endpointReference.map pullback) (endpointError + carryError) := by
  classical
  have hcouple : TVBound (p.map output) (p.map (fun s => pullback (endpoint s))) carryError := by
    apply (coupling_bound p output (fun s => pullback (endpoint s))).mono
    apply le_trans _ hcarry
    apply Finset.sum_le_sum
    intro sample _
    by_cases hb : badCarry sample
    · simp only [hb, ↓reduceIte]
      split_ifs <;> simp [p.nonneg sample]
    · simp [hb, hgood sample hb]
  have hcomp : (p.map endpoint).map pullback = p.map (fun s => pullback (endpoint s)) :=
    p.map_map endpoint pullback
  have htransport := hendpoint.map pullback
  rw [hcomp] at htransport
  simpa only [add_comm] using hcouple.triangle htransport

end FiniteDist
end AFT

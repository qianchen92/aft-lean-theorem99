import AFT.ConditionRejection
import AFT.FiniteRefresh

/-! # Executable finite rejection for a decidable event

The procedure checks a finite stream in order, returns its first accepted
entry, and returns a fixed fallback if every check fails. It evaluates no
real probabilities. Its law is exactly the capped conditioning law.
-/

namespace AFT.FiniteConditionProgram

open scoped BigOperators

variable {State : Type*}

def firstAccepted (event : State → Prop) [DecidablePred event] (fallback : State) :
    (attempts : ℕ) → (Fin attempts → State) → State
  | 0, _ => fallback
  | attempts + 1, proposals =>
      if event (proposals 0) then proposals 0
      else firstAccepted event fallback attempts (fun index => proposals index.succ)

/-- Number of event checks in the same short-circuit execution. -/
def checks (event : State → Prop) [DecidablePred event] :
    (attempts : ℕ) → (Fin attempts → State) → ℕ
  | 0, _ => 0
  | attempts + 1, proposals =>
      if event (proposals 0) then 1
      else 1 + checks event attempts (fun index => proposals index.succ)

def firstAcceptedFrom {Random : Type*} (decode : Random → State)
    (event : State → Prop) [DecidablePred event] (fallback : State)
    (attempts : ℕ) (randomness : Fin attempts → Random) : State :=
  firstAccepted event fallback attempts (fun index => decode (randomness index))

/-- Explicit row-major regrouping of one finite bit tape into proposal tapes. -/
def groupBits (attempts bits : ℕ) :
    (Fin (attempts * bits) → Fin 2) ≃ (Fin attempts → Fin bits → Fin 2) where
  toFun word attempt bit := word (finProdFinEquiv (attempt, bit))
  invFun words index := words (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
  left_inv word := by
    funext index
    change word (finProdFinEquiv (finProdFinEquiv.symm index)) = word index
    rw [Equiv.apply_symm_apply]
  right_inv words := by
    funext attempt bit
    change words (finProdFinEquiv.symm (finProdFinEquiv (attempt, bit))).1
      (finProdFinEquiv.symm (finProdFinEquiv (attempt, bit))).2 = words attempt bit
    rw [Equiv.symm_apply_apply]

/-- A finite rejection program driven by exactly `attempts * bits` available
fair bits. Early success may leave a suffix unread. -/
def draw (bits attempts : ℕ) (decode : (Fin bits → Fin 2) → State)
    (event : State → Prop) [DecidablePred event] (fallback : State)
    (randomness : Fin (attempts * bits) → Fin 2) : State :=
  firstAcceptedFrom decode event fallback attempts (groupBits attempts bits randomness)

theorem checks_le (event : State → Prop) [DecidablePred event]
    (attempts : ℕ) (proposals : Fin attempts → State) : checks event attempts proposals ≤ attempts := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [checks]
    split_ifs
    · omega
    · have hh := ih (fun index => proposals index.succ)
      omega

theorem firstAccepted_event (event : State → Prop) [DecidablePred event]
    (fallback : State) (hfallback : event fallback)
    (attempts : ℕ) (proposals : Fin attempts → State) :
    event (firstAccepted event fallback attempts proposals) := by
  induction attempts with
  | zero => exact hfallback
  | succ attempts ih =>
    simp only [firstAccepted]
    split_ifs with he
    · exact he
    · exact ih (fun index => proposals index.succ)

theorem firstAccepted_of_no_success (event : State → Prop) [DecidablePred event]
    (fallback : State) (attempts : ℕ) (proposals : Fin attempts → State)
    (hfail : ∀ index, ¬ event (proposals index)) :
    firstAccepted event fallback attempts proposals = fallback := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [firstAccepted, if_neg (hfail 0)]
    exact ih (fun index => proposals index.succ) (fun index => hfail index.succ)

theorem draw_event (bits attempts : ℕ) (decode : (Fin bits → Fin 2) → State)
    (event : State → Prop) [DecidablePred event] (fallback : State) (hfallback : event fallback)
    (randomness : Fin (attempts * bits) → Fin 2) :
    event (draw bits attempts decode event fallback randomness) :=
  firstAccepted_event event fallback hfallback attempts _

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable [Fintype State]

theorem independent_cons (proposal : FiniteDist State) (attempts : ℕ) :
    FiniteDist.independent (fun _ : Fin (attempts + 1) => proposal) =
      (proposal.prod (FiniteDist.independent (fun _ : Fin attempts => proposal))).map
        (Fin.consEquiv (fun _ : Fin (attempts + 1) => State)) := by
  apply FiniteDist.ext
  intro word
  rw [FiniteDist.map_equiv_weight]
  change (∏ index, proposal.weight (word index)) =
    proposal.weight (word 0) * ∏ index : Fin attempts, proposal.weight (word index.succ)
  exact Fin.prod_univ_succ _

/-- A fresh proposal either succeeds or uses an independently computed
remaining output. This is the exact transition, including event failure. -/
theorem select_event_law {Random : Type*} [Fintype Random]
    (proposal : FiniteDist State) (remaining : FiniteDist Random)
    (output : Random → State) (event : State → Prop) [DecidablePred event] :
    (proposal.prod remaining).map (fun pair => if event pair.1 then pair.1 else output pair.2) =
      FiniteDist.rejectionStep proposal (FiniteDist.eventCoin event)
        (FiniteDist.eventCoin_bounds event) (remaining.map output) := by
  apply FiniteDist.ext
  intro target
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  have hpoint (candidate : State) :
      (∑ random, if (if event candidate then candidate else output random) = target
        then proposal.weight candidate * remaining.weight random else 0) =
      (if event candidate then (if candidate = target then proposal.weight candidate else 0) else 0) +
        (if event candidate then 0 else proposal.weight candidate) *
          (remaining.map output).weight target := by
    by_cases he : event candidate
    · by_cases ht : candidate = target
      · subst candidate
        simp only [he, if_true, ← Finset.mul_sum, remaining.sum_one, mul_one, zero_mul, add_zero]
      · simp only [he, if_true, if_neg ht, Finset.sum_const_zero, zero_mul, add_zero]
    · simp only [he, if_false, zero_add, FiniteDist.map_weight, Finset.mul_sum, mul_ite, mul_zero]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have haccepted :
      (∑ candidate, if event candidate then (if candidate = target then proposal.weight candidate else 0) else 0) =
      if event target then proposal.weight target else 0 := by
    rw [Finset.sum_eq_single target]
    · simp
    · intro candidate _ hne
      simp [hne]
    · simp
  have hfailed : (∑ candidate, if event candidate then 0 else proposal.weight candidate) =
      1 - FiniteDist.acceptance proposal (FiniteDist.eventCoin event) := by
    calc
      _ = ∑ candidate, (proposal.weight candidate -
          proposal.weight candidate * FiniteDist.eventCoin event candidate) := by
        apply Finset.sum_congr rfl
        intro candidate _
        simp only [FiniteDist.eventCoin]
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, proposal.sum_one]; rfl
  rw [haccepted, hfailed]
  change (if event target then proposal.weight target else 0) + _ =
    proposal.weight target * FiniteDist.eventCoin event target + _
  simp only [FiniteDist.eventCoin, mul_ite, mul_one, mul_zero]

/-- Independent repeated proposals followed by the executable first-success
procedure have exactly the repository's capped conditioning law. -/
theorem firstAccepted_law (proposal : FiniteDist State)
    (event : State → Prop) [DecidablePred event] (fallback : State) (attempts : ℕ) :
    (FiniteDist.independent (fun _ : Fin attempts => proposal)).map
      (firstAccepted event fallback attempts) =
      FiniteDist.cappedCondition proposal event (CanonicalMoments.pointLaw fallback) attempts := by
  induction attempts with
  | zero =>
    apply FiniteDist.ext
    intro target
    change ((FiniteDist.independent (fun _ : Fin 0 => proposal)).map (fun _ => fallback)).weight target =
      (CanonicalMoments.pointLaw fallback).weight target
    rw [FiniteDist.map_const_weight]
    rfl
  | succ attempts ih =>
    rw [independent_cons, FiniteDist.map_map]
    have he : (fun pair : State × (Fin attempts → State) =>
        firstAccepted event fallback (attempts + 1)
          ((Fin.consEquiv (fun _ : Fin (attempts + 1) => State)) pair)) =
        (fun pair => if event pair.1 then pair.1 else firstAccepted event fallback attempts pair.2) := by
      funext pair
      simp only [firstAccepted, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [he, select_event_law, ih]
    rfl

/-- Coordinatewise executable decoding preserves independence. An explicit
index equality instance keeps the finite function alphabets definitionally
consistent when the index type is executable, such as `Fin`. -/
theorem independent_decode {Index Random : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Random] (randomness : Index → FiniteDist Random)
    (decode : Index → Random → State) :
    (FiniteDist.independent randomness).map (fun word index => decode index (word index)) =
      FiniteDist.independent (fun index => (randomness index).map (decode index)) := by
  apply FiniteDist.ext
  intro values
  simp only [FiniteDist.map_weight, FiniteDist.independent]
  change (∑ word : Index → Random,
    if (fun index => decode index (word index)) = values
    then ∏ index, (randomness index).weight (word index) else 0) =
    ∏ index, ∑ point, if decode index point = values index then (randomness index).weight point else 0
  have he := Fintype.prod_sum (fun index point =>
    if decode index point = values index then (randomness index).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

theorem firstAcceptedFrom_law {Random : Type*} [Fintype Random]
    (randomness : FiniteDist Random) (decode : Random → State)
    (event : State → Prop) [DecidablePred event] (fallback : State) (attempts : ℕ) :
    (FiniteDist.independent (fun _ : Fin attempts => randomness)).map
      (firstAcceptedFrom decode event fallback attempts) =
      FiniteDist.cappedCondition (randomness.map decode) event
        (CanonicalMoments.pointLaw fallback) attempts := by
  have hh := independent_decode (fun _ : Fin attempts => randomness) (fun _ => decode)
  have hm := congrArg (fun law : FiniteDist (Fin attempts → State) =>
    law.map (firstAccepted event fallback attempts)) hh
  dsimp only at hm
  rw [FiniteDist.map_map] at hm
  exact hm.trans (firstAccepted_law (randomness.map decode) event fallback attempts)

theorem independent_uniform {Random : Type*} [Fintype Random] [Nonempty Random]
    (attempts : ℕ) :
    FiniteDist.independent (fun _ : Fin attempts => FiniteDist.uniform Random) =
      FiniteDist.uniform (Fin attempts → Random) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fun,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_pow, inv_pow]

theorem groupBits_law (attempts bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (attempts * bits) => FiniteDist.uniform (Fin 2))).map
      (groupBits attempts bits) =
      FiniteDist.independent (fun _ : Fin attempts =>
        FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))) := by
  simp only [independent_uniform]
  exact FiniteDist.uniform_map_equiv (groupBits attempts bits)

/-- The actual finite fair-bit tape, decoded and tested by executable code,
has the exact capped-conditioning law, including its exhaustion fallback. -/
theorem draw_law (bits attempts : ℕ) (decode : (Fin bits → Fin 2) → State)
    (event : State → Prop) [DecidablePred event] (fallback : State) :
    (FiniteDist.independent (fun _ : Fin (attempts * bits) => FiniteDist.uniform (Fin 2))).map
      (draw bits attempts decode event fallback) =
      FiniteDist.cappedCondition
        ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map decode)
        event (CanonicalMoments.pointLaw fallback) attempts := by
  have hh := congrArg (fun law : FiniteDist (Fin attempts → Fin bits → Fin 2) =>
    law.map (firstAcceptedFrom decode event fallback attempts)) (groupBits_law attempts bits)
  dsimp only at hh
  rw [FiniteDist.map_map] at hh
  exact hh.trans (firstAcceptedFrom_law _ decode event fallback attempts)

theorem firstAccepted_tv (proposal : FiniteDist State)
    (event : State → Prop) [DecidablePred event] (fallback : State) (attempts : ℕ)
    (hpos : 0 < proposal.eventMass event) :
    FiniteDist.TVBound
      ((FiniteDist.independent (fun _ : Fin attempts => proposal)).map
        (firstAccepted event fallback attempts))
      (proposal.condition event hpos)
      (Real.exp (-(attempts : ℝ) * proposal.eventMass event)) := by
  rw [firstAccepted_law]
  exact FiniteDist.cappedCondition_tv proposal event hpos (CanonicalMoments.pointLaw fallback) attempts

theorem draw_tv (bits attempts : ℕ) (decode : (Fin bits → Fin 2) → State)
    (event : State → Prop) [DecidablePred event] (fallback : State)
    (hpos : 0 < ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map decode).eventMass event) :
    FiniteDist.TVBound
      ((FiniteDist.independent (fun _ : Fin (attempts * bits) => FiniteDist.uniform (Fin 2))).map
        (draw bits attempts decode event fallback))
      (((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map decode).condition event hpos)
      (Real.exp (-(attempts : ℝ) *
        ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map decode).eventMass event)) := by
  rw [draw_law]
  exact FiniteDist.cappedCondition_tv _ event hpos (CanonicalMoments.pointLaw fallback) attempts

end
end AFT.FiniteConditionProgram

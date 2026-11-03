import AFT.OrderedSeedFactors
import AFT.FiniteSeedExpansion

/-! # Executable finite branch expansion of literal input seed variables -/
namespace AFT.RationalNumerics
variable {State Branch Code : Type*}

def orderedSeedExpansion (base : State → Code) (linear : State → State)
    (choices : State → List Branch) (higher : State → Branch → State) : ℕ → State → OrderedSeedTable Code
  | 0,state => [⟨1,[base state]⟩]
  | steps+1,state => orderedSeedExpansion base linear choices higher steps (linear state) ++
      (choices state).flatMap (fun branch => orderedSeedExpansion base linear choices higher steps (higher state branch))

/-- Fixed-depth expansion has fixed exponential branching, with no
comparison of real input kernels or real coefficients. -/
theorem orderedSeedExpansion_length (base : State → Code) (linear : State → State)
    (choices : State → List Branch) (higher : State → Branch → State)
    (bound : ℕ) (hbound : ∀ state,(choices state).length ≤ bound) (steps : ℕ) (state : State) :
    (orderedSeedExpansion base linear choices higher steps state).length ≤ (1+bound)^steps := by
  induction steps generalizing state with
  | zero => simp [orderedSeedExpansion]
  | succ steps ih =>
    simp only [orderedSeedExpansion,List.length_append,List.length_flatMap]
    have hs : ((choices state).map (fun branch =>
        (orderedSeedExpansion base linear choices higher steps (higher state branch)).length)).sum ≤
        (choices state).length*(1+bound)^steps := by
      induction choices state with
      | nil => simp
      | cons branch rest hrest =>
        simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,one_mul,add_comm] using
          Nat.add_le_add (ih (higher state branch)) hrest
    calc
      _ ≤ (1+bound)^steps+(choices state).length*(1+bound)^steps := Nat.add_le_add (ih _) hs
      _ ≤ (1+bound)^steps+bound*(1+bound)^steps :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (hbound state)) _
      _ = (1+bound)^(steps+1) := by rw [pow_succ];ring

noncomputable section
open RepresentedPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {Seed : Type*}

theorem OrderedSeedTable.interpret_flatMap {Index : Type*} (decode : Code → Seed)
    (list : List Index) (table : Index → OrderedSeedTable Code) :
    OrderedSeedTable.interpret decode (list.flatMap table)=(list.map (fun index => (table index).interpret decode)).sum := by
  induction list with
  | nil => simp [OrderedSeedTable.interpret]
  | cons index list ih => simp only [List.flatMap_cons,OrderedSeedTable.interpret_append,List.map_cons,List.sum_cons,ih]

/-- An explicitly enumerated branch list realizes the exact finite seed
expansion whenever it lists each original branch exactly once. -/
theorem orderedSeedExpansion_interpret (decode : Code → Seed) (base : State → Code) (linear : State → State)
    (choices : State → List Branch) (branches : State → Finset Branch) (higher : State → Branch → State)
    (hchoices : ∀ state,(choices state).Nodup ∧ (choices state).toFinset=branches state)
    (steps : ℕ) (state : State) :
    (orderedSeedExpansion base linear choices higher steps state).interpret decode=
      seedExpansion (decode ∘ base) linear branches higher steps state := by
  induction steps generalizing state with
  | zero => simp [orderedSeedExpansion,OrderedSeedTable.interpret,OrderedSeedTerm.interpret,seedExpansion]
  | succ steps ih =>
    rw [orderedSeedExpansion,OrderedSeedTable.interpret_append,OrderedSeedTable.interpret_flatMap,ih,seedExpansion]
    congr 1
    have hp := List.perm_of_nodup_nodup_toFinset_eq (hchoices state).1 (Finset.nodup_toList (branches state))
      (by simpa only [Finset.toList_toFinset] using (hchoices state).2)
    rw [(hp.map (fun branch =>
      (orderedSeedExpansion base linear choices higher steps (higher state branch)).interpret decode)).sum_eq,
      Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro branch _
    exact ih _

end
end AFT.RationalNumerics

import AFT.OrderedSeedExpansion

/-! # Exact simulation of a literal seed expansion by a finite program -/
namespace AFT.RationalNumerics
open RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- State decoding and branch decoding may change dependent coordinate
representations. Only reachable valid states are required to simulate. -/
theorem orderedSeedExpansion_simulation {State Target Branch TargetBranch Code Seed : Type*}
    (decode : Code → Seed) (stateDecode : State → Target) (branchDecode : Branch → TargetBranch)
    (base : State → Code) (linear : State → State) (choices : State → List Branch) (higher : State → Branch → State)
    (targetBase : Target → Seed) (targetLinear : Target → Target)
    (targetChoices : Target → Finset TargetBranch) (targetHigher : Target → TargetBranch → Target)
    (good : State → Prop)
    (hbase : ∀ state,good state → decode (base state)=targetBase (stateDecode state))
    (hlinear : ∀ state,good state → good (linear state) ∧ stateDecode (linear state)=targetLinear (stateDecode state))
    (hchoices : ∀ state,good state → ((choices state).map branchDecode).Nodup ∧
      ((choices state).map branchDecode).toFinset=targetChoices (stateDecode state))
    (hhigher : ∀ state,good state → ∀ branch,branch∈choices state → good (higher state branch) ∧
      stateDecode (higher state branch)=targetHigher (stateDecode state) (branchDecode branch))
    (steps : ℕ) (state : State) (hs : good state) :
    (orderedSeedExpansion base linear choices higher steps state).interpret decode=
      seedExpansion targetBase targetLinear targetChoices targetHigher steps (stateDecode state) := by
  induction steps generalizing state with
  | zero =>
    simp only [orderedSeedExpansion,OrderedSeedTable.interpret,OrderedSeedTerm.interpret,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil,mul_one,
      Rat.cast_one,one_smul,add_zero,seedExpansion]
    rw [hbase state hs]
  | succ steps ih =>
    rw [orderedSeedExpansion,OrderedSeedTable.interpret_append,OrderedSeedTable.interpret_flatMap,
      ih _ (hlinear state hs).1,(hlinear state hs).2,seedExpansion]
    congr 1
    have hmap : (choices state).map (fun branch =>
        (orderedSeedExpansion base linear choices higher steps (higher state branch)).interpret decode)=
        (choices state).map (fun branch => seedExpansion targetBase targetLinear targetChoices targetHigher steps
          (targetHigher (stateDecode state) (branchDecode branch))) := by
      apply List.map_congr_left
      intro branch hb
      rw [ih _ (hhigher state hs branch hb).1,(hhigher state hs branch hb).2]
    rw [hmap]
    have hperm := List.perm_of_nodup_nodup_toFinset_eq (hchoices state hs).1
      (Finset.nodup_toList (targetChoices (stateDecode state)))
      (by simpa only [Finset.toList_toFinset] using (hchoices state hs).2)
    have hh := (hperm.map (fun branch => seedExpansion targetBase targetLinear targetChoices targetHigher steps
      (targetHigher (stateDecode state) branch))).sum_eq
    simpa only [List.map_map,Function.comp_def,Finset.sum_map_toList] using hh

end
end AFT.RationalNumerics

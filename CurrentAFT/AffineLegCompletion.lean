import CurrentAFT.AffineLegCoreErasure
import CurrentAFT.RefinedPublicOutput
import CurrentAFT.PublicAuxiliaryFubini

/-!
# Real public chart completion of a fixed leg core

The complete chart is sampled before, and independently of, both protected
source coordinates.  The retained second coordinate is reused in the
attachment.  The auxiliary activation bit of the old reference core is
ignored by this sampler.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge ActualPublicCharge DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

local instance completionFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

local instance completionPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

theorem mix_map_comm {A B O : Type*} [Fintype A] [Fintype B] [Fintype O]
    (first : FiniteDist A) (second : FiniteDist B) (value : A → B → O) :
    first.mix (fun a => second.map (value a)) =
      second.mix (fun b => first.map (fun a => value a b)) := by
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.map_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

def completionLaw (security : ℕ) (primary : Palette security) (seed : PublicSeed security) :
    FiniteDist (Bool × Chart (ZMod (Parameters.modulus security))) :=
  (currentLaw security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num)).joint

def evaluatePrimary (security : ℕ) (chart : Bool × Chart (ZMod (Parameters.modulus security)))
    (first second : Scalar security) : Palette security :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
    (feature ((first.val : ℤ) : ZMod (Parameters.modulus security))
      ((second.val : ℤ) : ZMod (Parameters.modulus security)) chart.2)

def evaluateTriple (security : ℕ) (root : ℤ) (primary : Palette security) (seed : LegCore security)
    (chart : Bool × Chart (ZMod (Parameters.modulus security))) (first second : Scalar security) :
    Fin 3 → Palette security :=
  PhysicalBlockTensors.tripleEquiv.symm
    (pairProjection security (publicShift security primary seed.1 - second.val)
      (evaluatePrimary security chart first second),
      shiftEquiv security (root + second.val) seed.2)

/-- The positive complete chart law is sampled independently of the entire
protected first/second pair.  Both coordinates are subsequently drawn from
their original clipped Gaussian law. -/
def completedTriple (security : ℕ) (root : ℤ) (primary : Palette security) (seed : LegCore security) :
    FiniteDist (Fin 3 → Palette security) :=
  (completionLaw security primary seed.1).mix (fun chart =>
    (scalarLaw security).mix (fun first =>
      (scalarLaw security).map (evaluateTriple security root primary seed chart first)))

theorem evaluatedPair_chart_map (security : ℕ) (primary : Palette security) (seed : PublicSeed security)
    (first second : Scalar security) :
    evaluatedPair security (publicShift security primary seed)
      (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
      primary first second =
      (completionLaw security primary seed).map (fun chart =>
        pairProjection security (publicShift security primary seed - second.val)
          (evaluatePrimary security chart first second)) := by
  rw [evaluatedPair, evaluatedPrimary, FiniteDist.map_map]
  rfl

theorem completedTriple_sources_first (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) :
    completedTriple security root primary seed =
      (scalarLaw security).mix (fun second => (scalarLaw security).mix (fun first =>
        (evaluatedPair security (publicShift security primary seed.1)
          (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed.1)
          primary first second).map (fun pair =>
            PhysicalBlockTensors.tripleEquiv.symm
              (pair, shiftEquiv security (root + second.val) seed.2)))) := by
  unfold completedTriple
  rw [FiniteDist.mix_comm]
  simp_rw [mix_map_comm (completionLaw security primary seed.1) (scalarLaw security)]
  rw [FiniteDist.mix_comm]
  apply congrArg (FiniteDist.mix (scalarLaw security))
  funext second
  apply congrArg (FiniteDist.mix (scalarLaw security))
  funext first
  rw [evaluatedPair_chart_map, FiniteDist.map_map]
  rfl

/-- Fixed roots and all other public core data.  This identity therefore
remains valid inside an arbitrary clipped and charged public multiplier. -/
theorem completedTriple_reference (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) :
    completedTriple security root primary seed =
      (activationLaw security).mix (fun flag =>
        RefinedPublicOutput.triple security root primary
          (setMarked security seed.1 flag, seed.2)) := by
  rw [completedTriple_sources_first]
  trans (scalarLaw security).mix (fun second =>
    (activationLaw security).mix (fun flag =>
      (refinedPair security primary second (setMarked security seed.1 flag)).map
        (fun pair => PhysicalBlockTensors.tripleEquiv.symm
          (pair, shiftEquiv security (root + second.val) seed.2))))
  · apply congrArg (FiniteDist.mix (scalarLaw security))
    funext second
    rw [← FiniteDist.map_mix, fixed_seed_reference, FiniteDist.map_mix]
  · rw [FiniteDist.mix_comm]
    rfl

theorem completionLaw_setMarked (security : ℕ) (primary : Palette security)
    (seed : PublicSeed security) (flag : Bool) :
    completionLaw security primary (setMarked security seed flag) = completionLaw security primary seed := rfl

theorem completedTriple_setMarked (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) (flag : Bool) :
    completedTriple security root primary (setMarked security seed.1 flag, seed.2) =
      completedTriple security root primary seed := rfl

end
end CurrentAFT.AffineFlagCalibration

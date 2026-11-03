import CurrentAFT.AffineLegPair

/-!
# Fixed-public-core comparison with the protected reference pair

The real public flag has probability one half.  The auxiliary `marked` bit
in the reference seed has probability `activation`, which also includes the
independent protected first scalar's zero atom.  They are never identified.
The equalities hold with coin, anchor index, blur and the second scalar fixed.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge DiffuseProfiles
open scoped BigOperators Classical

noncomputable section

theorem baseline_second_clear (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (second : Scalar security) :
    2 + |baseline - second.val| < (Parameters.modulus security : ℤ) := by
  have hs := InwardAnchor.scalar_bound security second
  have hroom := leg_trimmed_room security
  have hB : 0 < Parameters.sourceCutoff security := InwardAnchor.sourceCutoff_pos security
  have ha := (abs_sub baseline second.val).trans (add_le_add hbaseline hs)
  omega

theorem evaluatedPair_weight (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) (pair : Palette security × Palette security) :
    (evaluatedPair security baseline hbaseline mark first second).weight pair =
      if first.val = 0 then
        (1 / 2 : ℝ) * TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
          (baseline - second.val) pair.1 pair.2 +
        (1 / 2 : ℝ) * (if pairProjection security (baseline - second.val) mark = pair then 1 else 0)
      else TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
        (baseline - second.val) pair.1 pair.2 := by
  let sliceLaw := TrimmedSlice.finiteLaw (Parameters.modulus security) 1
    (baseline - second.val) (by norm_num) (baseline_second_clear security baseline hbaseline second)
  have hslice (color : Palette security) : sliceLaw.weight color =
      if color ∈ TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val) then
        ((TrimmedSlice.paletteSlice (Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0 := by
    dsimp only [sliceLaw, TrimmedSlice.finiteLaw, FiniteDist.uniformSafe]
    split_ifs <;> rfl
  have hdiffuse := uniformSlice_pair security (baseline - second.val)
    (baseline_second_clear security baseline hbaseline second) pair.1 pair.2
  change (sliceLaw.map (fun x => (x, companion security (baseline - second.val) x))).weight
    (pair.1, pair.2) = _ at hdiffuse
  rw [graph_map_weight] at hdiffuse
  have hpoint : (if pair.1 = mark then (1 : ℝ) else 0) *
      (if companion security (baseline - second.val) pair.1 = pair.2 then 1 else 0) =
      if pairProjection security (baseline - second.val) mark = pair then 1 else 0 := by
    rcases pair with ⟨a, b⟩
    by_cases ha : a = mark
    · subst a
      simp only [pairProjection, Prod.mk.injEq, true_and]
      split_ifs <;> norm_num
    · simp [ha, pairProjection, Ne.symm ha]
  change ((evaluatedPrimary security baseline hbaseline mark first second).map
    (fun x => (x, companion security (baseline - second.val) x))).weight (pair.1, pair.2) = _
  rw [graph_map_weight, evaluatedPrimary_weight]
  rw [hslice pair.1] at hdiffuse
  split_ifs at hdiffuse hpoint ⊢ <;>
    simp only [mul_zero, mul_one, add_zero, zero_add] at * <;> linarith

/-- Averaging the protected first scalar, with the public map still drawn
independently, produces the actual activation probability. -/
theorem averaged_evaluatedPair_weight (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (second : Scalar security) (pair : Palette security × Palette security) :
    ((scalarLaw security).mix (fun first => evaluatedPair security baseline hbaseline mark first second)).weight pair =
      (1 - activation security) * TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
        (baseline - second.val) pair.1 pair.2 +
      activation security * (if pairProjection security (baseline - second.val) mark = pair then 1 else 0) := by
  let zero := GaussianSource.windowZero (Parameters.sourceCutoff security - 1)
  have hz (first : Scalar security) : first.val = 0 ↔ first = zero := by
    constructor
    · intro he
      exact Subtype.ext he
    · rintro rfl
      rfl
  let d := TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
    (baseline - second.val) pair.1 pair.2
  let m : ℝ := if pairProjection security (baseline - second.val) mark = pair then 1 else 0
  have hrow (first : Scalar security) :
      (evaluatedPair security baseline hbaseline mark first second).weight pair =
        d + if first = zero then (1 / 2 : ℝ) * (m - d) else 0 := by
    rw [evaluatedPair_weight]
    by_cases hf : first.val = 0
    · simp only [if_pos hf, if_pos ((hz first).mp hf)]
      dsimp [d, m]
      ring
    · simp only [if_neg hf, if_neg (mt (hz first).mpr hf), add_zero]
      rfl
  rw [FiniteDist.mix_weight]
  simp_rw [hrow, mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  dsimp only [d, m, zero, activation]
  split_ifs <;> ring

def setMarked (security : ℕ) (seed : PublicSeed security) (flag : Bool) : PublicSeed security :=
  { seed with marked := flag }

theorem publicShift_setMarked (security : ℕ) (primary : Palette security)
    (seed : PublicSeed security) (flag : Bool) :
    publicShift security primary (setMarked security seed flag) = publicShift security primary seed := rfl

theorem markedPoint_setMarked (security : ℕ) (primary : Palette security) (second : Scalar security)
    (seed : PublicSeed security) (flag : Bool) :
    markedPoint security primary second (setMarked security seed flag) =
      markedPoint security primary second seed := rfl

theorem pairProjection_mark (security : ℕ) (primary : Palette security) (second : Scalar security)
    (seed : PublicSeed security) :
    pairProjection security (publicShift security primary seed - second.val) primary =
      (primary, markedPoint security primary second seed) := by
  have hc := markedLaw_charge security primary second seed
    (primary, markedPoint security primary second seed)
    (by rw [markedLaw_weight]; simp)
  have hs : companion security (publicShift security primary seed - second.val) primary =
      markedPoint security primary second seed := companion_of_integer_sum security _ _ _ (by
        dsimp only at hc
        omega)
  exact congrArg (fun color => (primary, color)) hs

theorem refinedPair_setMarked_true (security : ℕ) (primary : Palette security) (second : Scalar security)
    (seed : PublicSeed security) :
    refinedPair security primary second (setMarked security seed true) =
      markedLaw security primary second seed := rfl

theorem refinedPair_setMarked_false (security : ℕ) (primary : Palette security) (second : Scalar security)
    (seed : PublicSeed security) :
    refinedPair security primary second (setMarked security seed false) =
      diffuseLaw security primary second seed := rfl

/-- Pointwise in the entire public shift seed and the retained second
scalar.  Thus a multiplier depending on that core may be applied later. -/
theorem fixed_seed_reference (security : ℕ) (primary : Palette security)
    (seed : PublicSeed security) (second : Scalar security) :
    (scalarLaw security).mix (fun first => evaluatedPair security
      (publicShift security primary seed)
      (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
      primary first second) =
      (activationLaw security).mix (fun flag =>
        refinedPair security primary second (setMarked security seed flag)) := by
  ext pair
  rw [averaged_evaluatedPair_weight, FiniteDist.mix_weight, Fintype.sum_bool]
  simp only [refinedPair_setMarked_true, refinedPair_setMarked_false,
    activationLaw_true, activationLaw_false]
  rw [markedLaw_weight, pairProjection_mark]
  dsimp only [diffuseLaw]
  split_ifs <;> ring

end
end CurrentAFT.AffineFlagCalibration

import CurrentAFT.ActualPublicLegCharge
import AFT.Histogram

/-! # Exact public-seed disintegration of the actual protected pair law -/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical
noncomputable section
local instance disintegrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance disintegrationAnchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(InwardAnchor.anchorWidth_pos security).ne'⟩
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff

/-- The negative branch reverses the uniform anchor index. Both signs
therefore produce precisely the printed consecutive integer interval. -/
theorem signed_uniform_interval (width : ℕ) [NeZero width] (positive : Bool) (blur : ℤ) (kernel : ℤ → ℝ) :
    (FiniteDist.uniform (Fin width)).expectation (fun index =>
      kernel ((if positive then (width : ℤ) + index.val else -((width : ℤ) + index.val)) + blur)) =
      TrimmedSlice.intervalMixture (intervalStart positive width blur) width kernel := by
  unfold FiniteDist.expectation TrimmedSlice.intervalMixture
  simp only [FiniteDist.uniform_weight, Fintype.card_fin]
  refine Finset.sum_bij
    (fun index _ => (if positive then (width : ℤ) + index.val else -((width : ℤ) + index.val)) + blur) ?_ ?_ ?_ ?_
  · intro index _
    have hindex := index.isLt
    cases positive <;> simp only [Bool.false_eq_true, if_false, if_true, intervalStart, anchorInterval, Finset.mem_Ico] <;> omega
  · intro first _ second _ hequal
    apply Fin.ext
    cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hequal <;> omega
  · intro shift hshift
    have hwidth := (inferInstance : NeZero width).out
    cases positive
    · simp only [intervalStart, Bool.false_eq_true, if_false, anchorInterval, Finset.mem_Ico] at hshift
      let index : Fin width := ⟨(-shift + blur - width).toNat, by omega⟩
      refine ⟨index, Finset.mem_univ _, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      dsimp [index]
      omega
    · simp only [intervalStart, if_true, anchorInterval, Finset.mem_Ico] at hshift
      let index : Fin width := ⟨(shift - blur - width).toNat, by omega⟩
      refine ⟨index, Finset.mem_univ _, ?_⟩
      simp only [if_true]
      dsimp [index]
      omega
  · intro index _
    have hindex := index.isLt
    have hin : ((if positive then (width : ℤ) + index.val else -((width : ℤ) + index.val)) + blur) ∈
        anchorInterval (intervalStart positive width blur) width := by
      cases positive <;> simp only [Bool.false_eq_true, if_false, if_true, intervalStart, anchorInterval, Finset.mem_Ico] <;> omega
    rw [intervalAnchorLaw, if_pos hin]

theorem diffuse_index_average (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (coin : Bool) (blur : BlurSeed security) :
    (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
      diffuseLaw security primary scalar ⟨false, coin, index, blur⟩) =
        diffuseSeedPair security (positiveDirection security primary coin) (blur, scalar) := by
  ext pair
  rw [diffuseSeedPair_weight]
  change (FiniteDist.uniform (InwardAnchor.Index security)).expectation (fun index =>
    TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
      (publicShift security primary ⟨false, coin, index, blur⟩ - scalar.val) pair.1 pair.2) = _
  have h := signed_uniform_interval (Parameters.anchorWidth security) (positiveDirection security primary coin)
    (blur.1.val - blur.2.val) (fun shift => TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
      (shift - scalar.val) pair.1 pair.2)
  convert h using 1
  apply congrArg (FiniteDist.uniform (InwardAnchor.Index security)).expectation
  funext index
  congr 1
  unfold publicShift signedOffset offset
  ring


private theorem mix_comm {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (kernel : First → Second → FiniteDist Output) :
    first.mix (fun left => second.mix (kernel left)) =
      second.mix (fun right => first.mix (fun left => kernel left right)) := by
  ext output
  simp only [FiniteDist.mix_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  ring

private theorem prod_mix {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (kernel : First × Second → FiniteDist Output) :
    (first.prod second).mix kernel = first.mix (fun left => second.mix (fun right => kernel (left, right))) := by
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem marked_index_average (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (coin : Bool) (blur : BlurSeed security) :
    (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
      markedLaw security primary scalar ⟨true, coin, index, blur⟩) =
      ((fixedCoinLaw security primary coin (-scalar.val)
        (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)).map
          (shiftEquiv security (blur.1.val - blur.2.val))).map (fun companion => (primary, companion)) := by
  ext pair
  simp only [FiniteDist.mix_weight, markedLaw_weight, fixedCoinLaw, FiniteDist.map_map, FiniteDist.map_weight,
    markedPoint, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> rfl

theorem marked_average (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security) :
    (FiniteDist.uniform Bool).mix (fun coin =>
      (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
        (publicBlurLaw security).mix (fun blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩))) =
          markedPairAt security primary scalar := by
  have hswap (coin : Bool) := mix_comm (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)
    (fun index blur => markedLaw security primary scalar ⟨true, coin, index, blur⟩)
  simp_rw [hswap]
  rw [mix_comm (FiniteDist.uniform Bool) (publicBlurLaw security)]
  simp_rw [marked_index_average]
  unfold markedPairAt markedCompanionAt shiftedAnchorLaw
  rw [FiniteDist.map_mix]
  apply congrArg (publicBlurLaw security).mix
  funext blur
  rw [FiniteDist.map_mix, FiniteDist.map_mix]

theorem diffuse_average (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security) :
    (FiniteDist.uniform Bool).mix (fun coin =>
      (FiniteDist.uniform (InwardAnchor.Index security)).mix (fun index =>
        (publicBlurLaw security).mix (fun blur => diffuseLaw security primary scalar ⟨false, coin, index, blur⟩))) =
          diffusePairAt security primary scalar := by
  have hswap (coin : Bool) := mix_comm (FiniteDist.uniform (InwardAnchor.Index security)) (publicBlurLaw security)
    (fun index blur => diffuseLaw security primary scalar ⟨false, coin, index, blur⟩)
  simp_rw [hswap, diffuse_index_average]
  rfl

/-- Averaging only the source-independent seed gives exactly the original
protected pair experiment, for every primary control and protected scalar. -/
theorem pairAt_disintegration (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security) :
    (seedLaw security).mix (refinedPair security primary scalar) = pairAt security primary scalar := by
  rw [seedLaw, FiniteDist.mix_map]
  simp only [prod_mix, seedEquiv, Equiv.coe_fn_symm_mk]
  ext pair
  rw [FiniteDist.mix_weight, Fintype.sum_bool]
  simp only [refinedPair, Bool.false_eq_true, if_false, if_true]
  rw [marked_average, diffuse_average, activationLaw_true, activationLaw_false]
  change activation security * (markedPairAt security primary scalar).weight pair +
    (1 - activation security) * (diffusePairAt security primary scalar).weight pair =
      (1 - activation security) * (diffusePairAt security primary scalar).weight pair +
        activation security * (markedPairAt security primary scalar).weight pair
  ring

end
end CurrentAFT.ActualPublicLegCharge

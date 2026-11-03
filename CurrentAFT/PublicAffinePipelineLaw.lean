import CurrentAFT.PublicAffinePipeline

/-! Gaussian output laws of the literal integer arrays. The public placement
is held fixed throughout calibration and rejection, then averaged once. -/
namespace CurrentAFT.PublicAffinePipeline
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw

def gaussianChannel (security : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  CurrentHiddenSourceTransport.hiddenGaussianOutput security (fun input =>
    (FiniteDist.uniform Unit).map (fun _ index =>
      (((CurrentBinaryAffineEmitter.matrix security data).mulVec input index+
        CurrentBinaryAffineEmitter.offset security data index : ℤ) : ZMod (Parameters.modulus security))))

theorem addWork_channel (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    gaussianChannel security (addWork security extra data) = gaussianChannel security data := by
  simp only [gaussianChannel, addWork_matrix, addWork_offset]

theorem forLayout_channel (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    gaussianChannel security (forLayout security order producer layout word) =
      NumericalAffineTransport.gaussianChannel security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample) := by
  unfold gaussianChannel
  rw [forLayout_matrix, forLayout_offset]
  rfl

def fixedGaussian (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) : FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (CurrentMaterializedCompletion.Tapes security)).mix
    (fun word => gaussianChannel security (forLayout security order producer layout word))

theorem fixedGaussian_eq (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) :
    fixedGaussian security order producer layout =
      NumericalAffineTransport.gaussianOutput security layout.layout
        (CurrentMaterializedCompletion.publicLaw security order (producer layout).value) := by
  simp only [fixedGaussian, forLayout_channel, NumericalAffineTransport.gaussianOutput,
    CurrentMaterializedCompletion.publicLaw, FiniteDist.mix_map]

def runGaussian (security order : ℕ) (producer : Producer security order) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (PublicBitTapes.Tapes security)).mix
    (fun word => gaussianChannel security (run security order producer word))

def fairGaussian (security order : ℕ) (producer : Producer security order) :
    FiniteDist (CurrentZeroFiber.Word security) :=
  (FiniteDist.uniform (Fin (PublicBitTapes.current security).bits → Fin 2)).mix
    (fun word => gaussianChannel security (fairBitRun security order producer word))

theorem fairGaussian_eq (security order : ℕ) (producer : Producer security order) :
    fairGaussian security order producer = runGaussian security order producer := by
  unfold fairGaussian fairBitRun runGaussian
  rw [← FiniteDist.mix_map _ (PublicBitTapes.current security).equiv
    (fun word => gaussianChannel security (run security order producer word)), PublicBitTapes.uniform_decode]

theorem product_mix {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (channel : First × Second → FiniteDist Output) :
    (first.prod second).mix channel = first.mix (fun a => second.mix (fun b => channel (a,b))) := by
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem runGaussian_eq (security order : ℕ) (producer : Producer security order) :
    runGaussian security order producer =
      (FiniteDist.uniform (CurrentLayoutDraw.Tape security security)).mix
        (fun word => fixedGaussian security order producer (CurrentLayoutDraw.draw security security word).value) := by
  rw [runGaussian, FiniteDist.uniform_product, product_mix]
  simp only [run, addWork_channel, fixedGaussian]

theorem gaussian_accuracy (security order : ℕ) (producer : Producer security order) (error : ℝ)
    (hfixed : ∀ layout, (fixedGaussian security order producer layout).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ error) :
    (fairGaussian security order producer).totalVariation (CurrentZeroFiber.uniformFiber security) ≤ error := by
  rw [fairGaussian_eq, runGaussian_eq]
  have h := FiniteDist.TVBound.mix_right (FiniteDist.uniform (CurrentLayoutDraw.Tape security security))
    (first := fun word => fixedGaussian security order producer (CurrentLayoutDraw.draw security security word).value)
    (second := fun _ => CurrentZeroFiber.uniformFiber security)
    (fun word => (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr (hfixed _))
  rw [FiniteDist.mix_const] at h
  exact (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp h

end
end CurrentAFT.PublicAffinePipeline

import CurrentAFT.BinaryPublicBitCodec
import CurrentAFT.BinaryPublicBitSizes
import CurrentAFT.PublicBitResources

/-! The literal flat random tape is copied and split into stored public
buffers. All lengths are computed once by the counted preparation program. -/
namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current

variable (security : ℕ) (sizes : BinaryPublicBitSizes.Data) (correct : sizes=BinaryPublicBitSizes.current security)

def edge : Codec (CurrentPublicSeedDraw.EdgeTape security security) :=
  bitsCast sizes.edge _ (by rw [correct]; exact BinaryPublicBitSizes.edge_value security)

def safe : Codec (CurrentSafeDraw.Tape security security) :=
  bitsCast sizes.safe _ (by rw [correct]; exact BinaryPublicBitSizes.safe_value security)

def control : Codec (ControlTape security security) :=
  prod (bitsCast sizes.control _ (by rw [correct]; exact BinaryPublicBitSizes.control_value security))
    (safe security sizes correct)

def seed : Codec (CurrentPublicSeedDraw.Tape security security) :=
  prod (bitsCast sizes.activation _ (by rw [correct]; simpa only [Nat.add_assoc] using BinaryPublicBitSizes.activation_value security))
    (prod flag (prod (bitsCast sizes.anchor _ (by rw [correct]; exact BinaryPublicBitSizes.anchor_value security))
      (prod (edge security sizes correct) (edge security sizes correct))))

def leg : Codec (LegTape security security) :=
  prod (seed security sizes correct) (safe security sizes correct)

def withCount {Index State : Type*} {count other : ℕ} (same : count=other)
    (ordering : Fin other ≃ Index) (codec : Codec State) : Codec (Index → State) :=
  indexed ((finCongr same).trans ordering) codec

def core : Codec (CurrentCoreProposal.Tapes security security) :=
  prod (prod (prod (prod
    (withCount (count:=sizes.dimensions.controls) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.controlsEquiv security) (control security sizes correct))
    (withCount (count:=sizes.dimensions.legs) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.legEquiv security) (leg security sizes correct)))
    (withCount (count:=sizes.dimensions.colors) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
      (CurrentProposalDimensions.queueEquiv security) (safe security sizes correct)))
    (bitsCast sizes.body _ (by rw [correct]; exact BinaryPublicBitSizes.body_value security)))
    (bitsCast sizes.endpoint _ (by rw [correct]; exact BinaryPublicBitSizes.endpoint_value security))

def charts : Codec (CurrentChartsDraw.Tapes security security) :=
  withCount (count:=sizes.dimensions.legs) (by rw [correct,BinaryPublicBitSizes.dimensions_value])
    (CurrentProposalDimensions.legEquiv security)
    (prod flag (bitsCast sizes.chart _ (by rw [correct]; exact BinaryPublicBitSizes.chart_value security)))

def completion : Codec (CurrentPublicCompletion.Tapes security security security) :=
  prod (charts security sizes correct) (edge security sizes correct)

def rejection : Codec (CappedPublicRejection.Tapes security) :=
  withCount (count:=sizes.retries.count) (by rw [correct,BinaryPublicBitSizes.retries_value])
    (Equiv.refl (Fin (BinaryRejectionCap.current security).count))
    (prod (core security sizes correct) (bits security))

def materialized : Codec (CurrentMaterializedCompletion.Tapes security) :=
  prod (rejection security sizes correct) (completion security sizes correct)

def codec : Codec (PublicBitTapes.Tapes security) :=
  prod (bitsCast sizes.body _ (by rw [correct]; exact BinaryPublicBitSizes.body_value security))
    (materialized security sizes correct)

private theorem prod_encoding {First Second : Type*} (first : Codec First) (second : Codec Second) :
    (prod first second).encoding=first.encoding.prod second.encoding := rfl

private theorem withCount_encoding {Index State : Type*} {count other : ℕ} (same : count=other)
    (ordering : Fin other ≃ Index) (code : Codec State) :
    (withCount same ordering code).encoding=code.encoding.indexed ordering := by
  subst other
  rfl

theorem codec_encoding : (codec security sizes correct).encoding=PublicBitTapes.current security := by
  simp only [codec,materialized,rejection,completion,charts,core,leg,seed,control,safe,edge,
    prod_encoding,withCount_encoding,bitsCast_encoding,flag_encoding]
  unfold PublicBitTapes.current
  rfl

def current (security : ℕ) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    CountedValue (PublicBitTapes.Tapes security) :=
  let sizes := BinaryPublicBitSizes.current security
  let decoded := decodeAs (codec security sizes rfl) (PublicBitTapes.current security)
    (codec_encoding security sizes rfl) word
  ⟨decoded.value,sizes.work+decoded.work+1⟩

theorem current_value (security : ℕ) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (current security word).value=(PublicBitTapes.current security).equiv word :=
  decodeAs_value (codec security (BinaryPublicBitSizes.current security) rfl) (PublicBitTapes.current security)
    (codec_encoding security (BinaryPublicBitSizes.current security) rfl) word

noncomputable section
private theorem of_bound (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (bound : ∀ security, resource security≤polynomial.eval security) : UniformPolynomialBound resource := ⟨polynomial,bound⟩

attribute [local irreducible] UniformPolynomialBound

def workBound (security : ℕ) : ℕ :=
  (BinaryPublicBitSizes.current security).work+
    decodeBound (codec security (BinaryPublicBitSizes.current security) rfl)+1

theorem current_bound (security : ℕ) (word : Fin (PublicBitTapes.current security).bits → Fin 2) :
    (current security word).work≤workBound security := by
  have h := decodeAs_work (codec security (BinaryPublicBitSizes.current security) rfl) (PublicBitTapes.current security)
    (codec_encoding security (BinaryPublicBitSizes.current security) rfl) word
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) 1

end
end CurrentAFT.BinaryPublicBitDecode

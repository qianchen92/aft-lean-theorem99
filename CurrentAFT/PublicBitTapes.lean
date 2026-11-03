import CurrentAFT.CurrentMaterializedCompletionLaw
import CurrentAFT.CurrentLayoutDraw

/-! Explicit flat fair-bit tapes for all current public sampling stages.
Products split consecutive bits; indexed families use the native role
numberings, never an arbitrarily chosen finite equivalence. -/
namespace CurrentAFT.PublicBitTapes
open AFT CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current

structure Encoding (State : Type*) where
  bits : ℕ
  equiv : (Fin bits → Fin 2) ≃ State

def bits (count : ℕ) : Encoding (Fin count → Fin 2) := ⟨count, Equiv.refl _⟩

def flag : Encoding Bool := ⟨1,
  { toFun := fun word => finTwoEquiv (word 0)
    invFun := fun value _ => finTwoEquiv.symm value
    left_inv := by intro word; funext index; have h : index=0 := Subsingleton.elim _ _; subst index; simp
    right_inv := fun _ => finTwoEquiv.apply_symm_apply _ }⟩

def split (first second : ℕ) : (Fin (first+second) → Fin 2) ≃
    ((Fin first → Fin 2) × (Fin second → Fin 2)) where
  toFun word := (fun index => word (finSumFinEquiv (.inl index)), fun index => word (finSumFinEquiv (.inr index)))
  invFun pair index := Sum.elim pair.1 pair.2 (finSumFinEquiv.symm index)
  left_inv word := by
    funext index
    obtain ⟨left | right, rfl⟩ := finSumFinEquiv.surjective index <;> simp
  right_inv pair := by
    apply Prod.ext <;> funext index <;> simp

def Encoding.prod {First Second : Type*} (first : Encoding First) (second : Encoding Second) : Encoding (First×Second) :=
  ⟨first.bits+second.bits, (split first.bits second.bits).trans (Equiv.prodCongr first.equiv second.equiv)⟩

def Encoding.indexed {Index State : Type*} {count : ℕ} (ordering : Fin count ≃ Index)
    (encoding : Encoding State) : Encoding (Index → State) :=
  ⟨count*encoding.bits, (FiniteConditionProgram.groupBits count encoding.bits).trans
    (Equiv.arrowCongr ordering encoding.equiv)⟩

def edge (security precision : ℕ) : Encoding (CurrentPublicSeedDraw.EdgeTape security precision) :=
  bits (AFT.RationalNumerics.windowTicketBits (DiffuseProfiles.edgeCutoff security) precision)

def safe (security precision : ℕ) : Encoding (CurrentSafeDraw.Tape security precision) :=
  bits (precision+(CurrentReferenceDraw.counts security).safe+1)

def control (security precision : ℕ) : Encoding (ControlTape security precision) :=
  (bits (precision+(PublicParameterProgram.modulus security).count+1)).prod (safe security precision)

def seed (security precision : ℕ) : Encoding (CurrentPublicSeedDraw.Tape security precision) :=
  (bits (precision+2+1)).prod (flag.prod
    ((bits (precision+(CurrentAnchorIndexDraw.width security).count+1)).prod
      ((edge security precision).prod (edge security precision))))

def leg (security precision : ℕ) : Encoding (LegTape security precision) :=
  (seed security precision).prod (safe security precision)

def core (security precision : ℕ) : Encoding (CurrentCoreProposal.Tapes security precision) :=
  ((((control security precision).indexed (CurrentProposalDimensions.controlsEquiv security)).prod
      ((leg security precision).indexed (CurrentProposalDimensions.legEquiv security))).prod
    ((safe security precision).indexed (CurrentProposalDimensions.queueEquiv security))).prod
      (bits ((CurrentProposalDimensions.current security).body*precision)) |>.prod
      (bits ((CurrentProposalDimensions.current security).dimension*precision))

def charts (security precision : ℕ) : Encoding (CurrentChartsDraw.Tapes security precision) :=
  (flag.prod (bits (precision+Parameters.modulus security*(Parameters.modulus security*Parameters.modulus security)+1))).indexed
    (CurrentProposalDimensions.legEquiv security)

def completion (security : ℕ) : Encoding (CurrentPublicCompletion.Tapes security security security) :=
  (charts security security).prod (edge security security)

def rejection (security : ℕ) : Encoding (CappedPublicRejection.Tapes security) :=
  ((core security security).prod (bits security)).indexed (Equiv.refl (Fin (BinaryRejectionCap.current security).count))

def materialized (security : ℕ) : Encoding (CurrentMaterializedCompletion.Tapes security) :=
  (rejection security).prod (completion security)

abbrev Tapes (security : ℕ) := CurrentLayoutDraw.Tape security security × CurrentMaterializedCompletion.Tapes security

def current (security : ℕ) : Encoding (Tapes security) :=
  (bits ((CurrentProposalDimensions.current security).body*security)).prod (materialized security)

noncomputable section
open scoped Classical

theorem uniform_decode {State : Type*} [Fintype State] [Nonempty State] (encoding : Encoding State) :
    (FiniteDist.uniform (Fin encoding.bits → Fin 2)).map encoding.equiv = FiniteDist.uniform State :=
  FiniteDist.uniform_map_equiv encoding.equiv

theorem current_uniform (security : ℕ) :
    (FiniteDist.uniform (Fin (current security).bits → Fin 2)).map (current security).equiv =
      (FiniteDist.uniform (CurrentLayoutDraw.Tape security security)).prod
        (FiniteDist.uniform (CurrentMaterializedCompletion.Tapes security)) := by
  rw [uniform_decode, FiniteDist.uniform_product]

end
end CurrentAFT.PublicBitTapes

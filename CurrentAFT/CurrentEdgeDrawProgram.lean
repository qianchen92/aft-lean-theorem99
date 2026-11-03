import CurrentAFT.CurrentWindowDraw
import AFT.BinaryCounterDivision

/-! The closing-edge sampler includes its actual public cutoff generation. -/

namespace CurrentAFT.CurrentEdgeDrawProgram

open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def cutoffProgram (security : ℕ) : CounterDivisionResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let trimmed := differenceCounter square.count 1
  let result := divideCounter trimmed.count 2
  ⟨result.quotient, result.remainder, base.work + square.work + trimmed.work + result.work + 4⟩

theorem cutoff_value (security : ℕ) : (cutoffProgram security).quotient = DiffuseProfiles.edgeCutoff security := by
  simp only [cutoffProgram, (divideCounter_value _ 2 (by decide)).1, differenceCounter_value,
    powerCounter_value, addCounter_value, DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]

def cutoffWork (security : ℕ) : ℕ :=
  2 * security + 1 + powerCounterWork (security + 2) 2 + (2 * (security + 2) ^ 2 + 1) +
    500 * ((security + 2) ^ 2 + 4) ^ 2 + 4

theorem cutoff_work (security : ℕ) : (cutoffProgram security).work ≤ cutoffWork security := by
  have hp := powerCounter_work (security + 2) 2
  have ht := differenceCounter_work ((security + 2) ^ 2) 1
  have hd := divideCounter_work ((security + 2) ^ 2 - 1) 2 (by decide)
  have hd' : (divideCounter ((security + 2) ^ 2 - 1) 2).work ≤
      500 * ((security + 2) ^ 2 + 4) ^ 2 := hd.trans (by gcongr; exact Nat.sub_le _ _)
  simp only [cutoffProgram, powerCounter_value, addCounter_value, differenceCounter_value, addCounter_work, cutoffWork]
  omega

def castWindow {first second : ℕ} (h : first = second) (result : CountedValue (Window first)) : CountedValue (Window second) :=
  ⟨h ▸ result.value, result.work⟩

theorem cast_draw (security first second bits : ℕ) (h : first = second)
    (word : Fin (windowTicketBits second bits) → Fin 2) :
    castWindow h (CurrentWindowDraw.draw security first bits
      (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) h.symm) word)) =
      CurrentWindowDraw.draw security second bits word := by
  subst second
  rfl

def draw (security bits : ℕ) (word : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    CountedValue (Window (DiffuseProfiles.edgeCutoff security)) :=
  let cutoff := cutoffProgram security
  have hc : cutoff.quotient = DiffuseProfiles.edgeCutoff security := cutoff_value security
  let result := CurrentWindowDraw.draw security cutoff.quotient bits
    (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) hc.symm) word)
  let converted := castWindow hc result
  ⟨converted.value, cutoff.work + converted.work + 2⟩

theorem draw_value (security bits : ℕ) (word : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    (draw security bits word).value = WindowGaussianSampler.draw security (DiffuseProfiles.edgeCutoff security) bits word := by
  change (castWindow (cutoff_value security) (CurrentWindowDraw.draw security (cutoffProgram security).quotient bits
    (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) (cutoff_value security).symm) word))).value = _
  rw [cast_draw, CurrentWindowDraw.draw_value]

def workBound (security bits : ℕ) : ℕ :=
  cutoffWork security + CurrentWindowDraw.workBound security (DiffuseProfiles.edgeCutoff security) bits + 2

theorem draw_work (security bits : ℕ) (word : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    (draw security bits word).work ≤ workBound security bits := by
  have hc := cutoff_work security
  have he : DiffuseProfiles.edgeCutoff security ≤ (security + 2) ^ 2 :=
    (Nat.div_le_self (Parameters.sourceCutoff security - 1) 2).trans
      (by simpa only [Parameters.sourceCutoff, Parameters.base] using Nat.sub_le (Parameters.sourceCutoff security) 1)
  have hd := CurrentWindowDraw.draw_work security (DiffuseProfiles.edgeCutoff security) bits he word
  change (cutoffProgram security).work + (castWindow (cutoff_value security)
    (CurrentWindowDraw.draw security (cutoffProgram security).quotient bits
      (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) (cutoff_value security).symm) word))).work + 2 ≤ _
  rw [cast_draw]
  unfold workBound
  omega

noncomputable section
open scoped Classical

theorem draw_l1 (security bits : ℕ) :
    (∑ point, |((FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) => FiniteDist.uniform (Fin 2))).map
      (fun word => (draw security bits word).value)).weight point - (DiffuseProfiles.edgeLaw security).weight point|) ≤
      1 / (2 : ℝ) ^ bits := by
  simpa only [draw_value] using WindowGaussianSampler.edge_draw_l1 security bits

end
end CurrentAFT.CurrentEdgeDrawProgram

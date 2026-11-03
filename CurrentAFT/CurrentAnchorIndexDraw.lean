import CurrentAFT.CurrentUniformDraw
import CurrentAFT.InwardAnchor
import AFT.UnaryPolynomialCounters

/-! Public anchor indices from the executed current width counter. -/
namespace CurrentAFT.CurrentAnchorIndexDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def width (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let result := powerCounter base.count 48
  ⟨result.count, base.work + result.work + 2⟩

theorem width_value (security : ℕ) : (width security).count = Parameters.anchorWidth security := by
  simp only [width, powerCounter_value, addCounter_value, Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]

theorem width_positive (security : ℕ) : 0 < (width security).count := by
  rw [width_value]
  exact InwardAnchor.anchorWidth_pos security

abbrev Tape (security bits : ℕ) := Fin (bits + (width security).count + 1) → Fin 2

def indexEquiv (security : ℕ) : Fin (width security).count ≃ InwardAnchor.Index security :=
  finCongr (width_value security)

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (InwardAnchor.Index security) :=
  let result := binaryUniformDraw (width security).count (width_positive security) bits word
  ⟨indexEquiv security result.value, (width security).work + result.work + 1⟩

def workBound (security bits : ℕ) : ℕ :=
  (width security).work + binaryUniformDrawWork (width security).count bits + 1

theorem draw_work (security bits : ℕ) (word : Tape security bits) :
    (draw security bits word).work ≤ workBound security bits :=
  Nat.add_le_add_right (Nat.add_le_add_left (binaryUniformDraw_work _ (width_positive security) bits word) _) 1

noncomputable section
open scoped Classical
local instance anchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩

def law (security bits : ℕ) : FiniteDist (InwardAnchor.Index security) :=
  (FiniteDist.uniform (Tape security bits)).map (fun word => (draw security bits word).value)

theorem law_l1 (security bits : ℕ) :
    (∑ index, |(law security bits).weight index -
      (FiniteDist.uniform (InwardAnchor.Index security)).weight index|) ≤ 1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin (width security).count) := ⟨⟨0, width_positive security⟩⟩
  have h := FiniteDist.l1_map_le (CurrentUniformDraw.law _ (width_positive security) bits)
    (FiniteDist.uniform (Fin (width security).count)) (indexEquiv security)
  rw [FiniteDist.uniform_map_equiv] at h
  simp only [CurrentUniformDraw.law, FiniteDist.map_map] at h
  exact h.trans (CurrentUniformDraw.law_l1 _ (width_positive security) bits)

end
end CurrentAFT.CurrentAnchorIndexDraw

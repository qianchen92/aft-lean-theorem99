import CurrentAFT.CurrentReferenceDraw
import CurrentAFT.CurrentUniformDraw

/-! Finite-bit public safe-baseline draws, with executed native interval offsets. -/
namespace CurrentAFT.CurrentSafeDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev Tape (security bits : ℕ) := Fin (bits + (counts security).safe + 1) → Fin 2

def draw (security bits : ℕ) (word : Tape security bits) : CountedValue (FirstHistogram.Palette security) :=
  let selected := binaryUniformDraw (counts security).safe (safe_positive security) bits word
  let added := addCounter (counts security).margin selected.value.val
  have hi : added.count < Parameters.modulus security := by
    rw [addCounter_value, ← bodyEquiv_value]
    exact (bodyEquiv security selected.value).val.isLt
  ⟨⟨added.count, hi⟩, (counts security).work + selected.work + added.work + 2⟩

theorem draw_value (security bits : ℕ) (word : Tape security bits) :
    (draw security bits word).value = (bodyEquiv security
      (binaryUniformDraw (counts security).safe (safe_positive security) bits word).value).val := by
  apply Fin.ext
  change (addCounter (counts security).margin _).count = _
  rw [addCounter_value, bodyEquiv_value]

theorem draw_safe (security bits : ℕ) (word : Tape security bits) :
    InwardAnchor.SafeColor security (draw security bits word).value := by
  rw [draw_value]
  exact (bodyEquiv security _).property

def workBound (security bits : ℕ) : ℕ :=
  (counts security).work + binaryUniformDrawWork (counts security).safe bits + 2 * (counts security).margin + 3

theorem draw_work (security bits : ℕ) (word : Tape security bits) :
    (draw security bits word).work ≤ workBound security bits := by
  have h := binaryUniformDraw_work (counts security).safe (safe_positive security) bits word
  simp only [draw, addCounter_work, workBound]
  omega

noncomputable section
open scoped Classical

def law (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) :=
  (FiniteDist.uniform (Tape security bits)).map (fun word => (draw security bits word).value)

theorem uniform_target (security : ℕ) :
    (letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩;
      FiniteDist.uniform (Fin (counts security).safe)).map
        (fun index => (bodyEquiv security index).val) = ProposalPrimary.safeLaw security := by
  letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩
  letI : Nonempty (ActualControls.SafePalette security) := ⟨bodyEquiv security ⟨0, safe_positive security⟩⟩
  have he : (FiniteDist.uniform (Fin (counts security).safe)).map (bodyEquiv security) =
      CurrentSafePaletteIndex.uniformLaw security := by
    rw [FiniteDist.uniform_map_equiv]
    exact (FiniteDist.uniform_map_equiv (CurrentSafePaletteIndex.equiv security)).symm
  simpa only [← he, FiniteDist.map_map, Function.comp_def] using CurrentSafePaletteIndex.uniformLaw_full security

theorem law_l1 (security bits : ℕ) :
    (∑ color, |(law security bits).weight color - (ProposalPrimary.safeLaw security).weight color|) ≤
      1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩
  have h := FiniteDist.l1_map_le (CurrentUniformDraw.law (counts security).safe (safe_positive security) bits)
    (FiniteDist.uniform (Fin (counts security).safe)) (fun index => (bodyEquiv security index).val)
  rw [uniform_target] at h
  simp only [CurrentUniformDraw.law, FiniteDist.map_map] at h
  have he : law security bits =
      (FiniteDist.uniform (Tape security bits)).map (fun word => (bodyEquiv security
        (binaryUniformDraw (counts security).safe (safe_positive security) bits word).value).val) := by
    simp only [law, draw_value]
  rw [he]
  exact h.trans (CurrentUniformDraw.law_l1 (counts security).safe (safe_positive security) bits)

end
end CurrentAFT.CurrentSafeDraw

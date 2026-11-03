import AFT.QuantizedSampling

/-! # A fixed number of independent fair bits implements a dyadic table -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Little-endian binary evaluation; the underlying equivalence is explicit. -/
def bitTicket (bits : ℕ) : (Fin bits → Fin 2) → Fin (2 ^ bits) := finFunctionFinEquiv

theorem bitTicket_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitTicket bits word).val = ∑ index, (word index).val * 2 ^ index.val :=
  finFunctionFinEquiv_apply word

theorem independent_fair_bits_uniform (bits : ℕ) :
    FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2)) =
      FiniteDist.uniform (Fin bits → Fin 2) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]

theorem bitTicket_uniform (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map (bitTicket bits) =
      FiniteDist.uniform (Fin (2 ^ bits)) := by
  rw [independent_fair_bits_uniform]
  exact FiniteDist.uniform_map_equiv finFunctionFinEquiv

/-- Sampling from a precomputed integer table needs exactly `bits` input
bits. Selection uses only the executable integer ticket and bucket routines. -/
def drawBitTable {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ) (htotal : ∑ index, counts index = 2 ^ bits)
    (word : Fin bits → Fin 2) : Fin n :=
  drawFin counts (Fin.cast htotal.symm (bitTicket bits word))

theorem drawBitTable_law {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ index, counts index = 2 ^ bits) (index : Fin n) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (drawBitTable bits counts htotal)).weight index = (counts index : ℝ) / (2 : ℝ) ^ bits := by
  have hpos : 0 < ∑ index, counts index := by rw [htotal]; positivity
  letI : NeZero (∑ index, counts index) := ⟨hpos.ne'⟩
  have hu := bitTicket_uniform bits
  have ht := FiniteDist.uniform_map_equiv (finCongr htotal.symm)
  have hm := congrArg (fun p : FiniteDist (Fin (2 ^ bits)) =>
    p.map (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) hu
  dsimp only at hm
  rw [FiniteDist.map_map] at hm
  have hc := congrArg (fun p : FiniteDist (Fin (∑ index, counts index)) => p.map (drawFin counts)) ht
  dsimp only at hc
  rw [FiniteDist.map_map] at hc
  change ((FiniteDist.uniform (Fin (2 ^ bits))).map
    (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) = _ at hc
  change ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
    (fun word => drawFin counts (Fin.cast htotal.symm (bitTicket bits word)))).weight index = _
  rw [hm, hc]
  exact (drawFin_law counts hpos index).trans (by simp only [htotal, Nat.cast_pow, Nat.cast_ofNat])

end FiniteTicketSampler
end AFT

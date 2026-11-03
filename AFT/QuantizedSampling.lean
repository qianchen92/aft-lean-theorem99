import AFT.FiniteQuantization

/-! # Exact ticket implementation of the support-preserving rounded law -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

def drawFin {n : ℕ} (counts : Fin n → ℕ) (ticket : Fin (∑ index, counts index)) : Fin n :=
  ⟨bucket (List.ofFn counts) ticket.val, by
    have hh := bucket_lt_length (List.ofFn counts) ticket.val
      (by simpa only [List.sum_ofFn] using ticket.isLt)
    simpa only [List.length_ofFn] using hh⟩

theorem drawFin_law {n : ℕ} (counts : Fin n → ℕ) (hpositive : 0 < ∑ index, counts index)
    (index : Fin n) :
    (by
      letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
      exact ((FiniteDist.uniform (Fin (∑ index, counts index))).map (drawFin counts)).weight index) =
      (counts index : ℝ) / (∑ index, counts index) := by
  letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
  have hc := bucket_count (List.ofFn counts) index.val
  simp only [List.sum_ofFn, List.getElem?_ofFn, dif_pos index.isLt, Option.getD_some] at hc
  have hreal : (∑ ticket ∈ Finset.range (∑ index, counts index),
      if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0) = counts index := by
    exact_mod_cast hc
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin,
    drawFin, Fin.ext_iff]
  simp_rw [show ∀ ticket : Fin (∑ index, counts index),
    (if bucket (List.ofFn counts) ticket.val = index.val then ((∑ index, counts index : ℕ) : ℝ)⁻¹ else 0) =
      ((∑ index, counts index : ℕ) : ℝ)⁻¹ *
        (if bucket (List.ofFn counts) ticket.val = index.val then 1 else 0) from
          fun ticket => by split_ifs <;> simp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun ticket => if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0)
      (∑ index, counts index), hreal]
  ring

end FiniteTicketSampler

namespace FiniteQuantization

open scoped BigOperators Classical
noncomputable section

/-- A table lookup from one uniformly chosen finite ticket. The real-valued
rounding step is kept explicit in the definition of the integer table. -/
def drawRounded {n : ℕ} (law : FiniteDist (Fin n)) (tickets : ℕ) (fallback : Fin n)
    (ticket : Fin tickets) : Fin n :=
  FiniteTicketSampler.drawFin (count law tickets fallback)
    (Fin.cast (count_sum law tickets fallback).symm ticket)

theorem drawRounded_law {n : ℕ} (law : FiniteDist (Fin n)) (tickets : ℕ)
    (ht : 0 < tickets) (fallback : Fin n) :
    (by
      letI : NeZero tickets := ⟨ht.ne'⟩
      exact (FiniteDist.uniform (Fin tickets)).map (drawRounded law tickets fallback)) =
      roundedLaw law tickets ht fallback := by
  letI : NeZero tickets := ⟨ht.ne'⟩
  let counts := count law tickets fallback
  have htotal : (∑ index, counts index) = tickets := count_sum law tickets fallback
  have hpos : 0 < ∑ index, counts index := by omega
  letI : NeZero (∑ index, counts index) := ⟨hpos.ne'⟩
  let transport : Fin tickets ≃ Fin (∑ index, counts index) := finCongr htotal.symm
  have hu := FiniteDist.uniform_map_equiv transport
  have hm := congrArg (fun p : FiniteDist (Fin (∑ index, counts index)) => p.map (FiniteTicketSampler.drawFin counts)) hu
  dsimp only at hm
  rw [FiniteDist.map_map] at hm
  apply hm.trans
  apply FiniteDist.ext
  intro index
  exact FiniteTicketSampler.drawFin_law counts hpos index |>.trans (by
    simp only [roundedLaw, htotal, counts])

theorem drawRounded_tv {n : ℕ} (law : FiniteDist (Fin n)) (tickets : ℕ)
    (ht : 0 < tickets) (fallback : Fin n) :
    (by
      letI : NeZero tickets := ⟨ht.ne'⟩
      exact FiniteDist.TVBound ((FiniteDist.uniform (Fin tickets)).map (drawRounded law tickets fallback))
        law ((n : ℝ) / tickets)) := by
  rw [drawRounded_law law tickets ht fallback]
  simpa only [Fintype.card_fin] using roundedLaw_tv law tickets ht fallback

end
end FiniteQuantization
end AFT

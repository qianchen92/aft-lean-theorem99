import AFT.FairBitSampling

/-! # Binary-search sampling of an integer cumulative table

The algorithm queries only one cumulative entry at each level.  It does
not materialize or scan the exponentially large dyadic grid.
-/
namespace AFT.BinaryCDFSampler
open scoped BigOperators

/-- Locate the interval containing a ticket among `2^depth` consecutive
bins. The cumulative table is supplied as a function, not as a list. -/
def locate (cut : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lower, _ => lower
  | depth+1, lower, ticket =>
      if ticket<cut (lower+2^depth) then locate cut depth lower ticket
      else locate cut depth (lower+2^depth) ticket

/-- The search uses exactly one cumulative-table comparison per level. -/
def locateQueries (cut : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | depth+1, lower, ticket =>
      1+if ticket<cut (lower+2^depth) then locateQueries cut depth lower ticket
        else locateQueries cut depth (lower+2^depth) ticket

theorem locateQueries_eq (cut : ℕ → ℕ) (depth lower ticket : ℕ) :
    locateQueries cut depth lower ticket=depth := by
  induction depth generalizing lower with
  | zero => rfl
  | succ depth ih => simp only [locateQueries]; split_ifs <;> rw [ih] <;> omega

theorem locate_range (cut : ℕ → ℕ) (depth lower ticket : ℕ) :
    lower≤locate cut depth lower ticket ∧ locate cut depth lower ticket<lower+2^depth := by
  induction depth generalizing lower with
  | zero => simp [locate]
  | succ depth ih =>
    simp only [locate]
    split_ifs
    · have hh := ih lower
      rw [pow_succ]
      omega
    · have hh := ih (lower+2^depth)
      rw [pow_succ]
      omega

/-- Every returned bucket satisfies the actual cumulative inequalities.
Empty buckets are automatically skipped. -/
theorem locate_spec (cut : ℕ → ℕ) (depth lower ticket : ℕ)
    (hlow : cut lower≤ticket) (hhigh : ticket<cut (lower+2^depth)) :
    cut (locate cut depth lower ticket)≤ticket ∧ ticket<cut (locate cut depth lower ticket+1) := by
  induction depth generalizing lower with
  | zero => simpa only [locate,pow_zero] using And.intro hlow hhigh
  | succ depth ih =>
    simp only [locate]
    split_ifs with hsplit
    · exact ih lower hlow hsplit
    · apply ih (lower+2^depth) (Nat.le_of_not_gt hsplit)
      convert hhigh using 1
      rw [pow_succ]
      congr 1
      omega

/-- Under monotone cumulative counts, the interval inequalities characterize
the exact output bin. -/
theorem locate_eq_iff (cut : ℕ → ℕ) (depth ticket index : ℕ)
    (hmono : MonotoneOn cut (Set.Icc 0 (2^depth)))
    (hzero : cut 0=0) (hticket : ticket<cut (2^depth)) (hindex : index<2^depth) :
    locate cut depth 0 ticket=index ↔ cut index≤ticket ∧ ticket<cut (index+1) := by
  have hr := locate_range cut depth 0 ticket
  simp only [zero_add] at hr
  have hs := locate_spec cut depth 0 ticket (by rw [hzero]; exact Nat.zero_le _) (by simpa using hticket)
  constructor
  · intro he; simpa only [he] using hs
  · intro hi
    apply Nat.le_antisymm
    · by_contra h
      have hle : index+1≤locate cut depth 0 ticket := by omega
      have hh := hmono ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hle
      omega
    · by_contra h
      have hle : locate cut depth 0 ticket+1 ≤ index := by omega
      have hh := hmono ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hle
      omega

/-- An executable sampler with a fixed `depth`-comparison bound. -/
def draw (cut : ℕ → ℕ) (depth tickets : ℕ) (ticket : Fin tickets) : Fin (2^depth) :=
  ⟨locate cut depth 0 ticket.val,by have hh := (locate_range cut depth 0 ticket.val).2; simpa using hh⟩

/-- Its exact output law is the difference of consecutive cumulative
counts divided by the total ticket population. -/
theorem draw_weight (cut : ℕ → ℕ) (depth tickets : ℕ) (ht : 0<tickets)
    (hmono : MonotoneOn cut (Set.Icc 0 (2^depth))) (hzero : cut 0=0) (htotal : cut (2^depth)=tickets)
    (index : Fin (2^depth)) :
    (by letI : NeZero tickets := ⟨ht.ne'⟩; exact (FiniteDist.uniform (Fin tickets)).map (draw cut depth tickets) : FiniteDist (Fin (2^depth))).weight index=
      ((cut (index.val+1)-cut index.val : ℕ) : ℝ)/tickets := by
  classical
  letI : NeZero tickets := ⟨ht.ne'⟩
  have hindex := index.isLt
  have hlohi : cut index.val≤cut (index.val+1) :=
    hmono ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  have hupper : cut (index.val+1)≤tickets := by
    rw [← htotal]
    exact hmono ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  have hcount : (∑ ticket : Fin tickets,if locate cut depth 0 ticket.val=index.val then (1 : ℝ) else 0)=
      (cut (index.val+1)-cut index.val : ℕ) := by
    have he : (Finset.univ.filter fun ticket : Fin tickets => locate cut depth 0 ticket.val=index.val).card=
        cut (index.val+1)-cut index.val := by
      rw [← Finset.card_map Fin.valEmbedding]
      have heq : (Finset.univ.filter fun ticket : Fin tickets => locate cut depth 0 ticket.val=index.val).map Fin.valEmbedding=
          Finset.Ico (cut index.val) (cut (index.val+1)) := by
        ext ticket
        simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,Fin.valEmbedding_apply,Finset.mem_Ico]
        constructor
        · rintro ⟨point,hpoint,rfl⟩
          exact (locate_eq_iff cut depth point.val index.val hmono hzero (by rw [htotal]; exact point.isLt) index.isLt).mp hpoint
        · intro hp
          refine ⟨⟨ticket,hp.2.trans_le hupper⟩,?_,rfl⟩
          exact (locate_eq_iff cut depth ticket index.val hmono hzero (by rw [htotal]; omega) index.isLt).mpr hp
      rw [heq,Nat.card_Ico]
    have hn : (∑ ticket : Fin tickets,if locate cut depth 0 ticket.val=index.val then (1 : ℕ) else 0)=
        cut (index.val+1)-cut index.val := by simpa using he
    exact_mod_cast hn
  simp only [FiniteDist.map_weight,FiniteDist.uniform_weight,Fintype.card_fin,draw,Fin.ext_iff]
  calc
    _ = (∑ ticket : Fin tickets,if locate cut depth 0 ticket.val=index.val then (1 : ℝ) else 0)*(tickets : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ticket _
      split_ifs <;> simp
    _ = _ := by rw [hcount]; ring

end AFT.BinaryCDFSampler

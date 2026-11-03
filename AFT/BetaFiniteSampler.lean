import AFT.BetaGridLaw
import AFT.BinaryCDFSampler

/-! # Finite fair-bit beta sampling by rational CDF binary search -/
namespace AFT.BetaReference
open scoped BigOperators

/-- Integer cumulative counts computed from the exact rational beta CDF. -/
def finiteCut (K n depth bits j : ℕ) : ℕ :=
  ⌊((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) j⌋₊

/-- The sampler consumes exactly `bits` fair input bits and queries only
`depth` cumulative values, each evaluated by finite rational arithmetic. -/
def finiteDraw (K n depth bits : ℕ) (word : Fin bits → Fin 2) : Fin (2^depth) :=
  BinaryCDFSampler.draw (finiteCut K n depth bits) depth (2^bits) (FiniteTicketSampler.bitTicket bits word)

theorem finiteDraw_queries (K n depth bits : ℕ) (word : Fin bits → Fin 2) :
    BinaryCDFSampler.locateQueries (finiteCut K n depth bits) depth 0 (FiniteTicketSampler.bitTicket bits word).val=depth :=
  BinaryCDFSampler.locateQueries_eq _ _ _ _

theorem finiteCut_mono (K n depth bits : ℕ) : MonotoneOn (finiteCut K n depth bits) (Set.Icc 0 (2^depth)) := by
  intro i hi j hj hij
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (gridCDF_mono K n (2^depth) (by positivity) hi hj hij) (by positivity)

@[simp] theorem finiteCut_zero (K n depth bits : ℕ) : finiteCut K n depth bits 0=0 := by
  simp [finiteCut,gridCDF_zero]

@[simp] theorem finiteCut_total (K n depth bits : ℕ) : finiteCut K n depth bits (2^depth)=2^bits := by
  simp only [finiteCut,gridCDF_total K n (2^depth) (by positivity),mul_one,Nat.floor_natCast]

noncomputable section
open scoped Classical

def finiteLaw (K n depth bits : ℕ) : FiniteDist (Fin (2^depth)) :=
  (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map (finiteDraw K n depth bits)

/-- Exact law of the executable sampler, before comparison with rounded
continuous beta. -/
theorem finiteLaw_weight (K n depth bits : ℕ) (j : Fin (2^depth)) :
    (finiteLaw K n depth bits).weight j=
      ((finiteCut K n depth bits (j.val+1)-finiteCut K n depth bits j.val : ℕ) : ℝ)/(2^bits : ℕ) := by
  have hh := congrArg (fun law : FiniteDist (Fin (2^bits)) =>
    law.map (BinaryCDFSampler.draw (finiteCut K n depth bits) depth (2^bits))) (FiniteTicketSampler.bitTicket_uniform bits)
  dsimp only at hh
  rw [FiniteDist.map_map] at hh
  change finiteLaw K n depth bits=_ at hh
  rw [hh]
  exact BinaryCDFSampler.draw_weight _ _ _ (by positivity) (finiteCut_mono K n depth bits)
    (finiteCut_zero K n depth bits) (finiteCut_total K n depth bits) j

private theorem floor_error (x : ℚ) (hx : 0≤x) :
    |((⌊x⌋₊ : ℕ) : ℝ)-(x : ℝ)|≤1 := by
  have hle : ((⌊x⌋₊ : ℕ) : ℝ)≤(x : ℝ) := by exact_mod_cast Nat.floor_le hx
  have hlt : (x : ℝ)<((⌊x⌋₊ : ℕ) : ℝ)+1 := by exact_mod_cast Nat.lt_floor_add_one x
  rw [abs_le]
  constructor <;> linarith

/-- Quantizing the CDF changes each bin by at most two ticket units. -/
theorem finiteLaw_atom_error (K n depth bits : ℕ) (j : Fin (2^depth)) :
    |(finiteLaw K n depth bits).weight j-(gridLaw K n (2^depth) (by positivity)).weight j|≤
      (2 : ℝ)/(2^bits : ℕ) := by
  let cut := finiteCut K n depth bits
  have hindex := j.isLt
  have hmono := finiteCut_mono K n depth bits
  have hle : cut j.val≤cut (j.val+1) := hmono ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  have hc0 (i : ℕ) (hi : i≤2^depth) : 0≤gridCDF K n (2^depth) i := by
    rw [← gridCDF_zero K n (2^depth)]
    exact gridCDF_mono K n (2^depth) (by positivity) ⟨by omega,by omega⟩ ⟨by omega,hi⟩ (by omega)
  have hfirst := floor_error (((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) (j.val+1)) (mul_nonneg (by positivity) (hc0 _ (by omega)))
  have hsecond := floor_error (((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) j.val) (mul_nonneg (by positivity) (hc0 _ (by omega)))
  change |(cut (j.val+1) : ℝ)-((((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) (j.val+1) : ℚ) : ℝ)|≤1 at hfirst
  change |(cut j.val : ℝ)-((((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) j.val : ℚ) : ℝ)|≤1 at hsecond
  simp only [Rat.cast_mul,Rat.cast_natCast] at hfirst hsecond
  rw [finiteLaw_weight]
  change |((cut (j.val+1)-cut j.val : ℕ) : ℝ)/(2^bits : ℕ)-
    ((gridCDF K n (2^depth) (j.val+1)-gridCDF K n (2^depth) j.val : ℚ) : ℝ)|≤_
  rw [Nat.cast_sub hle,Rat.cast_sub]
  have ht : (0 : ℝ)<(2^bits : ℕ) := by positivity
  have heq : (cut (j.val+1) : ℝ)/(2^bits : ℕ)-(cut j.val : ℝ)/(2^bits : ℕ)-
      ((gridCDF K n (2^depth) (j.val+1) : ℝ)-(gridCDF K n (2^depth) j.val : ℝ))=
      (((cut (j.val+1) : ℝ)-(2^bits : ℕ)*(gridCDF K n (2^depth) (j.val+1) : ℝ))-
        ((cut j.val : ℝ)-(2^bits : ℕ)*(gridCDF K n (2^depth) j.val : ℝ)))/(2^bits : ℕ) := by
    field_simp
    ring
  rw [sub_div,heq,abs_div,abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  exact (abs_sub _ _).trans (by linarith)

/-- Full-law total variation, with an explicit precision cost independent
of the beta parameters. Taking `bits ≥ depth + precision` is sufficient. -/
theorem finiteLaw_tv (K n depth bits : ℕ) :
    FiniteDist.TVBound (finiteLaw K n depth bits) (gridLaw K n (2^depth) (by positivity))
      ((2^depth : ℕ)/(2^bits : ℕ)) := by
  apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr
  rw [FiniteDist.totalVariation_eq_half_l1]
  have hh : (∑ j : Fin (2^depth),|(finiteLaw K n depth bits).weight j-
      (gridLaw K n (2^depth) (by positivity)).weight j|)≤
      (2^depth : ℕ)*((2 : ℝ)/(2^bits : ℕ)) := by
    calc
      _ ≤ ∑ _j : Fin (2^depth),(2 : ℝ)/(2^bits : ℕ) := Finset.sum_le_sum fun j _ => finiteLaw_atom_error K n depth bits j
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact (div_le_div_of_nonneg_right hh (by norm_num)).trans_eq (by ring)

end
end AFT.BetaReference

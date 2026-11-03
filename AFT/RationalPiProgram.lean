import Mathlib

/-! # A finite rational program for pi with an explicit dyadic error

The program uses two convergent arctangent series and the proved identity
arctan(1/2)+arctan(1/3)=pi/4. No real-number oracle occurs in the program.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- A rational finite sum, executable by ordinary exact arithmetic. -/
def arctanSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,(-1 : ℚ)^index*value^(2*index+1)/(2*index+1 : ℕ)

def piApprox (bits : ℕ) : ℚ :=
  4*(arctanSum (1/2) (bits+3)+arctanSum (1/3) (bits+3))

noncomputable section
open scoped Classical

theorem arctan_term_bound (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- On the two actual rational inputs, absolute geometric majorization
bounds the entire remaining series, including its alternating signs. -/
theorem arctanSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := arctan_term_bound (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum

/-- `bits+3` terms of each short series give the requested binary accuracy. -/
theorem piApprox_error (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := arctanSum_error (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := arctanSum_error (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring

end
end AFT.RationalNumerics

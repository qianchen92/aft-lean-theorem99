import AFT.RationalBodyPaddingProgram

/-! # Integer and conditional-center heights of the cached scalar chain -/
namespace AFT.RationalNumerics
open GaussianSource Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem HeightBound.abs_le {value : ℚ} {bits : ℕ} (h : HeightBound value bits) :
    |value|≤(2 : ℚ)^bits := by
  have hd : (1 : ℚ)≤value.den := by exact_mod_cast value.den_pos
  have hn' : (value.num.natAbs : ℚ)≤(2 : ℚ)^bits := by exact_mod_cast h.1
  have hn : |(value.num : ℚ)|≤(2 : ℚ)^bits := by simpa using hn'
  rw [←Rat.num_div_den value,abs_div,abs_of_pos (by exact_mod_cast value.den_pos : (0 : ℚ)<value.den)]
  exact (div_le_self (abs_nonneg _) hd).trans hn

theorem centeredGaussianAnchor_abs (center : ℚ) :
    |(centeredGaussianAnchor center : ℚ)|≤|center|+1 := by
  have hlo := Int.floor_le center
  have hhi := Int.lt_floor_add_one center
  change |(⌊center⌋ : ℚ)|≤|center|+1
  rw [abs_le]
  constructor <;> linarith [le_abs_self center,neg_abs_le center]

theorem centeredGaussianDraw_value_bound (squaredWidth center : ℚ) (cutoff bits : ℕ)
    (tape : Fin (windowTicketBits cutoff bits) → Fin 2) :
    |((centeredGaussianAnchor center+(centeredGaussianDraw squaredWidth center cutoff bits tape : ℤ) : ℤ) : ℚ)|≤
      |center|+(cutoff+1) := by
  have hp := (centeredGaussianDraw squaredWidth center cutoff bits tape).property
  have hoff : |((centeredGaussianDraw squaredWidth center cutoff bits tape : ℤ) : ℚ)|≤cutoff := by
    rw [abs_le]
    have hh := Finset.mem_Icc.mp hp
    constructor <;> exact_mod_cast (by omega : _)
  calc
    _ ≤ |(centeredGaussianAnchor center : ℚ)|+
        |((centeredGaussianDraw squaredWidth center cutoff bits tape : ℤ) : ℚ)| := by
      simpa only [Int.cast_add] using abs_add_le (centeredGaussianAnchor center : ℚ)
        ((centeredGaussianDraw squaredWidth center cutoff bits tape : ℤ) : ℚ)
    _ ≤ _ := by linarith [centeredGaussianAnchor_abs center]

/-- A single global bound for all realized integer words. The exponent is
polynomial in the dimension and coefficient height, even though the
integers themselves need not have polynomial magnitude. -/
theorem upperRationalGaussianChain_draw_bound (cap height cutoff bits : ℕ) :
    ∀ (count : ℕ) (_hcount : count≤cap) (squaredWidth : Fin count → ℚ)
      (matrix : Matrix (Fin count) (Fin count) ℚ)
      (_hmat : ∀ i j,|matrix i j|≤(2 : ℚ)^height)
      (randomness : Fin count → Fin (windowTicketBits cutoff bits) → Fin 2) (index : Fin count),
      |(((upperRationalGaussianChain count squaredWidth (fun _ => 0) matrix).draw cutoff bits randomness).get index : ℚ)|≤
        (2 : ℚ)^((height+cap+1)*count+cutoff+1) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ index;exact Fin.elim0 index
  | succ count ih =>
    intro hcount squaredWidth matrix hmat randomness index
    let tail := upperRationalGaussianChain count (fun i => squaredWidth i.succ) (fun _ => 0)
      (fun i j => matrix i.succ j.succ)
    let word := (tail.draw cutoff bits (fun i => randomness i.succ)).get
    have hword (i : Fin count) : |(word i : ℚ)|≤(2 : ℚ)^((height+cap+1)*count+cutoff+1) :=
      ih (by omega) _ _ (fun i j => hmat i.succ j.succ) _ i
    have hbase : (count : ℚ)*(2 : ℚ)^height+1≤(2 : ℚ)^(height+cap+1) := by
      have hc : (count : ℚ)≤(2 : ℚ)^cap := by
        exact_mod_cast (le_trans (by omega : count≤cap) (Nat.lt_two_pow_self (n:=cap)).le)
      have hh : (1 : ℚ)≤(2 : ℚ)^height := one_le_pow₀ (by norm_num)
      have hp : (1 : ℚ)≤(2 : ℚ)^cap := one_le_pow₀ (by norm_num)
      rw [pow_add,pow_add,pow_one]
      nlinarith
    have hcutoff : (cutoff+1 : ℚ)≤(2 : ℚ)^((height+cap+1)*count+cutoff+1) := by
      have hc : cutoff+1≤2^(cutoff+1) := (Nat.lt_two_pow_self (n:=cutoff+1)).le
      have hp := Nat.pow_le_pow_right (by decide : 1≤2)
        (by omega : cutoff+1≤(height+cap+1)*count+cutoff+1)
      exact_mod_cast hc.trans hp
    have hcenter : |(0-∑ j : Fin count,matrix 0 j.succ*((word j : ℚ)-0) : ℚ)|≤
        (count : ℚ)*(2 : ℚ)^height*(2 : ℚ)^((height+cap+1)*count+cutoff+1) := by
      simp only [sub_zero,zero_sub,abs_neg]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ j : Fin count,(2 : ℚ)^height*(2 : ℚ)^((height+cap+1)*count+cutoff+1) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (hmat 0 j.succ) (hword j) (abs_nonneg _) (by positivity)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
    refine Fin.cases ?_ (fun i => ?_) index
    · simp only [upperRationalGaussianChain,RationalGaussianChain.draw,Vector.get_ofFn,Fin.cons_zero]
      change |((centeredGaussianAnchor (0-∑ j : Fin count,matrix 0 j.succ*((word j : ℚ)-0))+
        (centeredGaussianDraw (squaredWidth 0) (0-∑ j : Fin count,matrix 0 j.succ*((word j : ℚ)-0))
          cutoff bits (randomness 0) : ℤ) : ℤ) : ℚ)|≤_
      apply (centeredGaussianDraw_value_bound _ _ _ _ _).trans
      calc
        _ ≤ ((count : ℚ)*(2 : ℚ)^height+1)*(2 : ℚ)^((height+cap+1)*count+cutoff+1) := by nlinarith
        _ ≤ (2 : ℚ)^(height+cap+1)*(2 : ℚ)^((height+cap+1)*count+cutoff+1) := by gcongr
        _ = _ := by rw [←pow_add];congr 1;ring
    · simp only [upperRationalGaussianChain,RationalGaussianChain.draw,Vector.get_ofFn,Fin.cons_succ]
      change |(word i : ℚ)|≤_
      apply (hword i).trans
      exact pow_le_pow_right₀ (by norm_num) (by simp only [Nat.mul_add,Nat.mul_one];omega)

/-- Once word lengths are bounded globally, the *actual* rational center
uses only one finite dot product, so its height is polynomial as well. -/
theorem conditionalCenter_height {count coefficientBits wordBits : ℕ}
    (coefficients : Fin count → ℚ) (word : Fin count → ℤ)
    (hc : ∀ i,HeightBound (coefficients i) coefficientBits)
    (hw : ∀ i,(word i).natAbs≤2^wordBits) :
    HeightBound (-∑ i,coefficients i*(word i : ℚ)) (count*(coefficientBits+wordBits+1)) := by
  simpa only [Finset.card_univ,Fintype.card_fin] using
    (HeightBound.sum Finset.univ (fun i => coefficients i*(word i : ℚ)) (coefficientBits+wordBits)
      (fun i _ => (hc i).mul (HeightBound.of_int (hw i)))).neg

end
end AFT.RationalNumerics

import AFT.RationalFiniteQuantization
import AFT.FiniteConditionProgram
import AFT.FiniteProductVariation
import Mathlib.GroupTheory.Perm.Fin

/-! # A finite fair-bit permutation sampler without enumerating permutations -/
namespace AFT.PermutationProgram
open scoped BigOperators

def choiceWeight (size : ℕ) : Fin (size+1) → ℚ := fun _ => ((size+1 : ℕ) : ℚ)⁻¹

theorem choiceWeight_nonneg (size : ℕ) (index : Fin (size+1)) : 0≤choiceWeight size index := by
  unfold choiceWeight
  positivity

theorem choiceWeight_sum (size : ℕ) : (∑ index,choiceWeight size index)=1 := by
  simp only [choiceWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

def choiceDraw (size bits : ℕ) : (Fin bits → Fin 2) → Fin (size+1) :=
  RationalFiniteQuantization.draw (choiceWeight size) (choiceWeight_nonneg size) (choiceWeight_sum size) bits

/-- Insert one newly drawn image, then permute the remaining positions.
There are exactly count recursive stages, each using bits fresh fair bits. -/
def rows (bits : ℕ) : (count : ℕ) → (Fin count → Fin bits → Fin 2) → Equiv.Perm (Fin count)
  | 0,_ => Equiv.refl _
  | count+1,word => Equiv.Perm.decomposeFin.symm (choiceDraw count bits (word 0),rows bits count (Fin.tail word))

def draw (count bits : ℕ) (word : Fin (count*bits) → Fin 2) : Equiv.Perm (Fin count) :=
  rows bits count (FiniteConditionProgram.groupBits count bits word)

noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem uniform_prod {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (uniform A).prod (uniform B)=uniform (A × B) := by
  ext point
  simp only [prod_weight,uniform_weight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev]
  ring

private theorem uniform_function (count : ℕ) (A : Type*) [Fintype A] [Nonempty A] :
    independent (fun _ : Fin count => uniform A)=uniform (Fin count → A) := by
  ext word
  simp only [independent,uniform_weight,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_fun,Nat.cast_pow,inv_pow]

private theorem map_prod {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (first : FiniteDist A) (second : FiniteDist B) (f : A → X) (g : B → Y) :
    (first.prod second).map (fun point => (f point.1,g point.2))=(first.map f).prod (second.map g) := by
  ext point
  rcases point with ⟨x,y⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a=x <;> by_cases hg : g b=y <;> simp [hf,hg]

private theorem tv_prod {A B : Type*} [Fintype A] [Fintype B]
    {first first' : FiniteDist A} {second second' : FiniteDist B} {error error' : ℝ}
    (hfirst : TVBound first first' error) (hsecond : TVBound second second' error') :
    TVBound (first.prod second) (first'.prod second') (error+error') := by
  rw [tvBound_iff_totalVariation_le,totalVariation_eq_half_l1] at hfirst hsecond ⊢
  linarith [l1_prod_le first first' second second']

def choiceLaw (size bits : ℕ) : FiniteDist (Fin (size+1)) :=
  (uniform (Fin bits → Fin 2)).map (choiceDraw size bits)

theorem choiceLaw_tv (size bits : ℕ) : TVBound (choiceLaw size bits) (uniform (Fin (size+1)))
    ((size+1 : ℝ)/(2 : ℝ)^bits) := by
  have hh := RationalFiniteQuantization.draw_tv (choiceWeight size)
    (choiceWeight_nonneg size) (choiceWeight_sum size) bits
  rw [FiniteTicketSampler.independent_fair_bits_uniform] at hh
  have he : RationalFiniteQuantization.law (choiceWeight size)
      (choiceWeight_nonneg size) (choiceWeight_sum size)=uniform (Fin (size+1)) := by
    ext point
    simp [RationalFiniteQuantization.law,choiceWeight,uniform_weight]
  rwa [he] at hh

def permutationLaw (count bits : ℕ) : FiniteDist (Equiv.Perm (Fin count)) :=
  (uniform (Fin count → Fin bits → Fin 2)).map (rows bits count)

theorem permutationLaw_succ (count bits : ℕ) :
    permutationLaw (count+1) bits=
      ((choiceLaw count bits).prod (permutationLaw count bits)).map Equiv.Perm.decomposeFin.symm := by
  unfold permutationLaw
  rw [← uniform_function (count+1),FiniteConditionProgram.independent_cons,FiniteDist.map_map]
  rw [choiceLaw,← map_prod,FiniteDist.map_map]
  rw [uniform_function count]
  rfl

theorem draw_law (count bits : ℕ) :
    (uniform (Fin (count*bits) → Fin 2)).map (draw count bits)=permutationLaw count bits := by
  have hh := congrArg (fun law => law.map (rows bits count))
    (uniform_map_equiv (FiniteConditionProgram.groupBits count bits))
  simpa only [FiniteDist.map_map,draw,permutationLaw] using hh

/-- The total error is quadratic in the population and exponentially small
in the per-stage bit precision. No factorial-size permutation list occurs. -/
theorem permutationLaw_tv (count bits : ℕ) :
    TVBound (permutationLaw count bits) (uniform (Equiv.Perm (Fin count)))
      ((count : ℝ)^2/(2 : ℝ)^bits) := by
  induction count with
  | zero =>
    have he : permutationLaw 0 bits=uniform (Equiv.Perm (Fin 0)) := by
      ext permutation
      simp [permutationLaw,map_weight,uniform_weight,rows]
      exact Subsingleton.elim _ _
    rw [he]
    simpa using tvBound_refl (uniform (Equiv.Perm (Fin 0)))
  | succ count ih =>
    have hh := (tv_prod (choiceLaw_tv count bits) ih).map Equiv.Perm.decomposeFin.symm
    rw [uniform_prod,uniform_map_equiv,← permutationLaw_succ] at hh
    apply hh.mono
    have hden : 0<(2 : ℝ)^bits := by positivity
    rw [← add_div,Nat.cast_add,Nat.cast_one]
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith [Nat.cast_nonneg (α := ℝ) count]

end
end AFT.PermutationProgram

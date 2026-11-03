import AFT.ProfileTensorBoundary

/-! # A constant output coordinate annihilates a genuinely joint canonical input -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color Output : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Polynomial-valued orthogonality, coefficient by coefficient. -/
theorem canonical_weighted_polynomial_zero (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (slot : Slot) (hc : Hoeffding.CenteredAt reference slot kernel)
    (polynomial : (Slot → Color) → Table Output)
    (hp : ∀ first second,(∀ other,other≠slot → first other=second other) →
      polynomial first=polynomial second) :
    (∑ word,MvPolynomial.C (kernel word*∏ index,(reference index).weight (word index))*polynomial word)=0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  ext powers
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_zero]
  have he := Hoeffding.orthogonal_of_centered reference (Finset.univ.erase slot) slot
    (by simp) kernel (fun word => MvPolynomial.coeff powers (polynomial word)) hc (by
      intro first second h
      apply congrArg (MvPolynomial.coeff powers)
      apply hp first second
      intro other ho
      exact h other (Finset.mem_erase.mpr ⟨ho,Finset.mem_univ _⟩))
  unfold FiniteDist.expectation FiniteDist.independent at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro word _
  ring

def jointChannelPolynomial (reference : Slot → FiniteDist Color)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ) : Table Output :=
  ∑ word,MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*∏ slot,forms slot (word slot)

/-- Only positive-reference inputs need a constant channel. No condition is
imposed on inaccessible inputs, and the remaining kernel may be fully joint. -/
theorem jointChannelPolynomial_zero (reference : Slot → FiniteDist Color)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ)
    (slot : Slot) (common : Table Output)
    (hc : Hoeffding.CenteredAt reference slot kernel)
    (hforms : ∀ color,(reference slot).weight color≠0 → forms slot color=common) :
    jointChannelPolynomial reference forms kernel=0 := by
  let remaining := fun word : Slot → Color => ∏ other∈Finset.univ.erase slot,forms other (word other)
  have hz := canonical_weighted_polynomial_zero reference kernel slot hc remaining (by
    intro first second he
    apply Finset.prod_congr rfl
    intro other ho
    rw [he other (Finset.mem_erase.mp ho).1])
  have he : jointChannelPolynomial reference forms kernel=
      common*(∑ word,MvPolynomial.C (kernel word*∏ index,(reference index).weight (word index))*remaining word) := by
    unfold jointChannelPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    by_cases hw : (reference slot).weight (word slot)=0
    · have hh : (∏ index,(reference index).weight (word index))=0 :=
        Finset.prod_eq_zero (Finset.mem_univ slot) hw
      simp only [hh,mul_zero,map_zero,zero_mul]
    · rw [← Finset.mul_prod_erase Finset.univ (fun index => forms index (word index)) (Finset.mem_univ slot),hforms _ hw]
      change _=common*(_*∏ other∈Finset.univ.erase slot,forms other (word other))
      ring
  rw [he,hz,mul_zero]

theorem profilePolynomialMap_seedOutput [Fintype Output] [DecidableEq Output]
    (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ)
    (operator : Module.End ℝ (Output → ℝ)) (seed : InputSeed Color) :
    profilePolynomialMap operator (seedOutput primary body primaryChannel bodyChannel seed)=
      jointChannelPolynomial (inputReference primary body seed)
        (fun slot color => profileForm (operator (seedChannel primaryChannel bodyChannel seed slot color))) seed.kernel := by
  unfold seedOutput jointChannelPolynomial
  simp only [map_sum,map_mul,map_prod]
  apply Finset.sum_congr rfl
  intro word _
  have he (value : ℝ) : profilePolynomialMap operator (MvPolynomial.C value)=MvPolynomial.C value :=
    (profilePolynomialMap operator).commutes value
  simp_rw [he]
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  exact profilePolynomialMap_profileForm operator _

end
end AFT.RepresentedPolynomial

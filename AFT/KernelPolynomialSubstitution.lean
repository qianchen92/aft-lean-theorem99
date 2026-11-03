import AFT.KernelPolynomial

/-! # One genuinely joint coordinate replacement under arbitrary polynomial forms -/
namespace AFT.RepresentedPolynomial
open MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance kernelPolynomialSubstitutionUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance kernelPolynomialSubstitutionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {New Rest Color Output : Type*} [Fintype New] [Fintype Rest]
  [DecidableEq New] [DecidableEq Rest] [Fintype Color]

theorem kernelPolynomial_sum_smul (forms : New → Color → Table Output)
    (coefficient : Color → ℝ) (column : Color → (New → Color) → ℝ) :
    kernelPolynomial forms (fun word => ∑ color,coefficient color*column color word)=
      ∑ color,MvPolynomial.C (coefficient color)*kernelPolynomial forms (column color) := by
  unfold kernelPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro color _
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem kernelPolynomial_column_substitution (forms : New → Color → Table Output)
    (otherForms : Rest → Color → Table Output)
    (kernel : Color → (Rest → Color) → ℝ) (column : Color → (New → Color) → ℝ) :
    kernelPolynomial (Sum.elim forms otherForms)
      (fun word => ∑ color,kernel color (fun slot => word (Sum.inr slot))*column color (fun slot => word (Sum.inl slot)))=
    kernelPolynomial (Sum.elim (fun _ : Unit => fun color => kernelPolynomial forms (column color)) otherForms)
      (singletonJoin kernel) := by
  rw [kernelPolynomial_sum,kernelPolynomial_sum]
  apply Finset.sum_congr rfl
  intro rest _
  congr 1
  change kernelPolynomial forms (fun word => ∑ color,kernel color rest*column color word)=
    kernelPolynomial (fun _ : Unit => fun color => kernelPolynomial forms (column color)) (fun word => kernel (word ()) rest)
  rw [kernelPolynomial_unit,kernelPolynomial_sum_smul]

theorem kernelPolynomial_singleton_add (first second : Color → Table Output)
    (otherForms : Rest → Color → Table Output) (kernel : Color → (Rest → Color) → ℝ) :
    kernelPolynomial (Sum.elim (fun _ : Unit => fun color => first color+second color) otherForms) (singletonJoin kernel)=
      kernelPolynomial (Sum.elim (fun _ : Unit => first) otherForms) (singletonJoin kernel)+
      kernelPolynomial (Sum.elim (fun _ : Unit => second) otherForms) (singletonJoin kernel) := by
  simp only [kernelPolynomial_sum]
  simp only [kernelPolynomial_unit,singletonJoin,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    mul_add,Finset.sum_add_distrib,add_mul]

theorem kernelPolynomial_singleton_sum {Index : Type*} (indices : Finset Index)
    (forms : Index → Color → Table Output) (otherForms : Rest → Color → Table Output)
    (kernel : Color → (Rest → Color) → ℝ) :
    kernelPolynomial (Sum.elim (fun _ : Unit => fun color => ∑ index∈indices,forms index color) otherForms) (singletonJoin kernel)=
      ∑ index∈indices,kernelPolynomial (Sum.elim (fun _ : Unit => forms index) otherForms) (singletonJoin kernel) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [kernelPolynomial_sum,kernelPolynomial_unit,singletonJoin]
  | @insert index indices hnot ih =>
    simp only [Finset.sum_insert hnot,kernelPolynomial_singleton_add,ih]

end
end AFT.RepresentedPolynomial

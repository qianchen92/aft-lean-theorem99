import AFT.KernelPolynomialMonomial
import AFT.HistogramLowDegree

/-! # Input-order truncation preserves equality of all role polynomials

The universal primary/body color variables are homogeneous of degree one.
Truncate there first, then substitute arbitrary polynomial-valued forms.
This avoids requiring the final forms themselves to be homogeneous.
-/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Color Output Other Seed : Type*} [Fintype Color]

theorem inputKernelPolynomial_homogeneous (primary body : Color → Table Output)
    (hp : ∀ color,(primary color).IsHomogeneous 1)
    (hb : ∀ color,(body color).IsHomogeneous 1) (seed : InputSeed Color) :
    (inputKernelPolynomial primary body seed).IsHomogeneous (seed.primaryOrder+seed.bodyOrder) := by
  unfold inputKernelPolynomial kernelPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  apply MvPolynomial.IsHomogeneous.C_mul
  have hf (slot : Fin (seed.primaryOrder+seed.bodyOrder)) :
      ((Fin.addCases (motive:=fun _ => Color → Table Output) (fun _ : Fin seed.primaryOrder => primary)
        (fun _ : Fin seed.bodyOrder => body)) slot (word slot)).IsHomogeneous 1 := by
    cases slot using Fin.addCases with
    | left slot => simpa only [Fin.addCases_left] using hp (word (Fin.castAdd _ slot))
    | right slot => simpa only [Fin.addCases_right] using hb (word (Fin.natAdd _ slot))
  convert MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1) (fun slot _ => hf slot) using 1
  simp

omit [Fintype Color] in
theorem truncate_monomial_exact (order : Seed → ℕ) (cutoff : ℕ) (powers : Seed →₀ ℕ) (scalar : ℝ) :
    truncate order cutoff (MvPolynomial.monomial powers scalar)=
      if weightedOrder order powers≤cutoff then MvPolynomial.monomial powers scalar else 0 := by
  by_cases hp : weightedOrder order powers≤cutoff
  · rw [if_pos hp]
    exact Finsupp.filter_single_of_pos (fun term => weightedOrder order term≤cutoff) (a:=powers) (b:=scalar) hp
  · rw [if_neg hp]
    exact Finsupp.filter_single_of_neg (fun term => weightedOrder order term≤cutoff) (a:=powers) (b:=scalar) hp

/-- For homogeneous degree-one forms, input-order and ordinary polynomial
degree cutoffs agree exactly, including all coefficient cancellations. -/
theorem inputKernelPolynomialHom_truncate_homogeneous (primary body : Color → Table Output)
    (hp : ∀ color,(primary color).IsHomogeneous 1)
    (hb : ∀ color,(body color).IsHomogeneous 1) (cutoff : ℕ) (table : Table (InputSeed Color)) :
    inputKernelPolynomialHom primary body
      (truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff table)=
      truncate (fun _ : Output => 1) cutoff (inputKernelPolynomialHom primary body table) := by
  induction table using MvPolynomial.induction_on' with
  | monomial powers scalar =>
    have hh : (inputKernelPolynomialHom primary body (MvPolynomial.monomial powers scalar)).IsHomogeneous
        (weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers) := by
      exact aeval_monomial_homogeneous _ _ (inputKernelPolynomial_homogeneous primary body hp hb) powers scalar
    rw [truncate_monomial_exact,truncate_homogeneous _ _ _ hh]
    split_ifs <;> simp only [map_zero]
  | add first second hfirst hsecond =>
    simp only [truncate_add,map_add,hfirst,hsecond]

/-- Arbitrary polynomial substitutions commute with the complete input hom. -/
theorem inputKernelPolynomialHom_substitute (replace : Output → Table Other)
    (primary body : Color → Table Output) (table : Table (InputSeed Color)) :
    MvPolynomial.eval₂Hom MvPolynomial.C replace (inputKernelPolynomialHom primary body table)=
      inputKernelPolynomialHom
        (fun color => MvPolynomial.eval₂Hom MvPolynomial.C replace (primary color))
        (fun color => MvPolynomial.eval₂Hom MvPolynomial.C replace (body color)) table := by
  have he : (MvPolynomial.eval₂Hom MvPolynomial.C replace).comp (inputKernelPolynomialHom primary body)=
      inputKernelPolynomialHom
        (fun color => MvPolynomial.eval₂Hom MvPolynomial.C replace (primary color))
        (fun color => MvPolynomial.eval₂Hom MvPolynomial.C replace (body color)) := by
    apply MvPolynomial.ringHom_ext
    · intro scalar
      simp [inputKernelPolynomialHom]
    · intro seed
      simp only [RingHom.comp_apply,inputKernelPolynomialHom_X]
      unfold inputKernelPolynomial kernelPolynomial
      simp only [map_sum,map_mul,map_prod,MvPolynomial.eval₂Hom_C]
      apply Finset.sum_congr (by ext; simp)
      intro word _
      congr 1
      apply Finset.prod_congr rfl
      intro slot _
      cases slot using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]
  exact RingHom.congr_fun he table

/-- Only the universal role-color forms are needed to test equality. -/
theorem inputKernelPolynomialHom_universal_substitute (primary body : Color → Table Output)
    (table : Table (InputSeed Color)) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim primary body)
      (inputKernelPolynomialHom (fun color => MvPolynomial.X (Sum.inl color))
        (fun color => MvPolynomial.X (Sum.inr color)) table)=
      inputKernelPolynomialHom primary body table := by
  rw [inputKernelPolynomialHom_substitute]
  simp only [MvPolynomial.eval₂Hom_X',Sum.elim_inl,Sum.elim_inr]

/-- Equality of role polynomials survives the literal weighted input cutoff,
then evaluation at arbitrary, possibly nonhomogeneous forms. -/
theorem inputKernelPolynomialHom_truncate_congr (cutoff : ℕ) (first second : Table (InputSeed Color))
    (hequal : inputKernelPolynomialHom (fun color : Color => MvPolynomial.X (Sum.inl color))
        (fun color : Color => MvPolynomial.X (Sum.inr color)) first=
      inputKernelPolynomialHom (fun color : Color => MvPolynomial.X (Sum.inl color))
        (fun color : Color => MvPolynomial.X (Sum.inr color)) second)
    (primary body : Color → Table Output) :
    inputKernelPolynomialHom primary body (truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff first)=
      inputKernelPolynomialHom primary body (truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff second) := by
  have hh := congrArg (truncate (fun _ : Color⊕Color => 1) cutoff) hequal
  have hfirst := inputKernelPolynomialHom_truncate_homogeneous
    (fun color : Color => MvPolynomial.X (Sum.inl color : Color⊕Color))
    (fun color : Color => MvPolynomial.X (Sum.inr color : Color⊕Color))
    (fun color => MvPolynomial.isHomogeneous_X ℝ (Sum.inl color : Color⊕Color))
    (fun color => MvPolynomial.isHomogeneous_X ℝ (Sum.inr color : Color⊕Color)) cutoff first
  have hsecond := inputKernelPolynomialHom_truncate_homogeneous
    (fun color : Color => MvPolynomial.X (Sum.inl color : Color⊕Color))
    (fun color : Color => MvPolynomial.X (Sum.inr color : Color⊕Color))
    (fun color => MvPolynomial.isHomogeneous_X ℝ (Sum.inl color : Color⊕Color))
    (fun color => MvPolynomial.isHomogeneous_X ℝ (Sum.inr color : Color⊕Color)) cutoff second
  have hcut := hfirst.trans (hh.trans hsecond.symm)
  have hsub := congrArg (MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim primary body)) hcut
  simpa only [inputKernelPolynomialHom_universal_substitute] using hsub

end
end AFT.RepresentedPolynomial

import AFT.BoundaryPrimarySeed
import AFT.RepresentedCanonical

/-! # A literal finite table for the complete boundary transform -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

theorem boundaryCollapse_mass (interior : Finset Color) (target profile : Color → ℝ)
    (hm : (∑ color∈interior,target color)≠0) :
    (∑ color,boundaryCollapse interior target profile color)=∑ color,profile color := by
  rw [← Finset.sum_add_sum_compl interior (boundaryCollapse interior target profile),
    ← Finset.sum_add_sum_compl interior profile,boundaryCollapse_interior_sum _ _ _ hm]
  congr 1
  apply Finset.sum_congr rfl
  intro color hc
  exact boundaryCollapse_boundary _ _ _ _ (Finset.mem_compl.mp hc)

def boundaryInputTable (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (target : Color → ℝ) : Table (InputSeed Color) →ₐ[ℝ] Table (InputSeed Color) :=
  MvPolynomial.aeval (fun seed => if seed.bodyOrder=0 then
    MvPolynomial.X (boundaryPrimarySeed primary body operator interior target seed) else 0)

theorem boundaryInputTable_hasOrder (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (target : Color → ℝ) (minimum : ℕ) (table : Table (InputSeed Color))
    (ht : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum table) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum
      (boundaryInputTable primary body operator interior target table) := by
  apply aeval_hasOrder_of_lower_bounds _ _ _ _ minimum table ht
  intro seed
  split_ifs
  · simpa only [map_one,one_mul] using hasOrder_C_mul_X
      (fun input : InputSeed Color => input.primaryOrder+input.bodyOrder)
      (seed.primaryOrder+seed.bodyOrder) (boundaryPrimarySeed primary body operator interior target seed) 1 (le_refl _)
  · intro powers _
    exact MvPolynomial.coeff_zero _

omit [DecidableEq Color] in
theorem InputTableCanonical.aeval {primary body : FiniteDist Color} (table : Table (InputSeed Color))
    (images : InputSeed Color → Table (InputSeed Color))
    (hi : ∀ seed∈table.vars,InputTableCanonical primary body (images seed)) :
    InputTableCanonical primary body (MvPolynomial.aeval images table) := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply InputTableCanonical.sum
  intro powers hp
  rw [MvPolynomial.aeval_monomial]
  apply (InputTableCanonical.C _).mul
  unfold Finsupp.prod
  have hprod (s : Finset (InputSeed Color)) (hs : s⊆powers.support) :
      InputTableCanonical primary body (∏ seed∈s,images seed^powers seed) := by
    induction s using Finset.induction_on with
    | empty => simpa using (InputTableCanonical.one (primary := primary) (body := body))
    | @insert seed s hn ih =>
      rw [Finset.prod_insert hn]
      apply ((hi seed ((MvPolynomial.mem_vars seed).mpr ⟨powers,hp,hs (Finset.mem_insert_self _ _)⟩)).pow (powers seed)).mul
      exact ih (fun other ho => hs (Finset.mem_insert_of_mem ho))
  exact hprod _ (Finset.Subset.refl _)

theorem boundaryInputTable_canonical (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (target : Color → ℝ) (hpositive : ∀ color,primary.weight color≠0)
    (hm : (∑ color∈interior,target color)≠0)
    (hinverse : ∀ profile,(∑ color,operator.symm profile color)=∑ color,profile color)
    (table : Table (InputSeed Color)) (ht : InputTableCanonical primary body table) :
    InputTableCanonical primary body (boundaryInputTable primary body operator interior target table) := by
  apply InputTableCanonical.aeval
  intro seed hs
  split_ifs with hb
  · apply InputTableCanonical.X
    apply MixedKernel.inputIteration_canonical
    · intro slot hslot color
      change (inputReference primary body seed slot).weight color≠0
      rw [all_primary_reference primary body seed hb slot]
      exact hpositive color
    · intro slot hslot profile
      change (∑ color,operator.symm (boundaryCollapse interior target profile) color)=_
      rw [hinverse,boundaryCollapse_mass _ _ _ hm]
    · exact (inputTableCanonical_iff_vars primary body table).mp ht seed hs
  · exact InputTableCanonical.zero

end
end AFT.RepresentedPolynomial

import AFT.DependentTensorChannel
import AFT.FiniteRefresh
import AFT.BlockProducts

/-! # Actual finite tensor channels with dependent coordinate types -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Output : Index → Type*} [∀ i,Fintype (Input i)] [∀ i,Fintype (Output i)]

theorem dependentIndependent_map_coordinates (law : ∀ i,FiniteDist (Input i))
    (record : ∀ i,Input i → Output i) :
    (dependentIndependent law).map (fun word i => record i (word i))=
      dependentIndependent (fun i => (law i).map (record i)) := by
  ext values
  simp only [map_weight,dependentIndependent_weight]
  have he := Fintype.prod_sum (fun i point => if record i point=values i then (law i).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr rfl
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

/-- Averaging a genuine product of local probability channels gives the
product of their actual averaged laws. -/
theorem dependentIndependent_mix (law : ∀ i,FiniteDist (Input i))
    (channel : ∀ i,Input i → FiniteDist (Output i)) :
    (dependentIndependent law).mix (fun input => dependentIndependent (fun i => channel i (input i)))=
      dependentIndependent (fun i => (law i).mix (channel i)) := by
  ext output
  simp only [mix_weight,dependentIndependent_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i point => (law i).weight point*(channel i point).weight (output i))).symm

end
end AFT.FiniteDist

namespace AFT.BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Color : Type*} [Fintype Index] [Fintype Color]
  (Slots : Index → Type*) [∀ i,Fintype (Slots i)]
  {Input : Index → Type*} [∀ i,Fintype (Input i)]

/-- Keep every center explicit until the caller actually chooses to average
it. This equality is valid for arbitrary dependent local alphabets. -/
theorem blockLaw_mix (law : ∀ i,FiniteDist (Input i))
    (channel : ∀ i,Input i → FiniteDist (Slots i → Color)) :
    (FiniteDist.dependentIndependent law).mix (fun input => blockLaw Slots (fun i => channel i (input i)))=
      blockLaw Slots (fun i => (law i).mix (channel i)) := by
  ext output
  simp only [FiniteDist.mix_weight,FiniteDist.dependentIndependent_weight,blockLaw,blockMass]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i point => (law i).weight point*(channel i point).weight (fun slot => output ⟨i,slot⟩))).symm

/-- Exact sampled implementation of all local output blocks. -/
theorem blockLaw_map (law : ∀ i,FiniteDist (Input i)) (value : ∀ i,Input i → Slots i → Color) :
    (FiniteDist.dependentIndependent law).map (fun input coordinate => value coordinate.1 (input coordinate.1) coordinate.2)=
      blockLaw Slots (fun i => (law i).map (value i)) := by
  ext output
  simp only [FiniteDist.map_weight,FiniteDist.dependentIndependent_weight,blockLaw,blockMass]
  letI (i : Index) : DecidableEq (Slots i → Color) := Classical.decEq _
  have he := Fintype.prod_sum (fun i point => if value i point=(fun slot => output ⟨i,slot⟩) then (law i).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr rfl
  intro input _
  rw [Fintype.prod_ite_zero]
  congr 1
  simp only [funext_iff]
  apply propext
  constructor
  · intro h i slot
    exact h ⟨i,slot⟩
  · intro h coordinate
    exact h coordinate.1 coordinate.2

end
end AFT.BlockProducts

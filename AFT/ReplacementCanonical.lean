import AFT.SingletonSumFibers
import AFT.CanonicalJointInverse

/-! # Canonicality of a literal block channel on an arbitrary joint kernel -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {New Rest Color : Type*} [Fintype New] [Fintype Rest] [Fintype Color]
  [DecidableEq New] [DecidableEq Rest]
local instance replacementCanonicalSumDecEq (α β : Type*) : DecidableEq (α ⊕ β) := Classical.decEq _

def blockReplacement (channel : (Color → ℝ) →ₗ[ℝ] ((New → Color) → ℝ))
    (kernel : Color → (Rest → Color) → ℝ) : (New ⊕ Rest → Color) → ℝ :=
  fun word => channel (fun color => kernel color (word ∘ Sum.inr)) (word ∘ Sum.inl)

theorem blockReplacement_canonical (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (output : New → FiniteDist Color)
    (channel : (Color → ℝ) →ₗ[ℝ] ((New → Color) → ℝ))
    (hchannel : ∀ profile,Hoeffding.Canonical output Finset.univ (channel profile))
    (kernel : Color → (Rest → Color) → ℝ)
    (hkernel : Hoeffding.Canonical (Sum.elim (fun _ : Unit => primary) other) Finset.univ (singletonJoin kernel)) :
    Hoeffding.Canonical (Sum.elim output other) Finset.univ (blockReplacement channel kernel) := by
  cases Subsingleton.elim (inferInstance : DecidableEq New) (Classical.decEq New)
  cases Subsingleton.elim (inferInstance : DecidableEq Rest) (Classical.decEq Rest)
  constructor
  · intro first second heq
    have heq : first=second := funext (fun slot => heq slot (Finset.mem_univ slot))
    rw [heq]
  · intro slot _ word
    cases slot with
    | inl slot =>
      have hleft (color : Color) : Function.update word (Sum.inl slot) color ∘ Sum.inl =
          Function.update (word ∘ Sum.inl) slot color := by
        funext index
        simp [Function.update_apply]
      have hright (color : Color) : Function.update word (Sum.inl slot) color ∘ Sum.inr = word ∘ Sum.inr := by
        funext index
        simp
      simp only [blockReplacement,hleft,hright,Sum.elim_inl]
      exact (hchannel (fun color => kernel color (word ∘ Sum.inr))).2 slot (Finset.mem_univ slot) (word ∘ Sum.inl)
    | inr slot =>
      have hleft (color : Color) : Function.update word (Sum.inr slot) color ∘ Sum.inl = word ∘ Sum.inl := by
        funext index
        simp
      have hright (color : Color) : Function.update word (Sum.inr slot) color ∘ Sum.inr =
          Function.update (word ∘ Sum.inr) slot color := by
        funext index
        simp [Function.update_apply]
      have hz : (∑ color,(other slot).weight color •
          (fun input => kernel input (Function.update (word ∘ Sum.inr) slot color))) = (0 : Color → ℝ) := by
        funext input
        have hh := hkernel.2 (Sum.inr slot) (Finset.mem_univ _) (Sum.elim (fun _ => input) (word ∘ Sum.inr))
        have hu (color : Color) : Function.update (Sum.elim (fun _ : Unit => input) (word ∘ Sum.inr)) (Sum.inr slot) color =
            Sum.elim (fun _ : Unit => input) (Function.update (word ∘ Sum.inr) slot color) := by
          funext index
          cases index with
          | inl index => simp
          | inr index => simp [Function.update_apply]
        change (∑ color,(other slot).weight color*singletonJoin kernel
          (Function.update (Sum.elim (fun _ : Unit => input) (word ∘ Sum.inr)) (Sum.inr slot) color))=0 at hh
        simp_rw [hu] at hh
        simpa only [singletonJoin,Sum.elim_inr,Sum.elim_inl,Function.comp_def,
          Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hh
      simp only [blockReplacement,hleft,hright,Sum.elim_inr]
      calc
        _ = channel (∑ color,(other slot).weight color •
            (fun input => kernel input (Function.update (word ∘ Sum.inr) slot color))) (word ∘ Sum.inl) := by
          simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        _ = 0 := by rw [hz,map_zero]; rfl

end
end AFT.MixedKernel

import AFT.GroupedFiniteSeed
import AFT.JointSeedOutput

/-! # Exact leading evaluation after finite coordinate reindexing -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance finiteSeedOutputSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Slot Other Color Output : Type*} [Fintype Slot] [Fintype Other]
  [Fintype Color] [Fintype Output]

def indexedOutput (reference : Slot → FiniteDist Color) (channel : Slot → Color → Output → ℝ)
    (kernel : (Slot → Color) → ℝ) : MvPolynomial Output ℝ :=
  ∑ word,MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*
    ∏ slot,channelForm (channel slot) (word slot)

theorem seedOutput_indexed (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    seedOutput primary body primaryChannel bodyChannel seed =
      indexedOutput (inputReference primary body seed) (seedChannel primaryChannel bodyChannel seed) seed.kernel := by
  unfold seedOutput indexedOutput
  congr 1
  ext word
  simp

theorem indexedOutput_equiv (equiv : Slot ≃ Other)
    (reference : Slot → FiniteDist Color) (channel : Slot → Color → Output → ℝ)
    (kernel : (Slot → Color) → ℝ) :
    indexedOutput (fun slot => reference (equiv.symm slot))
      (fun slot => channel (equiv.symm slot)) (fun word => kernel (word ∘ equiv)) =
      indexedOutput reference channel kernel := by
  have hh := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => MvPolynomial.C (kernel word*∏ slot,(reference slot).weight (word slot))*
      ∏ slot,channelForm (channel slot) (word slot))
  apply Eq.trans ?_ hh
  unfold indexedOutput
  apply Finset.sum_congr rfl
  intro word _
  have hp := equiv.prod_comp (fun slot => (reference (equiv.symm slot)).weight (word slot))
  have hx := equiv.prod_comp (fun slot => channelForm (channel (equiv.symm slot)) (word slot))
  simp only [Equiv.symm_apply_apply] at hp hx
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_symm_mk,Function.comp_def,hp,hx]

variable {Primary Body New : Type*} [Fintype Primary] [Fintype Body] [Fintype New]

omit [Fintype Color] [Fintype Output] in
theorem mixedFiniteSeed_channel (primaryChannel bodyChannel : Color → Output → ℝ)
    (kernel : (Primary ⊕ Body → Color) → ℝ) :
    seedChannel primaryChannel bodyChannel (mixedFiniteSeed kernel) =
      fun slot => Sum.elim (fun _ : Primary => primaryChannel) (fun _ : Body => bodyChannel)
        (mixedFiniteEquiv.symm slot) := by
  funext slot
  obtain ⟨slot,rfl⟩ := mixedFiniteEquiv.surjective slot
  cases slot with
  | inl slot => simp [mixedFiniteSeed,mixedFiniteEquiv,seedChannel]
  | inr slot => simp [mixedFiniteSeed,mixedFiniteEquiv,seedChannel]

theorem mixedFiniteSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ)
    (kernel : (Primary ⊕ Body → Color) → ℝ) :
    seedOutput primary body primaryChannel bodyChannel (mixedFiniteSeed kernel)=
      indexedOutput (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))
        (Sum.elim (fun _ : Primary => primaryChannel) (fun _ : Body => bodyChannel)) kernel := by
  have hindex : seedOutput primary body primaryChannel bodyChannel (mixedFiniteSeed kernel)=
      indexedOutput (inputReference primary body (mixedFiniteSeed kernel))
        (seedChannel primaryChannel bodyChannel (mixedFiniteSeed kernel)) (mixedFiniteSeed kernel).kernel := by
    unfold seedOutput indexedOutput
    congr 1
    ext word
    simp
  rw [hindex]
  rw [mixedFiniteSeed_reference,mixedFiniteSeed_channel]
  exact indexedOutput_equiv mixedFiniteEquiv _ _ kernel

theorem groupedFiniteSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ)
    (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ) :
    seedOutput primary body primaryChannel bodyChannel (groupedFiniteSeed kernel)=
      indexedOutput (Sum.elim (fun _ : New => primary)
        (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)))
        (Sum.elim (fun _ : New => primaryChannel)
          (Sum.elim (fun _ : Primary => primaryChannel) (fun _ : Body => bodyChannel))) kernel := by
  rw [groupedFiniteSeed,mixedFiniteSeed_output]
  have he := indexedOutput_equiv (Equiv.sumAssoc New Primary Body).symm
    (Sum.elim (fun _ : New => primary) (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)))
    (Sum.elim (fun _ : New => primaryChannel) (Sum.elim (fun _ : Primary => primaryChannel) (fun _ : Body => bodyChannel))) kernel
  have hc : (fun slot => Sum.elim (fun _ : New => primaryChannel)
      (Sum.elim (fun _ : Primary => primaryChannel) (fun _ : Body => bodyChannel)) (Equiv.sumAssoc New Primary Body slot)) =
      Sum.elim (fun _ : New ⊕ Primary => primaryChannel) (fun _ : Body => bodyChannel) := by
    funext slot
    rcases slot with (slot|slot)|slot <;> rfl
  simpa only [Equiv.symm_symm,groupedFiniteSeed_reference_assoc,hc] using he

/-- The remaining old channels stay inside their actual joint contraction. -/
theorem indexedOutput_sum (reference : Slot → FiniteDist Color) (other : Other → FiniteDist Color)
    (channel : Slot → Color → Output → ℝ) (otherChannel : Other → Color → Output → ℝ)
    (kernel : (Slot ⊕ Other → Color) → ℝ) :
    indexedOutput (Sum.elim reference other) (Sum.elim channel otherChannel) kernel =
      ∑ rest,MvPolynomial.C (∏ slot,(other slot).weight (rest slot))*
        indexedOutput reference channel (fun word => kernel (Sum.elim word rest))*
        ∏ slot,channelForm (otherChannel slot) (rest slot) := by
  unfold indexedOutput
  have he := (Equiv.sumArrowEquivProdArrow Slot Other Color).symm.sum_comp
    (fun word : Slot ⊕ Other → Color =>
      MvPolynomial.C (kernel word*∏ slot,(Sum.elim reference other slot).weight (word slot))*
        ∏ slot,channelForm (Sum.elim channel otherChannel slot) (word slot))
  have hsum : (∑ word : Slot ⊕ Other → Color,
      MvPolynomial.C (kernel word*∏ slot,(Sum.elim reference other slot).weight (word slot))*
        ∏ slot,channelForm (Sum.elim channel otherChannel slot) (word slot)) =
      ∑ pair : (Slot → Color) × (Other → Color),
        MvPolynomial.C (kernel (Sum.elim pair.1 pair.2)*
          ∏ slot,(Sum.elim reference other slot).weight (Sum.elim pair.1 pair.2 slot))*
            ∏ slot,channelForm (Sum.elim channel otherChannel slot) (Sum.elim pair.1 pair.2 slot) := by
    exact he.symm
  rw [hsum,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr,map_mul]
  ring

end
end AFT.RepresentedPolynomial

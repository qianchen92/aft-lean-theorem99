import AFT.RepresentedTwoPoolKernel
import AFT.FiniteSeedOutput
import AFT.PrimaryMonomialSeed

/-! # Every literal two-pool monomial as one finite joint input seed -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def mixedProductSeed (seeds : List (InputSeed Color)) : InputSeed Color :=
  mixedFiniteSeed (twoPoolControlKernel seeds)

def mixedMonomialSeed (powers : InputSeed Color →₀ ℕ) : InputSeed Color :=
  mixedProductSeed (monomialOccurrences powers)

omit [Fintype Color] in
theorem controlPool_radius (radius : ℝ) (seeds : List (InputSeed Color)) :
    radius^Fintype.card (ControlBodySlot seeds)=radius^controlProductBodyOrder seeds := by
  have he := (controlPoolEquiv seeds).prod_comp
    (fun slot => if controlProductRole seeds slot then (1 : ℝ) else radius)
  rw [controlProductRole_radius_prod] at he
  simp only [Fintype.prod_sum_type,controlPoolEquiv,Equiv.sumCompl_apply_inl,Equiv.sumCompl_apply_inr] at he
  have hp : (∏ slot : ControlPrimarySlot seeds,if controlProductRole seeds slot.val then (1:ℝ) else radius)=1 := by
    apply Finset.prod_eq_one
    intro slot _
    exact if_pos slot.property
  have hb : (∏ slot : ControlBodySlot seeds,if controlProductRole seeds slot.val then (1:ℝ) else radius)=
      radius^Fintype.card (ControlBodySlot seeds) := by
    simp only [show ∀ slot : ControlBodySlot seeds, (if controlProductRole seeds slot.val then (1:ℝ) else radius)=radius
      from fun slot => if_neg slot.property,Finset.prod_const,Finset.card_univ]
  rw [hp,hb,one_mul] at he
  exact he

theorem mixedProductSeed_weight (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (seeds : List (InputSeed Color)) :
    inputWeight primary body primaryPool bodyPool radius (mixedProductSeed seeds)=
      controlProductActivity primary body primaryPool bodyPool radius seeds := by
  rw [mixedProductSeed,mixedFiniteSeed_weight,controlPool_radius]
  congr 1
  have he := MixedKernel.CoordinateTransport.activity_equiv (controlPoolEquiv seeds).symm
    (controlProductRate primaryPool bodyPool seeds) (controlProductReference primary body seeds) (controlProductKernel seeds)
  simpa only [Equiv.symm_symm,controlPool_rate,controlPool_reference,twoPoolControlKernel,one_div] using he

theorem mixedMonomialSeed_weight_le (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 0 ≤ radius) (powers : InputSeed Color →₀ ℕ) :
    inputWeight primary body primaryPool bodyPool radius (mixedMonomialSeed powers) ≤
      monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers := by
  rw [mixedMonomialSeed,mixedProductSeed_weight]
  exact monomial_control_activity_le _ _ _ _ _ hradius powers

theorem mixedMonomialSeed_canonical (primary body : FiniteDist Color) (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed ∈ powers.support,Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (inputReference primary body (mixedMonomialSeed powers)) Finset.univ
      (mixedMonomialSeed powers).kernel := by
  apply mixedFiniteSeed_canonical
  exact twoPoolControlKernel_canonical primary body _
    (fun seed hs => hc seed (mem_monomialOccurrences_support powers seed hs))

omit [Fintype Color] in
theorem mixedMonomialSeed_order (powers : InputSeed Color →₀ ℕ) :
    (mixedMonomialSeed powers).primaryOrder+(mixedMonomialSeed powers).bodyOrder=
      weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers := by
  change Fintype.card (ControlPrimarySlot (monomialOccurrences powers))+
    Fintype.card (ControlBodySlot (monomialOccurrences powers))=_
  rw [← Fintype.card_sum,Fintype.card_congr (controlPoolEquiv _)]
  exact monomialOccurrences_order powers

omit [Fintype Color] in
def controlProductChannel (primaryChannel bodyChannel : Color → Color → ℝ) :
    (seeds : List (InputSeed Color)) → ControlProductSlot seeds → Color → Color → ℝ
  | [], slot => PEmpty.elim slot
  | seed::rest, slot => Sum.elim (seedChannel primaryChannel bodyChannel seed)
      (controlProductChannel primaryChannel bodyChannel rest) slot

omit [Fintype Color] in
theorem controlProductChannel_role (primaryChannel bodyChannel : Color → Color → ℝ)
    (seeds : List (InputSeed Color)) (slot : ControlProductSlot seeds) :
    controlProductChannel primaryChannel bodyChannel seeds slot=
      if controlProductRole seeds slot then primaryChannel else bodyChannel := by
  induction seeds with
  | nil => exact PEmpty.elim slot
  | cons seed rest ih =>
    cases slot with
    | inr slot => exact ih slot
    | inl slot =>
      cases slot using Fin.addCases <;>
        simp only [controlProductChannel,controlProductRole,Sum.elim_inl,seedChannel,
          Fin.addCases_left,Fin.addCases_right,Bool.false_eq_true,if_false,if_true]

theorem indexedOutput_joint {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (reference : Slot → FiniteDist Color) (channel : Slot → Color → Color → ℝ)
    (kernel : (Slot → Color) → ℝ) :
    indexedOutput reference channel kernel=
      jointChannelPolynomial reference (fun slot => channelForm (channel slot)) kernel := by
  unfold indexedOutput jointChannelPolynomial
  apply Finset.sum_congr (by ext word; simp)
  intro word _
  rfl

theorem controlProduct_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (seeds : List (InputSeed Color)) :
    indexedOutput (controlProductReference primary body seeds)
      (controlProductChannel primaryChannel bodyChannel seeds) (controlProductKernel seeds)=
      (seeds.map (seedOutput primary body primaryChannel bodyChannel)).prod := by
  induction seeds with
  | nil => simp [indexedOutput,ControlProductSlot,controlProductKernel]
  | cons seed rest ih =>
    have he := jointChannelPolynomial_tensor (inputReference primary body seed)
      (controlProductReference primary body rest)
      (fun slot => channelForm (seedChannel primaryChannel bodyChannel seed slot))
      (fun slot => channelForm (controlProductChannel primaryChannel bodyChannel rest slot))
      seed.kernel (controlProductKernel rest)
    change indexedOutput _ _ (MixedKernel.tensor seed.kernel (controlProductKernel rest))=_
    have hforms : Sum.elim
        (fun slot => channelForm (seedChannel primaryChannel bodyChannel seed slot))
        (fun slot => channelForm (controlProductChannel primaryChannel bodyChannel rest slot)) =
        (fun slot => channelForm (Sum.elim (seedChannel primaryChannel bodyChannel seed)
          (controlProductChannel primaryChannel bodyChannel rest) slot)) := by
      funext slot
      cases slot <;> rfl
    rw [hforms] at he
    have hh : indexedOutput
        (Sum.elim (inputReference primary body seed) (controlProductReference primary body rest))
        (Sum.elim (seedChannel primaryChannel bodyChannel seed) (controlProductChannel primaryChannel bodyChannel rest))
        (MixedKernel.tensor seed.kernel (controlProductKernel rest))=
        indexedOutput (inputReference primary body seed) (seedChannel primaryChannel bodyChannel seed) seed.kernel *
        indexedOutput (controlProductReference primary body rest) (controlProductChannel primaryChannel bodyChannel rest)
          (controlProductKernel rest) := by
      simpa only [indexedOutput_joint] using he
    have ht : indexedOutput (controlProductReference primary body (seed::rest))
        (controlProductChannel primaryChannel bodyChannel (seed::rest))
        (MixedKernel.tensor seed.kernel (controlProductKernel rest))=
        indexedOutput (Sum.elim (inputReference primary body seed) (controlProductReference primary body rest))
        (Sum.elim (seedChannel primaryChannel bodyChannel seed) (controlProductChannel primaryChannel bodyChannel rest))
        (MixedKernel.tensor seed.kernel (controlProductKernel rest)) := by
      unfold indexedOutput
      apply Finset.sum_congr (by ext word; simp)
      intro word _
      rfl
    rw [ht,hh,ih,← seedOutput_indexed]
    rfl

theorem mixedProductSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (seeds : List (InputSeed Color)) :
    seedOutput primary body primaryChannel bodyChannel (mixedProductSeed seeds)=
      (seeds.map (seedOutput primary body primaryChannel bodyChannel)).prod := by
  rw [mixedProductSeed,mixedFiniteSeed_output]
  have he := indexedOutput_equiv (controlPoolEquiv seeds).symm
    (controlProductReference primary body seeds) (controlProductChannel primaryChannel bodyChannel seeds)
    (controlProductKernel seeds)
  have hchannel : (fun slot => controlProductChannel primaryChannel bodyChannel seeds (controlPoolEquiv seeds slot))=
      Sum.elim (fun _ : ControlPrimarySlot seeds => primaryChannel) (fun _ : ControlBodySlot seeds => bodyChannel) := by
    funext slot
    cases slot with
    | inl slot => simp [controlPoolEquiv,controlProductChannel_role,slot.property]
    | inr slot => simp [controlPoolEquiv,controlProductChannel_role,slot.property]
  have hh := he.trans (controlProduct_output primary body primaryChannel bodyChannel seeds)
  simpa only [Equiv.symm_symm,controlPool_reference,hchannel,twoPoolControlKernel] using hh

theorem mixedMonomialSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ) :
    seedOutput primary body primaryChannel bodyChannel (mixedMonomialSeed powers)=
      outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1) := by
  rw [mixedMonomialSeed,mixedProductSeed_output,monomialOccurrences_product]
  unfold outputHom
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one,one_mul]

end
end AFT.RepresentedPolynomial

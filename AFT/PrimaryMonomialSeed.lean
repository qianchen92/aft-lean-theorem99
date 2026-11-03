import AFT.PrimaryFiniteSeed
import AFT.RepresentedControlOrder
import AFT.CanonicalPolynomialChannel

/-! # Rebundling a literal all-primary monomial as its complete joint seed -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

theorem primaryFiniteSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ)
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot] (kernel : (Slot → Color) → ℝ) :
    seedOutput primary body primaryChannel bodyChannel (primaryFiniteSeed kernel)=
      jointChannelPolynomial (fun _ : Slot => primary) (fun _ => channelForm primaryChannel) kernel := by
  let equiv := Fintype.equivFin Slot
  have hh := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word : Slot → Color => MvPolynomial.C (kernel word*∏ slot,primary.weight (word slot))*
      ∏ slot,channelForm primaryChannel (word slot))
  unfold seedOutput jointChannelPolynomial
  simp only [all_primary_reference primary body (primaryFiniteSeed kernel) rfl,
    all_primary_channel primaryChannel bodyChannel (primaryFiniteSeed kernel) rfl]
  apply Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro word _
  have hp := equiv.prod_comp (fun slot => primary.weight (word slot))
  have hx := equiv.prod_comp (fun slot => channelForm primaryChannel (word slot))
  simp only [HistogramNormalization.renameWord,Equiv.coe_fn_symm_mk,Function.comp_def,hp,hx,primaryFiniteSeed]
  rfl

theorem jointChannelPolynomial_tensor {Left Right Output : Type*} [Fintype Left] [Fintype Right]
    [DecidableEq Left] [DecidableEq Right]
    (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (forms : Left → Color → Table Output) (other : Right → Color → Table Output)
    (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ) :
    jointChannelPolynomial (Sum.elim p q) (Sum.elim forms other) (MixedKernel.tensor first second)=
      jointChannelPolynomial p forms first*jointChannelPolynomial q other second := by
  unfold jointChannelPolynomial
  simp only [MixedKernel.tensor,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  let f := fun word : Left → Color => MvPolynomial.C (first word*∏ slot,(p slot).weight (word slot))*∏ slot,forms slot (word slot)
  let g := fun word : Right → Color => MvPolynomial.C (second word*∏ slot,(q slot).weight (word slot))*∏ slot,other slot (word slot)
  have he := (Equiv.sumArrowEquivProdArrow Left Right Color).sum_comp (fun pair => f pair.1*g pair.2)
  calc
    _ = ∑ pair : (Left → Color)×(Right → Color),f pair.1*g pair.2 := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro word _
      dsimp [f,g,Equiv.sumArrowEquivProdArrow]
      simp only [map_mul]
      ring
    _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

theorem controlProductReference_primary (primary body : FiniteDist Color) (seeds : List (InputSeed Color))
    (hbody : controlProductBodyOrder seeds=0) :
    controlProductReference primary body seeds=fun _ => primary := by
  induction seeds with
  | nil => funext slot; exact PEmpty.elim slot
  | cons seed rest ih =>
    have hs : seed.bodyOrder=0 ∧ controlProductBodyOrder rest=0 := by
      simpa only [controlProductBodyOrder,List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] using hbody
    funext slot
    cases slot with
    | inl slot => exact all_primary_reference primary body seed hs.1 slot
    | inr slot => exact congrFun (ih hs.2) slot

omit [Fintype Color] in
theorem controlProductRate_primary (primaryPool bodyPool : ℝ) (seeds : List (InputSeed Color))
    (hbody : controlProductBodyOrder seeds=0) :
    controlProductRate primaryPool bodyPool seeds=fun _ => (Real.sqrt primaryPool)⁻¹ := by
  induction seeds with
  | nil => funext slot; exact PEmpty.elim slot
  | cons seed rest ih =>
    have hs : seed.bodyOrder=0 ∧ controlProductBodyOrder rest=0 := by
      simpa only [controlProductBodyOrder,List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] using hbody
    funext slot
    cases slot with
    | inl slot => exact primaryCoordinates_rate primaryPool bodyPool seed slot (primaryCoordinates_complete seed hs.1 slot)
    | inr slot => exact congrFun (ih hs.2) slot

theorem controlProduct_output_primary (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (seeds : List (InputSeed Color))
    (hbody : controlProductBodyOrder seeds=0) :
    jointChannelPolynomial (fun _ : ControlProductSlot seeds => primary)
      (fun _ => channelForm primaryChannel) (controlProductKernel seeds)=
      (seeds.map (seedOutput primary body primaryChannel bodyChannel)).prod := by
  induction seeds with
  | nil => simp [jointChannelPolynomial,ControlProductSlot,controlProductKernel]
  | cons seed rest ih =>
    have hs : seed.bodyOrder=0 ∧ controlProductBodyOrder rest=0 := by
      simpa only [controlProductBodyOrder,List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] using hbody
    have he := jointChannelPolynomial_tensor (fun _ : Fin (seed.primaryOrder+seed.bodyOrder) => primary)
      (fun _ : ControlProductSlot rest => primary) (fun _ => channelForm primaryChannel)
      (fun _ => channelForm primaryChannel) seed.kernel (controlProductKernel rest)
    have hr : Sum.elim (fun _ : Fin (seed.primaryOrder+seed.bodyOrder) => primary)
      (fun _ : ControlProductSlot rest => primary)=(fun _ => primary) := by funext slot; cases slot <;> rfl
    have hf : Sum.elim (fun _ : Fin (seed.primaryOrder+seed.bodyOrder) => channelForm primaryChannel)
      (fun _ : ControlProductSlot rest => channelForm primaryChannel)=(fun _ => channelForm primaryChannel) := by
      funext slot; cases slot <;> rfl
    rw [hr,hf] at he
    change jointChannelPolynomial _ _ (MixedKernel.tensor seed.kernel (controlProductKernel rest))=_
    calc
      _ = jointChannelPolynomial (fun _ : Fin (seed.primaryOrder+seed.bodyOrder) => primary)
          (fun _ => channelForm primaryChannel) seed.kernel*
          jointChannelPolynomial (fun _ : ControlProductSlot rest => primary)
            (fun _ => channelForm primaryChannel) (controlProductKernel rest) := by convert he using 1
      _ = _ := by
        rw [ih hs.2,List.map_cons,List.prod_cons]
        congr 1
        simp only [seedOutput,jointChannelPolynomial,all_primary_reference primary body seed hs.1,
          all_primary_channel primaryChannel bodyChannel seed hs.1]

omit [Fintype Color] in
theorem monomialOccurrences_product {M : Type*} [CommMonoid M]
    (value : InputSeed Color → M) (powers : InputSeed Color →₀ ℕ) :
    ((monomialOccurrences powers).map value).prod=powers.prod (fun seed count => value seed^count) := by
  unfold monomialOccurrences Finsupp.prod
  rw [List.map_flatMap]
  have hh (seeds : List (InputSeed Color)) :
      ((seeds.flatMap fun seed => List.replicate (powers seed) (value seed)).prod)=
        (seeds.map fun seed => value seed^powers seed).prod := by
    induction seeds with
    | nil => simp
    | cons seed seeds ih => simp [List.flatMap_cons,ih]
  simpa using hh powers.support.toList

def primaryMonomialSeed (powers : InputSeed Color →₀ ℕ) : InputSeed Color :=
  primaryFiniteSeed (controlProductKernel (monomialOccurrences powers))

omit [Fintype Color] in
theorem primaryMonomialSeed_order (powers : InputSeed Color →₀ ℕ) :
    (primaryMonomialSeed powers).primaryOrder+(primaryMonomialSeed powers).bodyOrder=
      weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers := by
  simpa only [primaryMonomialSeed,primaryFiniteSeed,Nat.add_zero] using monomialOccurrences_order powers

theorem primaryMonomialSeed_output (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ)
    (hbody : controlProductBodyOrder (monomialOccurrences powers)=0) :
    seedOutput primary body primaryChannel bodyChannel (primaryMonomialSeed powers)=
      outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1) := by
  rw [primaryMonomialSeed,primaryFiniteSeed_output,
    controlProduct_output_primary primary body primaryChannel bodyChannel _ hbody,monomialOccurrences_product]
  unfold outputHom
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one,one_mul]

theorem primaryMonomialSeed_canonical (primary body : FiniteDist Color) (powers : InputSeed Color →₀ ℕ)
    (hbody : controlProductBodyOrder (monomialOccurrences powers)=0)
    (hc : ∀ seed∈powers.support,Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (inputReference primary body (primaryMonomialSeed powers)) Finset.univ
      (primaryMonomialSeed powers).kernel := by
  apply primaryFiniteSeed_canonical
  have hh := monomial_control_canonical primary body powers hc
  rwa [controlProductReference_primary primary body _ hbody] at hh

theorem primaryMonomialSeed_weight (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 0≤radius) (powers : InputSeed Color →₀ ℕ)
    (hbody : controlProductBodyOrder (monomialOccurrences powers)=0) :
    inputWeight primary body primaryPool bodyPool radius (primaryMonomialSeed powers)≤
      monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers := by
  rw [primaryMonomialSeed,primaryFiniteSeed_weight]
  have hh := monomial_control_activity_le primary body primaryPool bodyPool radius hradius powers
  simpa only [controlProductActivity,hbody,pow_zero,one_mul,
    controlProductReference_primary primary body _ hbody,controlProductRate_primary primaryPool bodyPool _ hbody] using hh

end
end AFT.RepresentedPolynomial

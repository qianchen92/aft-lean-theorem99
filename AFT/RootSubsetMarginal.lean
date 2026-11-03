import AFT.RootExchangeability
import AFT.LocalTensors
import AFT.RootANOVAAsymptotic

/-! # Exact arbitrary-subset marginals of the conditioned root word -/
namespace AFT.RootSlice
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootSubsetMarginalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Source Slot Other : Type*} [Fintype Source] [Fintype Slot] [Fintype Other]

/-- Relabeling every coordinate transports the full conditioned law,
including its actual normalizer, to the law on the new coordinate type. -/
theorem law_map_equiv (source : FiniteDist Source) (score : Source → ℤ) (target : ℤ)
    (equiv : Slot ≃ Other)
    (hfirst : 0<probability (fun _ : Slot => source) score target)
    (hsecond : 0<probability (fun _ : Other => source) score target) :
    (law (fun _ : Slot => source) score target hfirst).map (Equiv.arrowCongr equiv (Equiv.refl Source)) =
      law (fun _ : Other => source) score target hsecond := by
  ext word
  rw [FiniteDist.map_equiv_weight]
  have hsum : integerSum score ((Equiv.arrowCongr equiv (Equiv.refl Source)).symm word)=integerSum score word := by
    change (∑ slot,score (word (equiv slot)))=∑ other,score (word other)
    exact equiv.sum_comp (fun other => score (word other))
  have hprod : (∏ slot,source.weight (((Equiv.arrowCongr equiv (Equiv.refl Source)).symm word) slot))=
      ∏ other,source.weight (word other) := by
    change (∏ slot,source.weight (word (equiv slot)))=∏ other,source.weight (word other)
    exact equiv.prod_comp (fun other => source.weight (word other))
  simp only [law,FiniteDist.condition,FiniteDist.independent,hsum,hprod]
  congr 1
  exact probability_const_equiv source score target equiv

omit [Fintype Other] in
/-- Selected coordinates precede the complement, with no omitted index
and with the actual selected enumeration made explicit. -/
def subsetCoordinates (selected : Finset Slot) :
    Slot ≃ Fin (selected.card+(Fintype.card Slot-selected.card)) :=
  (Equiv.sumCompl (fun slot => slot∈selected)).symm |>.trans
    ((Equiv.sumCongr (Fintype.equivOfCardEq (by simp : Fintype.card selected=Fintype.card (Fin selected.card)))
      (Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl] :
        Fintype.card {slot : Slot // slot∉selected}=Fintype.card (Fin (Fintype.card Slot-selected.card))))).trans
      finSumFinEquiv)

omit [Fintype Other] in
/-- The literal chosen-coordinate restriction associated to the split. -/
def subsetPrefix (selected : Finset Slot) (word : Slot → Source) : Fin selected.card → Source :=
  fun index => word ((subsetCoordinates selected).symm (Fin.castAdd (Fintype.card Slot-selected.card) index))

omit [Fintype Other] in
def subsetEnumeration (selected : Finset Slot) : Fin selected.card ≃ selected :=
  (Fintype.equivOfCardEq (by simp : Fintype.card selected=Fintype.card (Fin selected.card))).symm

omit [Fintype Other] [Fintype Source] in
theorem subsetPrefix_apply (selected : Finset Slot) (word : Slot → Source) (index : Fin selected.card) :
    subsetPrefix selected word index=word (subsetEnumeration selected index) := by
  simp [subsetPrefix,subsetCoordinates,subsetEnumeration,Equiv.sumCompl]

omit [Fintype Other] in
/-- Every actual selected subset has the same finite conditioned prefix
law after its explicit enumeration. This is stronger than marginal equality. -/
theorem law_subsetPrefix (source : FiniteDist Source) (score : Source → ℤ)
    (selected : Finset Slot) (hfirst : 0<probability (fun _ : Slot => source) score 0)
    (hsecond : 0<sumProbability source score (selected.card+(Fintype.card Slot-selected.card)) 0) :
    (law (fun _ : Slot => source) score 0 hfirst).map (subsetPrefix selected)=
      prefixLaw source score selected.card (Fintype.card Slot-selected.card) hsecond := by
  have hh := law_map_equiv source score 0 (subsetCoordinates selected) hfirst hsecond
  unfold prefixLaw
  rw [← hh,FiniteDist.map_map]
  rfl

end
end AFT.RootSlice

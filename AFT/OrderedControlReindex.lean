import AFT.PublicRoleStatistic
import AFT.OrderedSeedFactors

/-! # Reordering actual seed occurrences preserves the full paired statistic -/
namespace AFT.RepresentedPolynomial
open CanonicalMoments V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Color : Type*} [Fintype Color]

omit [Fintype Color] in
/-- Every occurrence permutation has a role-preserving coordinate bijection.
No kernel is factored into rank-one components. -/
theorem controlProduct_permutation {first second : List (InputSeed Color)} (h : first.Perm second) :
    ∃ e : ControlProductSlot first ≃ ControlProductSlot second,
      (∀ slot,controlProductRole second (e slot)=controlProductRole first slot) ∧
      (∀ word,controlProductKernel first (word ∘ e)=controlProductKernel second word) := by
  induction h with
  | nil => exact ⟨Equiv.refl _,(fun slot => PEmpty.elim slot),(fun _ => rfl)⟩
  | @cons seed first second h ih =>
    obtain ⟨e,hr,hk⟩ := ih
    refine ⟨Equiv.sumCongr (Equiv.refl _) e,?_,?_⟩
    · intro slot
      cases slot with
      | inl slot => rfl
      | inr slot => exact hr slot
    · intro word
      change seed.kernel (word ∘ Sum.inl)*controlProductKernel first ((word ∘ Sum.inr) ∘ e)=_
      rw [hk]
      rfl
  | swap second first rest =>
    let e : ControlProductSlot (first::second::rest) ≃ ControlProductSlot (second::first::rest) :=
      (Equiv.sumAssoc _ _ _).symm.trans
        ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))
    refine ⟨e,?_,?_⟩
    · intro slot
      rcases slot with slot|slot|slot <;> rfl
    · intro word
      change first.kernel (word ∘ Sum.inr ∘ Sum.inl)*
          (second.kernel (word ∘ Sum.inl)*controlProductKernel rest (word ∘ Sum.inr ∘ Sum.inr))=
        second.kernel (word ∘ Sum.inl)*
          (first.kernel (word ∘ Sum.inr ∘ Sum.inl)*controlProductKernel rest (word ∘ Sum.inr ∘ Sum.inr))
      ring
  | trans hfirst hsecond ihfirst ihsecond =>
    obtain ⟨first,hfr,hfk⟩ := ihfirst
    obtain ⟨second,hsr,hsk⟩ := ihsecond
    refine ⟨first.trans second,?_,?_⟩
    · intro slot
      exact (hsr (first slot)).trans (hfr slot)
    · intro word
      exact (hfk (word ∘ second)).trans (hsk word)

/-- The complete two-pool statistic, including the compensator score and
without-replacement denominators, is independent of the occurrence order. -/
theorem twoPoolPairedStatistic_permutation (primary body : FiniteDist Color)
    (anchor : Color → Color → ℝ) (activation : ℝ)
    {first second : List (InputSeed Color)} (h : first.Perm second)
    {PP BP : Type*} [Fintype PP] [Fintype BP] (word : PP ⊕ BP → Color × Color) :
    twoPoolStatistic (twoPoolPairedKernel primary body anchor activation first) word=
      twoPoolStatistic (twoPoolPairedKernel primary body anchor activation second) word := by
  obtain ⟨e,hr,hk⟩ := controlProduct_permutation h
  let ep : ControlPrimarySlot first ≃ ControlPrimarySlot second :=
    Equiv.subtypeEquiv e (fun slot => by rw [hr])
  let eb : ControlBodySlot first ≃ ControlBodySlot second :=
    Equiv.subtypeEquiv e (fun slot => by rw [hr])
  have hpool (slot : ControlPrimarySlot first ⊕ ControlBodySlot first) :
      controlPoolEquiv second (Equiv.sumCongr ep eb slot)=e (controlPoolEquiv first slot) := by
    cases slot <;> rfl
  have hkernel : (fun input => twoPoolControlKernel first (input ∘ Equiv.sumCongr ep eb))=
      twoPoolControlKernel second := by
    funext input
    unfold twoPoolControlKernel
    rw [← hk (input ∘ (controlPoolEquiv second).symm)]
    congr 1
    funext slot
    change input (Equiv.sumCongr ep eb ((controlPoolEquiv first).symm slot))=
      input ((controlPoolEquiv second).symm (e slot))
    apply congrArg input
    apply (controlPoolEquiv second).injective
    rw [hpool,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hpaired := pairedPublicKernel_sum_reindex primary body anchor activation ep eb (twoPoolControlKernel first)
  rw [hkernel] at hpaired
  have hh := twoPoolStatistic_reindex ep eb (Equiv.refl PP) (Equiv.refl BP)
    (twoPoolPairedKernel primary body anchor activation first) word
  simpa only [twoPoolPairedKernel,←hpaired,Equiv.sumCongr_refl,Equiv.coe_refl,Function.comp_id] using hh.symm


omit [Fintype Color] in
theorem monomialOccurrences_count (powers : InputSeed Color →₀ ℕ) (seed : InputSeed Color) :
    (monomialOccurrences powers).count seed=powers seed := by
  simp only [monomialOccurrences,List.count_flatMap,Function.comp_def,List.count_replicate,beq_iff_eq]
  change (powers.support.toList.map (fun other => if other=seed then powers other else 0)).sum=powers seed
  rw [Finset.sum_map_toList]
  by_cases hs : seed∈powers.support
  · simp [hs]
  · have hz : powers seed=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hs
    simp [hs,hz]

omit [Fintype Color] in
theorem orderedSeedPowers_count {Code : Type*} (decode : Code → InputSeed Color)
    (factors : List Code) (seed : InputSeed Color) :
    RationalNumerics.orderedSeedPowers decode factors seed=(factors.map decode).count seed := by
  induction factors with
  | nil => simp [RationalNumerics.orderedSeedPowers]
  | cons code rest ih =>
    simp only [RationalNumerics.orderedSeedPowers,Finsupp.add_apply,Finsupp.single_apply,ih,
      List.map_cons,List.count_cons,beq_iff_eq]
    split_ifs <;> omega

omit [Fintype Color] in
theorem orderedSeedPowers_occurrences {Code : Type*} (decode : Code → InputSeed Color) (factors : List Code) :
    (factors.map decode).Perm (monomialOccurrences (RationalNumerics.orderedSeedPowers decode factors)) := by
  apply List.perm_iff_count.mpr
  intro seed
  rw [monomialOccurrences_count,orderedSeedPowers_count]

/-- The executable ordered list gives exactly the original represented
paired score, even when two distinct codes decode to the same real seed. -/
theorem orderedSeedTerm_paired_score {Code : Type*} (decode : Code → InputSeed Color)
    (primary body : FiniteDist Color) (anchor : Color → Color → ℝ) (activation : ℝ)
    (primaryPool bodyPool : ℕ) (term : RationalNumerics.OrderedSeedTerm Code)
    (word : Fin primaryPool ⊕ Fin bodyPool → Color × Color) :
    tablePairedStatistic primary body anchor activation primaryPool bodyPool (term.interpret decode) word=
      (term.coefficient : ℝ)*twoPoolStatistic
        (twoPoolPairedKernel primary body anchor activation (term.factors.map decode)) word := by
  rw [RationalNumerics.OrderedSeedTerm.interpret_monomial,tablePairedStatistic_monomial]
  change _*twoPoolStatistic (twoPoolPairedKernel primary body anchor activation
    (monomialOccurrences (RationalNumerics.orderedSeedPowers decode term.factors))) word=_
  rw [twoPoolPairedStatistic_permutation primary body anchor activation
    (orderedSeedPowers_occurrences decode term.factors)]

end
end AFT.RepresentedPolynomial

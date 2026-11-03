import CurrentAFT.BinaryFullResponseCounts
import CurrentAFT.BinaryTwoPoolAverage
import CurrentAFT.BinaryWeightResources

/-! # Actual counter-generated independent without-replacement control choices -/
namespace CurrentAFT.BinaryControlChoiceAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryFullResponseCounts.current BinaryTwoPoolAverage.current
  PublicParameterProgram.modulus BinaryProposalMetadata.counts Parameters.legCount BackgroundRates.ordinaryPool

abbrev PrimaryPool (security : ℕ) := Fin (BinaryFullResponseCounts.current security).leg
abbrev BodyPool (security : ℕ) := Fin (BinaryFullResponseCounts.current security).ordinary
abbrev Choice (security r s : ℕ) := (Fin r ↪ PrimaryPool security) × (Fin s ↪ BodyPool security)

def current (security order : ℕ) (source : TruncatedArity order)
    (kernel : Vector (PrimaryPool security) source.val.1.val → Vector (BodyPool security) source.val.2.val → RationalResult) : RationalResult :=
  let counts := BinaryFullResponseCounts.current security
  let result := BinaryTwoPoolAverage.current counts.leg counts.ordinary source.val.1.val source.val.2.val
    (BinaryFullResponseCounts.positive security).1 (BinaryFullResponseCounts.positive security).2.1 kernel
  ⟨result.data,counts.work+result.work+2⟩

def choiceEquiv (security r s : ℕ) : Choice security r s ≃ UniformTaggedOutput.Choice security r s :=
  Equiv.prodCongr
    (Equiv.embeddingCongr (Equiv.refl (Fin r)) (finCongr (BinaryFullResponseCounts.current_value security).1))
    (Equiv.embeddingCongr (Equiv.refl (Fin s)) (finCongr (BinaryFullResponseCounts.current_value security).2.1))

noncomputable section
open scoped Classical
theorem current_value (security order : ℕ) (source : TruncatedArity order)
    (kernel : Vector (PrimaryPool security) source.val.1.val → Vector (BodyPool security) source.val.2.val → RationalResult) :
    (current security order source kernel).data.decode=
      (∑ primary : Fin source.val.1.val ↪ PrimaryPool security, ∑ body : Fin source.val.2.val ↪ BodyPool security,
        (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)/
        (((BinaryFullResponseCounts.current security).leg.descFactorial source.val.1.val:ℚ)*
          ((BinaryFullResponseCounts.current security).ordinary.descFactorial source.val.2.val:ℚ)) :=
  BinaryTwoPoolAverage.current_value _ _ _ _ _ _ kernel

private theorem sum_embeddings (primaryPool bodyPool r s : ℕ)
    (kernel : (Fin r ↪ Fin primaryPool) → (Fin s ↪ Fin bodyPool) → ℚ) :
    (∑ primary, ∑ body, kernel primary body)=∑ choice : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool), kernel choice.1 choice.2 :=
  (Fintype.sum_prod_type (fun choice => kernel choice.1 choice.2)).symm

theorem current_value_actual (security order : ℕ) (source : TruncatedArity order)
    (kernel : Vector (PrimaryPool security) source.val.1.val → Vector (BodyPool security) source.val.2.val → RationalResult)
    (value : UniformTaggedOutput.Choice security source.val.1.val source.val.2.val → ℚ)
    (hvalue : ∀ choice : Choice security source.val.1.val source.val.2.val,
      (kernel (Vector.ofFn choice.1) (Vector.ofFn choice.2)).data.decode=value (choiceEquiv security _ _ choice)) :
    (current security order source kernel).data.decode=
      (∑ choice : UniformTaggedOutput.Choice security source.val.1.val source.val.2.val, value choice)/
        (((Parameters.legCount security).descFactorial source.val.1.val:ℚ)*
          ((BackgroundRates.ordinaryPool security).descFactorial source.val.2.val:ℚ)) := by
  rw [current_value]
  have hsum : (∑ primary : Fin source.val.1.val ↪ PrimaryPool security, ∑ body : Fin source.val.2.val ↪ BodyPool security,
      (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)=
      ∑ choice : UniformTaggedOutput.Choice security source.val.1.val source.val.2.val, value choice := by
    rw [sum_embeddings (BinaryFullResponseCounts.current security).leg (BinaryFullResponseCounts.current security).ordinary
      source.val.1.val source.val.2.val (fun primary body => (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)]
    calc
      _ = ∑ choice : Choice security source.val.1.val source.val.2.val, value (choiceEquiv security _ _ choice) :=
        Finset.sum_congr rfl (fun choice _ => hvalue choice)
      _ = _ := (choiceEquiv security _ _).sum_comp value
  rw [hsum,(BinaryFullResponseCounts.current_value security).1,(BinaryFullResponseCounts.current_value security).2.1]

noncomputable def heightPolynomial (order : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ source : TruncatedArity order, BinaryWeightResources.averageHeightPolynomial BinaryProposalMetadata.sizePolynomial
    BinaryProposalMetadata.sizePolynomial source.val.1.val source.val.2.val leafHeight
noncomputable def workPolynomial (order : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFullResponseCounts.workPolynomial+
    (∑ source : TruncatedArity order, BinaryWeightResources.averageWorkPolynomial BinaryProposalMetadata.sizePolynomial
      BinaryProposalMetadata.sizePolynomial source.val.1.val source.val.2.val leafHeight leafWork)+2

theorem current_bounds (security order : ℕ) (source : TruncatedArity order) (leafHeight leafWork : Polynomial ℕ)
    (kernel : Vector (PrimaryPool security) source.val.1.val → Vector (BodyPool security) source.val.2.val → RationalResult)
    (hh : ∀ primary body, HeightBound (kernel primary body).data.decode (leafHeight.eval security))
    (hw : ∀ primary body, (kernel primary body).work ≤ leafWork.eval security) :
    HeightBound (current security order source kernel).data.decode ((heightPolynomial order leafHeight).eval security) ∧
      (current security order source kernel).work ≤ (workPolynomial order leafHeight leafWork).eval security := by
  let counts := BinaryFullResponseCounts.current security
  have hp : counts.leg ≤ BinaryProposalMetadata.sizePolynomial.eval security :=
    (BinaryFullResponseCounts.current_sizes security).1.trans_eq (BinaryProposalMetadata.sizePolynomial_eval security).symm
  have hb : counts.ordinary ≤ BinaryProposalMetadata.sizePolynomial.eval security :=
    (BinaryFullResponseCounts.current_sizes security).2.1.trans_eq (BinaryProposalMetadata.sizePolynomial_eval security).symm
  have h := BinaryTwoPoolAverage.current_bounds counts.leg counts.ordinary source.val.1.val source.val.2.val
    (BinaryFullResponseCounts.positive security).1 (BinaryFullResponseCounts.positive security).2.1 kernel
    (leafHeight.eval security) (leafWork.eval security) hh hw
  have hheight := BinaryWeightResources.averageHeight_mono (r := source.val.1.val) (s := source.val.2.val) hp hb (le_refl (leafHeight.eval security))
  have hwork := BinaryWeightResources.averageWork_mono (r := source.val.1.val) (s := source.val.2.val) hp hb
    (le_refl (leafHeight.eval security)) (le_refl (leafWork.eval security))
  have hh' : BinaryTwoPoolAverage.height counts.leg counts.ordinary source.val.1.val source.val.2.val (leafHeight.eval security) ≤
      (heightPolynomial order leafHeight).eval security := by
    apply hheight.trans
    rw [heightPolynomial,Polynomial.eval_finset_sum]
    have hs := Finset.single_le_sum (f := fun arity : TruncatedArity order =>
      (BinaryWeightResources.averageHeightPolynomial BinaryProposalMetadata.sizePolynomial BinaryProposalMetadata.sizePolynomial
        arity.val.1.val arity.val.2.val leafHeight).eval security) (fun _ _ => Nat.zero_le _) (Finset.mem_univ source)
    simpa only [BinaryWeightResources.averageHeightPolynomial_eval] using hs
  have hw' : BinaryTwoPoolAverage.work counts.leg counts.ordinary source.val.1.val source.val.2.val (leafHeight.eval security) (leafWork.eval security) ≤
      ∑ arity : TruncatedArity order, (BinaryWeightResources.averageWorkPolynomial BinaryProposalMetadata.sizePolynomial
        BinaryProposalMetadata.sizePolynomial arity.val.1.val arity.val.2.val leafHeight leafWork).eval security := by
    apply hwork.trans
    have hs := Finset.single_le_sum (f := fun arity : TruncatedArity order =>
      (BinaryWeightResources.averageWorkPolynomial BinaryProposalMetadata.sizePolynomial BinaryProposalMetadata.sizePolynomial
        arity.val.1.val arity.val.2.val leafHeight leafWork).eval security) (fun _ _ => Nat.zero_le _) (Finset.mem_univ source)
    simpa only [BinaryWeightResources.averageWorkPolynomial_eval] using hs
  refine ⟨h.1.mono hh',?_⟩
  have wc := BinaryFullResponseCounts.current_work security
  have wr := h.2.trans hw'
  change counts.work+(BinaryTwoPoolAverage.current _ _ _ _ _ _ _).work+2 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_finset_sum,Polynomial.eval_ofNat]
  change counts.work ≤ _ at wc
  dsimp only [counts] at wr wc ⊢
  omega

end
end CurrentAFT.BinaryControlChoiceAverage

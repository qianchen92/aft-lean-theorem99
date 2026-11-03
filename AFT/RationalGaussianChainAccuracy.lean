import AFT.RationalGaussianChain
import AFT.CountableChannelComposition
import AFT.TransportBound

/-! # Full joint accuracy of the literal rational-centered bit program -/
namespace AFT.RationalNumerics
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {Output : Type*} [Fintype Output]

def RationalGaussianChain.exactChannel {count : ℕ} (chain : RationalGaussianChain count)
    (hw : chain.realChain.Wide 1) (channel : (Fin count → ℤ) → FiniteDist Output) : FiniteDist Output :=
  FiniteDist.countableMix chain.realChain.sequentialMass
    (chain.realChain.sequentialMass_nonneg 1 zero_lt_one hw)
    (chain.realChain.sequentialMass_probability 1 zero_lt_one hw).1
    (chain.realChain.sequentialMass_probability 1 zero_lt_one hw).2 channel

/-- Exact countable Fubini for the conditional scalar draws; the random
center depends on the entire realized tail throughout this identity. -/
theorem RationalGaussianChain.exactChannel_cons {count : ℕ} (squaredWidth : ℚ)
    (center : (Fin count → ℤ) → ℚ) (tail : RationalGaussianChain count)
    (hw : (RationalGaussianChain.cons squaredWidth center tail).realChain.Wide 1)
    (channel : (Fin (count+1) → ℤ) → FiniteDist Output) :
    (RationalGaussianChain.cons squaredWidth center tail).exactChannel hw channel=
      tail.exactChannel hw.2 (fun word => FiniteDist.countableMix
        (centeredScalarMass (Real.sqrt (squaredWidth : ℝ)) (center word))
        (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hw.1))
        (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hw.1))
        (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hw.1))
        (fun first => channel (Fin.cons first word))) := by
  let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
  have he (point : (Fin count → ℤ) × ℤ) : equiv point=Fin.cons point.2 point.1 := by cases point;rfl
  ext output
  change (∑' word,(RationalGaussianChain.cons squaredWidth center tail).realChain.sequentialMass word*
    (channel word).weight output)=_
  rw [←equiv.tsum_eq]
  have hs := FiniteDist.countableChannel_summable _
    ((RationalGaussianChain.cons squaredWidth center tail).realChain.sequentialMass_probability 1 zero_lt_one hw).1
    channel output
  have hp := equiv.summable_iff.mpr hs
  simp only [Function.comp_def,he,RationalGaussianChain.realChain,GaussianChain.sequentialMass,Fin.tail_cons,Fin.cons_zero] at hp ⊢
  rw [hp.tsum_prod]
  change _=∑' word,tail.realChain.sequentialMass word*
    (∑' first,centeredScalarMass (Real.sqrt (squaredWidth : ℝ)) (center word) first*
      (channel (Fin.cons first word)).weight output)
  apply tsum_congr
  intro word
  rw [←tsum_mul_left]
  apply tsum_congr
  intro first
  unfold centeredScalarMass
  ring

def RationalGaussianChain.WidthsLe (upper : ℝ) : {count : ℕ} → RationalGaussianChain count → Prop
  | 0,.nil => True
  | _+1,.cons squaredWidth _ tail => Real.sqrt (squaredWidth : ℝ)≤upper ∧ tail.WidthsLe upper

def centeredScalarError (upper : ℝ) (cutoff bits : ℕ) : ℝ :=
  1/(2 : ℝ)^bits+810*upper*Real.exp (-Real.pi*((cutoff : ℝ)-1)^2/(2*upper^2))

private theorem scalar_error_mono (width upper : ℝ) (cutoff bits : ℕ)
    (hw : 0<width) (hu : width≤upper) :
    1/(2 : ℝ)^bits+810*width*Real.exp (-Real.pi*((cutoff : ℝ)-1)^2/(2*width^2))≤
      centeredScalarError upper cutoff bits := by
  have hu0 : 0<upper := hw.trans_le hu
  unfold centeredScalarError
  apply add_le_add le_rfl
  apply mul_le_mul
  · gcongr
  · apply Real.exp_le_exp.mpr
    have hnum : 0≤Real.pi*((cutoff : ℝ)-1)^2 := by positivity
    have hden : 2*width^2≤2*upper^2 := by nlinarith
    have hh := div_le_div_of_nonneg_left hnum (by positivity : 0<2*width^2) hden
    simpa only [neg_mul,neg_div] using neg_le_neg hh
  · exact (Real.exp_pos _).le
  · positivity

/-- Total joint error is at most the sum of the actual scalar errors.
This applies to every finite physical channel of the entire sampled word. -/
theorem RationalGaussianChain.finiteChannel_accuracy {count : ℕ} (chain : RationalGaussianChain count)
    (hw : chain.realChain.Wide 1) (upper : ℝ) (hu : chain.WidthsLe upper)
    (cutoff bits : ℕ) (hc : 1≤cutoff) (channel : (Fin count → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound (chain.finiteChannel cutoff bits channel) (chain.exactChannel hw channel)
      (count*centeredScalarError upper cutoff bits) := by
  induction chain with
  | nil =>
    have he : RationalGaussianChain.nil.exactChannel hw channel=channel Fin.elim0 := by
      ext output
      change (∑' word : Fin 0 → ℤ,1*(channel word).weight output)=(channel Fin.elim0).weight output
      simp only [one_mul,tsum_fintype,Fintype.sum_unique]
      have he (word : Fin 0 → ℤ) : word=Fin.elim0 := by funext index;exact Fin.elim0 index
      exact congrArg (fun word => (channel word).weight output) (he _)
    rw [he]
    intro event
    simp [finiteChannel]
  | @cons count squaredWidth center tail ih =>
    let actual (word : Fin count → ℤ) := FiniteDist.countableMix
      (centeredScalarMass (Real.sqrt (squaredWidth : ℝ)) (center word))
      (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hw.1))
      (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hw.1))
      (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hw.1))
      (fun first => channel (Fin.cons first word))
    let computed (word : Fin count → ℤ) :=
      (centeredTicketLaw squaredWidth (center word) cutoff bits).mix
        (fun offset => channel (Fin.cons (centeredGaussianAnchor (center word)+offset) word))
    have hsquare : (squaredWidth : ℝ)=(Real.sqrt (squaredWidth : ℝ))^2 :=
      (Real.sq_sqrt (Real.sqrt_pos.mp (zero_lt_one.trans_le hw.1)).le).symm
    have hstep (word : Fin count → ℤ) : FiniteDist.TVBound (computed word) (actual word)
        (centeredScalarError upper cutoff bits) :=
      (centeredTicketLaw_channel_tv squaredWidth (center word) _ cutoff bits hw.1 hsquare hc
        (fun first => channel (Fin.cons first word))).mono
          (scalar_error_mono _ upper cutoff bits (zero_lt_one.trans_le hw.1) hu.1)
    have hfirst : FiniteDist.TVBound (tail.finiteChannel cutoff bits computed)
        (tail.finiteChannel cutoff bits actual) (centeredScalarError upper cutoff bits) := by
      rw [←tail.draw_channel cutoff bits computed,←tail.draw_channel cutoff bits actual]
      exact FiniteDist.TVBound.mix_right _ (fun randomness => hstep (tail.draw cutoff bits randomness).get)
    have hsecond := ih hw.2 hu.2 actual
    have hh := hfirst.triangle hsecond
    rw [exactChannel_cons]
    simpa only [finiteChannel,computed,actual,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh

end
end AFT.RationalNumerics

import AFT.ScalarProgramResources
import AFT.NumericalPairedScore

/-! # Stable scalar expressions with exact rational inverses

Actual source weights are numerical atoms. The only inverse syntax allowed
here is an inverse of a rational literal, which is evaluated exactly; no
lower bound on an unevaluated real scalar is silently assumed.
-/
namespace AFT.RationalNumerics
namespace ScalarProgram
variable {Scalar : Type*}

 def exactInverseSyntax : ScalarProgram Scalar → Prop
  | .rational _ => True
  | .atom _ => True
  | .add first second => first.exactInverseSyntax ∧ second.exactInverseSyntax
  | .multiply first second => first.exactInverseSyntax ∧ second.exactInverseSyntax
  | .negate term => term.exactInverseSyntax
  | .inverse term => ∃ value : ℚ,term=.rational value

 def literalMagnitude (bound : ℝ) : ScalarProgram Scalar → Prop
  | .rational value => |(value : ℝ)|≤bound
  | .atom _ => True
  | .add first second => first.literalMagnitude bound ∧ second.literalMagnitude bound
  | .multiply first second => first.literalMagnitude bound ∧ second.literalMagnitude bound
  | .negate term => term.literalMagnitude bound
  | .inverse term => ∀ value : ℚ,term=.rational value → |((value : ℝ)⁻¹)|≤bound

 theorem stable_evaluation (realLeaf : Scalar → ℝ) (rationalLeaf : Scalar → ℚ)
    (bound error : ℝ) (hb : 2≤bound) (he : 0≤error)
    (hr : ∀ code,|realLeaf code|≤bound)
    (hq : ∀ code,|(rationalLeaf code : ℝ)|≤bound)
    (hd : ∀ code,|(rationalLeaf code : ℝ)-realLeaf code|≤error)
    (program : ScalarProgram Scalar) (hi : program.exactInverseSyntax)
    (hl : program.literalMagnitude bound) :
    |program.denote realLeaf|≤bound^program.nodes ∧
      |(program.run rationalLeaf : ℝ)|≤bound^program.nodes ∧
      |(program.run rationalLeaf : ℝ)-program.denote realLeaf|≤(program.nodes : ℝ)*error*bound^program.nodes := by
  have hb0 : 0≤bound := by linarith
  have hb1 : 1≤bound := by linarith
  have hpow (a b : ℕ) : bound^a≤bound^(a+b) := pow_le_pow_right₀ hb1 (Nat.le_add_right _ _)
  induction program with
  | rational value =>
    simp only [run,denote,nodes,pow_one,sub_self,abs_zero,Nat.cast_one,one_mul]
    exact ⟨hl,hl,by positivity⟩
  | atom code =>
    simp only [run,denote,nodes,pow_one,Nat.cast_one,one_mul]
    exact ⟨hr code,hq code,(hd code).trans (le_mul_of_one_le_right he hb1)⟩
  | add first second hf hs =>
    obtain ⟨hfr,hfq,hfd⟩ := hf hi.1 hl.1
    obtain ⟨hsr,hsq,hsd⟩ := hs hi.2 hl.2
    have hp1 := hpow first.nodes second.nodes
    have hp2 : bound^second.nodes≤bound^(first.nodes+second.nodes) := by simpa only [Nat.add_comm] using hpow second.nodes first.nodes
    have hsum : bound^first.nodes+bound^second.nodes≤bound^(first.nodes+second.nodes+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hb0 (first.nodes+second.nodes)]
    simp only [run,denote,nodes,Rat.cast_add]
    refine ⟨(abs_add_le _ _).trans ((add_le_add hfr hsr).trans hsum),
      (abs_add_le _ _).trans ((add_le_add hfq hsq).trans hsum),?_⟩
    rw [show (first.run rationalLeaf : ℝ)+(second.run rationalLeaf : ℝ)-
      (first.denote realLeaf+second.denote realLeaf)=
      ((first.run rationalLeaf : ℝ)-first.denote realLeaf)+
        ((second.run rationalLeaf : ℝ)-second.denote realLeaf) by ring]
    have hsumerror := (abs_add_le _ _).trans (add_le_add hfd hsd)
    apply hsumerror.trans
    have ha := mul_le_mul_of_nonneg_left hp1 (show 0≤(first.nodes : ℝ)*error by positivity)
    have hb := mul_le_mul_of_nonneg_left hp2 (show 0≤(second.nodes : ℝ)*error by positivity)
    have hc : ((first.nodes : ℝ)+(second.nodes : ℝ))*error*bound^(first.nodes+second.nodes)≤
        ((first.nodes : ℝ)+(second.nodes : ℝ)+1)*error*bound^(first.nodes+second.nodes+1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) he)
        (pow_le_pow_right₀ hb1 (Nat.le_succ _)) (by positivity) (by positivity)
    push_cast
    nlinarith
  | multiply first second hf hs =>
    obtain ⟨hfr,hfq,hfd⟩ := hf hi.1 hl.1
    obtain ⟨hsr,hsq,hsd⟩ := hs hi.2 hl.2
    have hpp : bound^first.nodes*bound^second.nodes≤bound^(first.nodes+second.nodes+1) := by
      rw [←pow_add]
      exact pow_le_pow_right₀ hb1 (Nat.le_succ _)
    simp only [run,denote,nodes,Rat.cast_mul]
    refine ⟨?_,?_,?_⟩
    · rw [abs_mul]
      exact (mul_le_mul hfr hsr (abs_nonneg _) (by positivity)).trans hpp
    · rw [abs_mul]
      exact (mul_le_mul hfq hsq (abs_nonneg _) (by positivity)).trans hpp
    · rw [show (first.run rationalLeaf : ℝ)*(second.run rationalLeaf : ℝ)-
          first.denote realLeaf*second.denote realLeaf=
        ((first.run rationalLeaf : ℝ)-first.denote realLeaf)*second.denote realLeaf+
          (first.run rationalLeaf : ℝ)*((second.run rationalLeaf : ℝ)-second.denote realLeaf) by ring]
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      apply (add_le_add (mul_le_mul hfd hsr (abs_nonneg _) (by positivity))
        (mul_le_mul hfq hsd (abs_nonneg _) (by positivity))).trans
      calc
        _ = ((first.nodes : ℝ)+(second.nodes : ℝ))*error*(bound^first.nodes*bound^second.nodes) := by ring
        _ ≤ ((first.nodes : ℝ)+(second.nodes : ℝ)+1)*error*bound^(first.nodes+second.nodes+1) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) he) hpp (by positivity) (by positivity)
        _ = _ := by push_cast; ring
  | negate term ht =>
    obtain ⟨htr,htq,htd⟩ := ht hi hl
    have hp := pow_le_pow_right₀ hb1 (Nat.le_succ term.nodes)
    simp only [run,denote,nodes,Rat.cast_neg,abs_neg]
    refine ⟨htr.trans hp,htq.trans hp,?_⟩
    rw [show -(term.run rationalLeaf : ℝ)- -term.denote realLeaf=
      -((term.run rationalLeaf : ℝ)-term.denote realLeaf) by ring,abs_neg]
    apply htd.trans
    push_cast
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) he) hp (by positivity) (by positivity)
  | inverse term _ =>
    obtain ⟨value,rfl⟩ := hi
    have hv := hl value rfl
    simp only [run,denote,nodes,Rat.cast_inv,sub_self,abs_zero]
    have hp : bound≤bound^(1+1) := by simpa only [pow_one] using pow_le_pow_right₀ hb1 (by decide : 1≤1+1)
    exact ⟨hv.trans hp,hv.trans hp,by positivity⟩

end ScalarProgram
end AFT.RationalNumerics

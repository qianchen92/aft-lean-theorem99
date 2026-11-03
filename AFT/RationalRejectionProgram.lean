import AFT.FiniteConditionProgram
import AFT.FiniteConditionalSampling
import AFT.RationalAcceptanceCoin

/-! # A finite fair-bit implementation of rational-coin rejection

The program draws a fresh proposal and a fresh rational acceptance coin
at each attempt, then returns the first accepted proposal or its fallback.
-/
namespace AFT.RationalRejectionProgram
open FiniteDist FiniteConditionProgram
open scoped BigOperators
variable {State Tape : Type*}

 def run (fallback : State) : (attempts : ℕ) → (Fin attempts → State×Fin 2) → State
  | 0,_ => fallback
  | attempts+1,proposals => if (proposals 0).2=0 then (proposals 0).1
      else run fallback attempts (fun index => proposals index.succ)

 def proposal (decode : Tape → State) (coin : State → ℚ) (bits : ℕ)
    (tape : Tape×(Fin bits → Fin 2)) : State×Fin 2 :=
  let candidate := decode tape.1
  (candidate,RationalAcceptanceCoin.draw bits (coin candidate) tape.2)

 def draw (decode : Tape → State) (coin : State → ℚ) (bits attempts : ℕ) (fallback : State)
    (tape : Fin attempts → Tape×(Fin bits → Fin 2)) : State :=
  run fallback attempts (fun index => proposal decode coin bits (tape index))

 theorem run_property (property : State → Prop) (fallback : State) (hfallback : property fallback)
    (attempts : ℕ) (proposals : Fin attempts → State×Fin 2)
    (hproposal : ∀ index,property (proposals index).1) : property (run fallback attempts proposals) := by
  induction attempts with
  | zero => exact hfallback
  | succ attempts ih =>
    simp only [run]
    split_ifs
    · exact hproposal 0
    · exact ih (fun index => proposals index.succ) (fun index => hproposal index.succ)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State] [Fintype Tape] [Nonempty Tape]

 theorem select_coin_law {Random : Type*} [Fintype Random]
    (law : FiniteDist State) (coins : State → FiniteDist (Fin 2))
    (remaining : FiniteDist Random) (output : Random → State) :
    ((joint law coins).prod remaining).map
      (fun pair => if pair.1.2=0 then pair.1.1 else output pair.2)=
      rejectionStep law (fun point => (coins point).weight 0)
        (fun point => ⟨(coins point).nonneg 0,by
          have hh := Finset.single_le_sum (fun index (_ : index∈Finset.univ) => (coins point).nonneg index) (Finset.mem_univ 0)
          simpa only [(coins point).sum_one] using hh⟩) (remaining.map output) := by
  ext target
  have hc (point : State) : (coins point).weight 1=1-(coins point).weight 0 := by
    have hh := (coins point).sum_one
    rw [Fin.sum_univ_two] at hh
    linarith
  simp only [map_weight,prod_weight,joint,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [if_true,show ¬(1 : Fin 2)=0 by decide,if_false]
  have hfirst (point : State) :
      (∑ random,if point=target then law.weight point*(coins point).weight 0*remaining.weight random else 0)=
      if point=target then law.weight point*(coins point).weight 0 else 0 := by
    split_ifs with hp
    · rw [←Finset.mul_sum,remaining.sum_one,mul_one]
    · simp
  simp_rw [hfirst]
  have hsecond (point : State) :
      (∑ random,if output random=target then law.weight point*(coins point).weight 1*remaining.weight random else 0)=
      law.weight point*(coins point).weight 1*(remaining.map output).weight target := by
    simp only [map_weight,Finset.mul_sum,mul_ite,mul_zero]
  simp_rw [hsecond]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,←Finset.sum_mul]
  change law.weight target*(coins target).weight 0+_=
    law.weight target*(coins target).weight 0+(1-acceptance law (fun point => (coins point).weight 0))*_
  congr 1
  rw [show (∑point,law.weight point*(coins point).weight 1)=
    1-acceptance law (fun point => (coins point).weight 0) by
      simp only [hc,mul_sub,mul_one,Finset.sum_sub_distrib,law.sum_one,acceptance]]

 theorem run_law (law : FiniteDist State) (coins : State → FiniteDist (Fin 2))
    (fallback : State) (attempts : ℕ) :
    (independent (fun _ : Fin attempts => joint law coins)).map (run fallback attempts)=
      cappedRejection law (fun point => (coins point).weight 0)
        (fun point => ⟨(coins point).nonneg 0,by
          have hh := Finset.single_le_sum (fun index (_ : index∈Finset.univ) => (coins point).nonneg index) (Finset.mem_univ 0)
          simpa only [(coins point).sum_one] using hh⟩) (CanonicalMoments.pointLaw fallback) attempts := by
  induction attempts with
  | zero =>
    ext target
    change ((independent (fun _ : Fin 0 => joint law coins)).map (fun _ => fallback)).weight target=_
    rw [map_const_weight]
    rfl
  | succ attempts ih =>
    rw [independent_cons,FiniteDist.map_map]
    have he : (fun pair => run fallback (attempts+1)
      ((Fin.consEquiv (fun _ : Fin (attempts+1) => State×Fin 2)) pair))=
      (fun pair => if pair.1.2=0 then pair.1.1 else run fallback attempts pair.2) := by
        funext pair;simp only [run,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
    rw [he,select_coin_law,ih]
    rfl

 theorem proposal_law (decode : Tape → State) (coin : State → ℚ) (bits : ℕ) :
    (uniform (Tape×(Fin bits → Fin 2))).map (proposal decode coin bits)=
      joint ((uniform Tape).map decode) (fun point => (uniform (Fin bits → Fin 2)).map
        (RationalAcceptanceCoin.draw bits (coin point))) := by
  rw [uniform_product]
  exact map_joint_program (uniform Tape) (uniform (Fin bits → Fin 2)) decode
    (fun point => RationalAcceptanceCoin.draw bits (coin point))

 theorem draw_law (decode : Tape → State) (coin : State → ℚ) (bits attempts : ℕ) (fallback : State) :
    (uniform (Fin attempts → Tape×(Fin bits → Fin 2))).map (draw decode coin bits attempts fallback)=
      cappedRejection ((uniform Tape).map decode) (fun point => RationalAcceptanceCoin.probability bits (coin point))
        (fun point => RationalAcceptanceCoin.probability_bounds bits (coin point)) (CanonicalMoments.pointLaw fallback) attempts := by
  have hi := independent_decode (fun _ : Fin attempts => uniform (Tape×(Fin bits → Fin 2)))
    (fun _ => proposal decode coin bits)
  rw [independent_uniform] at hi
  simp only [proposal_law] at hi
  have hh := congrArg (fun law : FiniteDist (Fin attempts → State×Fin 2) => law.map (run fallback attempts)) hi
  dsimp only at hh
  rw [FiniteDist.map_map,run_law] at hh
  have hc (point : State) : ((uniform (Fin bits → Fin 2)).map
      (RationalAcceptanceCoin.draw bits (coin point))).weight 0=RationalAcceptanceCoin.probability bits (coin point) := by
    rw [←independent_uniform]
    exact RationalAcceptanceCoin.draw_acceptance bits (coin point)
  simpa only [hc,draw] using hh

end
end AFT.RationalRejectionProgram

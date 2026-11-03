import AFT.FiniteProductVariation
import AFT.PublicRecordExtension

/-! # Exact finite conditional sampling and additive law-error propagation -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

 theorem l1_dependentJoint_le {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (first second : FiniteDist Index)
    (conditional conditional' : ∀ index,FiniteDist (Fiber index)) :
    (∑ point,|(dependentJoint first conditional).weight point-(dependentJoint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+
        ∑ index,second.weight index*(∑ point,|(conditional index).weight point-(conditional' index).weight point|) := by
  simp only [dependentJoint,Fintype.sum_sigma]
  calc
    _ ≤ ∑ index,∑ point,(|first.weight index-second.weight index| *(conditional index).weight point+
        second.weight index*|(conditional index).weight point-(conditional' index).weight point|) := by
      apply Finset.sum_le_sum
      intro index _
      apply Finset.sum_le_sum
      intro point _
      have he : first.weight index*(conditional index).weight point-second.weight index*(conditional' index).weight point=
        (first.weight index-second.weight index)*(conditional index).weight point+
          second.weight index*((conditional index).weight point-(conditional' index).weight point) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg ((conditional index).nonneg point),abs_of_nonneg (second.nonneg index)] using
        abs_add_le ((first.weight index-second.weight index)*(conditional index).weight point)
          (second.weight index*((conditional index).weight point-(conditional' index).weight point))
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
      simp_rw [(conditional _).sum_one,mul_one]

 theorem l1_dependentJoint_uniform {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (first second : FiniteDist Index)
    (conditional conditional' : ∀ index,FiniteDist (Fiber index)) (error : ℝ)
    (h : ∀ index,(∑ point,|(conditional index).weight point-(conditional' index).weight point|)≤error) :
    (∑ point,|(dependentJoint first conditional).weight point-(dependentJoint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+error := by
  apply (l1_dependentJoint_le first second conditional conditional').trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ index,second.weight index*error := Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left (h index) (second.nonneg index))
    _ = error := by rw [←Finset.sum_mul,second.sum_one,one_mul]

 theorem map_conditional_program {Input Bits Index : Type*} [Fintype Input] [Fintype Bits] [Fintype Index]
    {Fiber : Index → Type*} [∀ index,Fintype (Fiber index)]
    (input : FiniteDist Input) (bits : FiniteDist Bits) (first : Input → Index)
    (second : ∀ index,Bits → Fiber index) :
    (input.prod bits).map (fun pair => (⟨first pair.1,second (first pair.1) pair.2⟩ : Sigma Fiber))=
      dependentJoint (input.map first) (fun index => bits.map (second index)) := by
  ext output
  rcases output with ⟨index,value⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,dependentJoint,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  apply Finset.sum_congr rfl
  intro tape _
  by_cases hi : first point=index
  · subst index
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,if_true]
    split_ifs <;> simp
  · have hne : (⟨first point,second (first point) tape⟩ : Sigma Fiber)≠⟨index,value⟩ :=
      fun hh => hi (congrArg Sigma.fst hh)
    simp only [if_neg hi,if_neg hne,zero_mul]

 theorem map_prod_functions {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1,g pair.2))=(first.map f).prod (second.map g) := by
  ext point
  rcases point with ⟨left,right⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,Prod.mk.injEq,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : f a=left <;> by_cases hb : g b=right <;> simp [ha,hb]

 theorem uniform_product {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    uniform (A×B)=(uniform A).prod (uniform B) := by
  ext point
  simp only [uniform_weight,prod_weight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,mul_comm]

 theorem map_joint_program {Input Bits Index Fiber : Type*} [Fintype Input] [Fintype Bits] [Fintype Index] [Fintype Fiber]
    (input : FiniteDist Input) (bits : FiniteDist Bits) (first : Input → Index)
    (second : Index → Bits → Fiber) :
    (input.prod bits).map (fun pair => (first pair.1,second (first pair.1) pair.2))=
      joint (input.map first) (fun index => bits.map (second index)) := by
  have hh := congrArg (fun law : FiniteDist (Sigma (fun _ : Index => Fiber)) => law.map (Equiv.sigmaEquivProd Index Fiber))
    (map_conditional_program input bits first second)
  dsimp only at hh
  rw [map_map] at hh
  apply hh.trans
  ext point
  rw [map_equiv_weight]
  rfl

 theorem l1_joint_uniform {Index Fiber : Type*} [Fintype Index] [Fintype Fiber]
    (first second : FiniteDist Index) (conditional conditional' : Index → FiniteDist Fiber) (error : ℝ)
    (h : ∀ index,(∑ point,|(conditional index).weight point-(conditional' index).weight point|)≤error) :
    (∑ point,|(joint first conditional).weight point-(joint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+error := by
  have hh := l1_dependentJoint_uniform first second (Fiber:=fun _ => Fiber) conditional conditional' error h
  simpa only [Fintype.sum_sigma,Fintype.sum_prod_type,dependentJoint,joint] using hh

end
end AFT.FiniteDist

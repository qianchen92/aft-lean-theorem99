import AFT.FiniteDisintegration

/-! # Exact public extensions and coarse-record conditional marginals -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Sample the mark first and then all dependent public randomness.
The dependent pair retains the sampled data for the later charge choice. -/
def dependentJoint {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (law : FiniteDist Index)
    (conditional : ∀ index,FiniteDist (Fiber index)) : FiniteDist (Sigma Fiber) where
  weight point := law.weight point.1*(conditional point.1).weight point.2
  nonneg point := mul_nonneg (law.nonneg point.1) ((conditional point.1).nonneg point.2)
  sum_one := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum]
    simp_rw [(conditional _).sum_one,mul_one]
    exact law.sum_one

theorem dependentJoint_map_fst {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (law : FiniteDist Index)
    (conditional : ∀ index,FiniteDist (Fiber index)) :
    (dependentJoint law conditional).map Sigma.fst=law := by
  ext point
  simp only [map_weight,dependentJoint,Fintype.sum_sigma]
  trans ∑ index,if index=point then law.weight index else 0
  · apply Finset.sum_congr rfl
    intro index _
    by_cases h : index=point
    · simp only [h,ite_true,← Finset.mul_sum]
      rw [(conditional index).sum_one,mul_one]
    · simp only [h,ite_false,Finset.sum_const_zero]
  · simp

theorem dependentJoint_expectation {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (law : FiniteDist Index)
    (conditional : ∀ index,FiniteDist (Fiber index)) (value : Sigma Fiber → ℝ) :
    (dependentJoint law conditional).expectation value=
      law.expectation (fun index => (conditional index).expectation (fun point => value ⟨index,point⟩)) := by
  simp only [expectation,dependentJoint,Fintype.sum_sigma,Finset.mul_sum,mul_assoc]

variable {State Mark Record : Type*} [Fintype State] [Fintype Mark] [Fintype Record]

theorem condition_expectation (law : FiniteDist State) (event : State → Prop)
    (hpos : 0<law.eventMass event) (value : State → ℝ) :
    (law.condition event hpos).expectation value=
      law.expectation (fun state => if event state then value state else 0)/law.eventMass event := by
  simp only [expectation,condition,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  split_ifs <;> ring

/-- Conditional means are unchanged by extra public randomness when the
coarse record and the score use only the indicated projection. -/
theorem recordConditional_projection_expectation (law : FiniteDist State)
    (projection : State → Mark) (record : Mark → Record)
    (cell : {value // 0<(law.map (record ∘ projection)).weight value})
    (value : Mark → ℝ) :
    (recordConditional law (record ∘ projection) cell).expectation (value ∘ projection)=
      (recordConditional (law.map projection) record
        ⟨cell.val,by simpa only [map_map] using cell.property⟩).expectation value := by
  unfold recordConditional
  rw [condition_expectation,condition_expectation]
  have hden : law.eventMass (fun state => (record ∘ projection) state=cell.val)=
      (law.map projection).eventMass (fun mark => record mark=cell.val) := by
    change (law.map (record ∘ projection)).weight cell.val=((law.map projection).map record).weight cell.val
    rw [map_map]
    rfl
  rw [hden,expectation_map]
  rfl

/-- The same identity applies when the body word is drawn afterwards and
only the projected public marks occur in the score. -/
theorem recordConditional_projection_joint_expectation {Body : Type*} [Fintype Body]
    (law : FiniteDist State) (projection : State → Mark) (record : Mark → Record)
    (cell : {value // 0<(law.map (record ∘ projection)).weight value})
    (body : FiniteDist Body) (value : Mark × Body → ℝ) :
    (joint (recordConditional law (record ∘ projection) cell) (fun _ => body)).expectation
      (fun point => value (projection point.1,point.2))=
    (joint (recordConditional (law.map projection) record
      ⟨cell.val,by simpa only [map_map] using cell.property⟩) (fun _ => body)).expectation value := by
  rw [expectation_joint,expectation_joint]
  exact recordConditional_projection_expectation law projection record cell
    (fun mark => body.expectation (fun point => value (mark,point)))

/-- A projected zero conditional mean remains exactly zero after adding
arbitrary dependent public data. -/
theorem recordConditional_projection_joint_zero {Body : Type*} [Fintype Body]
    (law : FiniteDist State) (projection : State → Mark) (markLaw : FiniteDist Mark)
    (hmark : law.map projection=markLaw) (record : Mark → Record)
    (body : FiniteDist Body) (value : Mark × Body → ℝ)
    (hzero : ∀ cell : {value // 0<(markLaw.map record).weight value},
      (joint (recordConditional markLaw record cell) (fun _ => body)).expectation value=0)
    (cell : {value // 0<(law.map (record ∘ projection)).weight value}) :
    (joint (recordConditional law (record ∘ projection) cell) (fun _ => body)).expectation
      (fun point => value (projection point.1,point.2))=0 := by
  subst markLaw
  exact (recordConditional_projection_joint_expectation law projection record cell body value).trans (hzero _)

end
end AFT.FiniteDist

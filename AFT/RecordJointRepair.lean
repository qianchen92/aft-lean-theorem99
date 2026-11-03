import AFT.FiniteDisintegration
import AFT.ChargedPairedSupport

/-! # Forgetting the repair cell preserves its real public record and support -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Public Record Center Output : Type*} [Fintype Public] [Fintype Record]
  [Fintype Center] [Fintype Output]

omit [Fintype Record] [Fintype Center] in
theorem map_nonzero_witness (law : FiniteDist Public) (function : Public → Output)
    (output : Output) (hn : (law.map function).weight output≠0) :
    ∃ input,function input=output ∧ law.weight input≠0 := by
  by_contra hh
  push_neg at hh
  apply hn
  rw [map_weight]
  apply Finset.sum_eq_zero
  intro input _
  split_ifs with he
  · exact hh input he
  · rfl

omit [Fintype Record] [Fintype Center] in
theorem map_eq_of_support (law : FiniteDist Public) (first second : Public → Output)
    (he : ∀ input,law.weight input≠0 →first input=second input) : law.map first=law.map second := by
  ext output
  simp only [map_weight]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hz : law.weight input=0
  · simp only [hz,ite_self]
  · rw [he input hz]

omit [Fintype Output] in
def recordJointRepair (law : FiniteDist Public) (record : Public → Record)
    (conditional : Public → FiniteDist Center) (score : Public × Center → ℝ)
    (hmean : ∀ cell,0<signedMass (weightedMass
      (joint (recordConditional law record cell) conditional) score)) : FiniteDist (Public × Center) :=
  (conditionalRepair (recordSkeleton law record)
    (fun cell => joint (recordConditional law record cell) conditional) (fun _ => score) hmean).map Prod.snd

omit [Fintype Output] in
theorem recordJointRepair_tagged_support (law : FiniteDist Public) (record : Public → Record)
    (conditional : Public → FiniteDist Center) (score : Public × Center → ℝ)
    (hmean : ∀ cell,0<signedMass (weightedMass
      (joint (recordConditional law record cell) conditional) score))
    (pair : {value //0<(law.map record).weight value} × (Public × Center))
    (hn : (conditionalRepair (recordSkeleton law record)
      (fun cell => joint (recordConditional law record cell) conditional) (fun _ => score) hmean).weight pair≠0) :
    record pair.2.1=pair.1.val ∧ law.weight pair.2.1≠0 ∧ (conditional pair.2.1).weight pair.2.2≠0 := by
  have hs := conditionalRepair_nonzero_support _ _ _ hmean pair hn
  have hj : (recordConditional law record pair.1).weight pair.2.1≠0 ∧
      (conditional pair.2.1).weight pair.2.2≠0 := mul_ne_zero_iff.mp hs.2
  have hp := condition_nonzero_support law (fun point => record point=pair.1.val) pair.1.property pair.2.1 hj.1
  exact ⟨hp.1,hp.2,hj.2⟩

omit [Fintype Output] in
theorem recordJointRepair_support (law : FiniteDist Public) (record : Public → Record)
    (conditional : Public → FiniteDist Center) (score : Public × Center → ℝ)
    (hmean : ∀ cell,0<signedMass (weightedMass
      (joint (recordConditional law record cell) conditional) score)) (point : Public × Center)
    (hn : (recordJointRepair law record conditional score hmean).weight point≠0) :
    law.weight point.1≠0 ∧ (conditional point.1).weight point.2≠0 := by
  obtain ⟨pair,he,hs⟩ := map_nonzero_witness _ Prod.snd point hn
  have hh := recordJointRepair_tagged_support law record conditional score hmean pair hs
  simpa only [show pair.2=point from he] using hh.2

omit [Fintype Output] in
theorem recordJointRepair_record (law : FiniteDist Public) (record : Public → Record)
    (conditional : Public → FiniteDist Center) (score : Public × Center → ℝ)
    (hmean : ∀ cell,0<signedMass (weightedMass
      (joint (recordConditional law record cell) conditional) score)) :
    (recordJointRepair law record conditional score hmean).map (fun point => record point.1)=law.map record := by
  let repaired := conditionalRepair (recordSkeleton law record)
    (fun cell => joint (recordConditional law record cell) conditional) (fun _ => score) hmean
  have he : repaired.map (fun pair => record pair.2.1)=repaired.map (fun pair => pair.1.val) :=
    map_eq_of_support repaired _ _ (fun pair hn => (recordJointRepair_tagged_support law record conditional score hmean pair hn).1)
  change (repaired.map Prod.snd).map (fun point => record point.1)=_
  rw [FiniteDist.map_map]
  change repaired.map (fun pair => record pair.2.1)=_
  rw [he,← FiniteDist.map_map]
  change ((conditionalRepair _ _ _ hmean).map Prod.fst).map Subtype.val=_
  rw [conditionalRepair_skeleton]
  exact positiveSupportLaw_map (law.map record)

end
end AFT.FiniteDist

import AFT.MixedFiniteSeed

/-! # A literal seed for newly created primaries and unchanged two-pool coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {New Primary Body Color : Type*} [Fintype New] [Fintype Primary] [Fintype Body] [Fintype Color]
  [DecidableEq New] [DecidableEq Primary] [DecidableEq Body]

def groupedFiniteSeed (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ) : InputSeed Color :=
  mixedFiniteSeed (fun word => kernel (word ∘ (Equiv.sumAssoc New Primary Body).symm))

omit [Fintype New] [Fintype Primary] [Fintype Body] [DecidableEq New] [DecidableEq Primary] [DecidableEq Body] in
theorem groupedFiniteSeed_reference_assoc (primary body : FiniteDist Color) :
    (fun slot => Sum.elim (fun _ : New => primary)
      (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) (Equiv.sumAssoc New Primary Body slot)) =
      Sum.elim (fun _ : New ⊕ Primary => primary) (fun _ : Body => body) := by
  funext slot
  rcases slot with (slot|slot)|slot <;> rfl

omit [Fintype New] [Fintype Primary] [Fintype Body] [Fintype Color] [DecidableEq New] [DecidableEq Primary] [DecidableEq Body] in
theorem groupedFiniteSeed_rate_assoc (primaryPool bodyPool : ℝ) :
    (fun slot => Sum.elim (fun _ : New => (Real.sqrt primaryPool)⁻¹)
      (Sum.elim (fun _ : Primary => (Real.sqrt primaryPool)⁻¹) (fun _ : Body => (Real.sqrt bodyPool)⁻¹))
        (Equiv.sumAssoc New Primary Body slot)) =
      Sum.elim (fun _ : New ⊕ Primary => (Real.sqrt primaryPool)⁻¹) (fun _ : Body => (Real.sqrt bodyPool)⁻¹) := by
  funext slot
  rcases slot with (slot|slot)|slot <;> rfl

theorem groupedFiniteSeed_weight (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ) :
    inputWeight primary body primaryPool bodyPool radius (groupedFiniteSeed kernel) =
      radius^Fintype.card Body*MixedKernel.activity
        (Sum.elim (fun _ : New => (Real.sqrt primaryPool)⁻¹)
          (Sum.elim (fun _ : Primary => (Real.sqrt primaryPool)⁻¹) (fun _ : Body => (Real.sqrt bodyPool)⁻¹)))
        (Sum.elim (fun _ : New => primary) (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))) kernel := by
  rw [groupedFiniteSeed,mixedFiniteSeed_weight]
  congr 1
  have he := MixedKernel.CoordinateTransport.activity_equiv (Equiv.sumAssoc New Primary Body).symm
    (Sum.elim (fun _ : New => (Real.sqrt primaryPool)⁻¹)
      (Sum.elim (fun _ : Primary => (Real.sqrt primaryPool)⁻¹) (fun _ : Body => (Real.sqrt bodyPool)⁻¹)))
    (Sum.elim (fun _ : New => primary) (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))) kernel
  simpa only [Equiv.symm_symm,groupedFiniteSeed_reference_assoc,groupedFiniteSeed_rate_assoc] using he

omit [DecidableEq New] [DecidableEq Primary] [DecidableEq Body] in
theorem groupedFiniteSeed_canonical (primary body : FiniteDist Color)
    (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ)
    (hc : Hoeffding.Canonical
      (Sum.elim (fun _ : New => primary) (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))) Finset.univ kernel) :
    Hoeffding.Canonical (inputReference primary body (groupedFiniteSeed kernel)) Finset.univ
      (groupedFiniteSeed kernel).kernel := by
  apply mixedFiniteSeed_canonical
  have he := MixedKernel.CoordinateTransport.canonical_equiv (Equiv.sumAssoc New Primary Body).symm
    (Sum.elim (fun _ : New => primary) (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))) kernel hc
  simpa only [Equiv.symm_symm,groupedFiniteSeed_reference_assoc] using he

end
end AFT.RepresentedPolynomial

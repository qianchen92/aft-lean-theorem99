import AFT.PrimaryFiniteSeed

/-! # Literal two-pool input seeds indexed by arbitrary finite coordinate sets -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body Color : Type*} [Fintype Primary] [Fintype Body] [Fintype Color]
  [DecidableEq Primary] [DecidableEq Body]

def mixedFiniteEquiv : Primary ⊕ Body ≃ Fin (Fintype.card Primary+Fintype.card Body) :=
  (Equiv.sumCongr (Fintype.equivFin Primary) (Fintype.equivFin Body)).trans finSumFinEquiv

def mixedFiniteSeed (kernel : (Primary ⊕ Body → Color) → ℝ) : InputSeed Color where
  primaryOrder := Fintype.card Primary
  bodyOrder := Fintype.card Body
  kernel := fun word => kernel (word ∘ mixedFiniteEquiv)

omit [DecidableEq Primary] [DecidableEq Body] in
theorem mixedFiniteSeed_reference (primary body : FiniteDist Color)
    (kernel : (Primary ⊕ Body → Color) → ℝ) :
    inputReference primary body (mixedFiniteSeed kernel) =
      fun slot => Sum.elim (fun _ : Primary => primary) (fun _ : Body => body) (mixedFiniteEquiv.symm slot) := by
  funext slot
  obtain ⟨slot,rfl⟩ := mixedFiniteEquiv.surjective slot
  cases slot with
  | inl slot => simp [mixedFiniteSeed,mixedFiniteEquiv,inputReference]
  | inr slot => simp [mixedFiniteSeed,mixedFiniteEquiv,inputReference]

omit [Fintype Color] [DecidableEq Primary] [DecidableEq Body] in
theorem mixedFiniteSeed_rate (primaryPool bodyPool : ℝ)
    (kernel : (Primary ⊕ Body → Color) → ℝ) :
    inputRate primaryPool bodyPool (mixedFiniteSeed kernel) =
      fun slot => Sum.elim (fun _ : Primary => (Real.sqrt primaryPool)⁻¹)
        (fun _ : Body => (Real.sqrt bodyPool)⁻¹) (mixedFiniteEquiv.symm slot) := by
  funext slot
  obtain ⟨slot,rfl⟩ := mixedFiniteEquiv.surjective slot
  cases slot with
  | inl slot => simp [mixedFiniteSeed,mixedFiniteEquiv,inputRate]
  | inr slot => simp [mixedFiniteSeed,mixedFiniteEquiv,inputRate]

/-- The entire joint seed is renamed once; its body radius and both pool
rates are retained exactly, including every fixed-coordinate fiber. -/
theorem mixedFiniteSeed_weight (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) (kernel : (Primary ⊕ Body → Color) → ℝ) :
    inputWeight primary body primaryPool bodyPool radius (mixedFiniteSeed kernel) =
      radius^Fintype.card Body*MixedKernel.activity
        (Sum.elim (fun _ : Primary => (Real.sqrt primaryPool)⁻¹) (fun _ : Body => (Real.sqrt bodyPool)⁻¹))
        (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) kernel := by
  change radius^Fintype.card Body*MixedKernel.activity
    (inputRate primaryPool bodyPool (mixedFiniteSeed kernel))
    (inputReference primary body (mixedFiniteSeed kernel)) (mixedFiniteSeed kernel).kernel = _
  rw [mixedFiniteSeed_rate,mixedFiniteSeed_reference]
  congr 1
  exact MixedKernel.CoordinateTransport.activity_equiv mixedFiniteEquiv _ _ kernel

omit [DecidableEq Primary] [DecidableEq Body] in
theorem mixedFiniteSeed_canonical (primary body : FiniteDist Color)
    (kernel : (Primary ⊕ Body → Color) → ℝ)
    (hc : Hoeffding.Canonical (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) Finset.univ kernel) :
    Hoeffding.Canonical (inputReference primary body (mixedFiniteSeed kernel)) Finset.univ
      (mixedFiniteSeed kernel).kernel := by
  have hh := MixedKernel.CoordinateTransport.canonical_equiv mixedFiniteEquiv
    (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) kernel hc
  convert hh using 1
  exact mixedFiniteSeed_reference primary body kernel

end
end AFT.RepresentedPolynomial

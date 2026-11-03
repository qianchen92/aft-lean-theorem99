import AFT.MixedProducts

/-! # Literal numbered three-coordinate products and finite source averages -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color] [Nonempty Color]

def tripleProductKernel (pair : Color → Color → ℝ) (single : Color → ℝ) (word : Fin 3 → Color) : ℝ :=
  pair (word 0) (word 1) * single (word 2)

set_option backward.isDefEq.respectTransparency false in
theorem tripleProduct_activity_le (primary : FiniteDist Color) (pair : Color → Color → ℝ)
    (single : Color → ℝ) (rate : ℝ) (hrate : 0 ≤ rate) :
    activity (fun _ : Fin 3 => rate) (fun _ => primary) (tripleProductKernel pair single) ≤
      activity ![rate,rate] (pairReference primary primary) (pairKernel pair) *
        activity (fun _ : Fin 1 => rate) (fun _ => primary) (singletonKernel single) := by
  have hk : tripleProductKernel pair single =
      fun word => tensor (pairKernel pair) (singletonKernel single) (word ∘ finSumFinEquiv) := by
    funext word
    rfl
  rw [hk]
  have heq := activity_equiv (fun _ : Fin 3 => rate) (fun _ => primary)
    (tensor (pairKernel pair) (singletonKernel single)) (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)
  apply heq.le.trans
  have hr : (fun _ : Fin 2 ⊕ Fin 1 => rate) = Sum.elim ![rate,rate] (fun _ : Fin 1 => rate) := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rfl
  have hp : (fun _ : Fin 2 ⊕ Fin 1 => primary) =
      Sum.elim (pairReference primary primary) (fun _ : Fin 1 => primary) := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rfl
  rw [hr, hp]
  exact activity_tensor_le ![rate,rate] (fun _ : Fin 1 => rate)
    (pairReference primary primary) (fun _ : Fin 1 => primary) (pairKernel pair) (singletonKernel single)
    (fun i => by fin_cases i <;> exact hrate) (fun _ => hrate)

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical
noncomputable section

variable {Color : Type*} [Fintype Color]

def primaryPairInput (kernel : Color → Color → ℝ) : InputSeed Color where
  primaryOrder := 2
  bodyOrder := 0
  kernel := MixedKernel.pairKernel kernel

theorem primaryPairInput_weight (kernel : Color → Color → ℝ) (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) :
    inputWeight primary body primaryPool bodyPool radius (primaryPairInput kernel) =
      MixedKernel.activity ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt primaryPool)⁻¹]
        (MixedKernel.pairReference primary primary) (MixedKernel.pairKernel kernel) := by
  have hrate : inputRate primaryPool bodyPool (primaryPairInput kernel) = ![(Real.sqrt primaryPool)⁻¹, (Real.sqrt primaryPool)⁻¹] := by
    funext i
    fin_cases i <;> rfl
  have href : inputReference primary body (primaryPairInput kernel) = MixedKernel.pairReference primary primary := by
    funext i
    fin_cases i <;> rfl
  unfold inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [primaryPairInput, pow_zero, one_mul]
  rfl

def primaryTripleInput (kernel : (Fin 3 → Color) → ℝ) : InputSeed Color where
  primaryOrder := 3
  bodyOrder := 0
  kernel := kernel

theorem primaryTripleInput_weight (kernel : (Fin 3 → Color) → ℝ) (primary body : FiniteDist Color)
    (primaryPool bodyPool radius : ℝ) :
    inputWeight primary body primaryPool bodyPool radius (primaryTripleInput kernel) =
      MixedKernel.activity (fun _ : Fin 3 => (Real.sqrt primaryPool)⁻¹) (fun _ => primary) kernel := by
  have hrate : inputRate primaryPool bodyPool (primaryTripleInput kernel) = fun _ : Fin 3 => (Real.sqrt primaryPool)⁻¹ := by
    funext i
    fin_cases i <;> rfl
  have href : inputReference primary body (primaryTripleInput kernel) = fun _ : Fin 3 => primary := by
    funext i
    fin_cases i <;> rfl
  unfold inputWeight MixedKernel.analyticActivity
  rw [hrate, href]
  simp only [primaryTripleInput, pow_zero, one_mul]
  rfl

end
end AFT.RepresentedPolynomial

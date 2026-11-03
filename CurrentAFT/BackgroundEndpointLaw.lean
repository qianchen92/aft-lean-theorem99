import CurrentAFT.BackgroundPolynomialEvaluation

/-! Fixed endpoint numbering for the actual complete background experiment.
This numbering is a deterministic equivalence, not the final random endpoint
permutation used by the transport construction. -/

namespace CurrentAFT.BackgroundEndpointLaw

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  BackgroundPopulationBounds BackgroundPolynomialEvaluation BackgroundEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

abbrev Endpoint (security : ℕ) :=
  Fin (freeCount security) ⊕ (Fin (Parameters.modulus security) ⊕ (Fin (Parameters.legCount security) × Fin 3))

theorem endpoint_card (security : ℕ) : Fintype.card (Endpoint security) = Parameters.dimension security := by
  have hroom := population_room security
  simp only [Endpoint, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  unfold freeCount Parameters.dimension
  omega

/-- A fixed mathematical numbering of exactly all output endpoints. -/
noncomputable def endpointEquiv (security : ℕ) : Endpoint security ≃ Fin (Parameters.dimension security) :=
  Fintype.equivFinOfCardEq (endpoint_card security)

def endpointColor (security : ℕ) (output : BackgroundColors security) : Endpoint security → ActualControls.Palette security
  | .inl free => output.1 free
  | .inr (.inl queue) => output.2.1 queue
  | .inr (.inr (leg, coordinate)) =>
      if coordinate.val = 0 then (output.2.2 leg).1.1 else
        if coordinate.val = 1 then (output.2.2 leg).1.2 else (output.2.2 leg).2

theorem endpointFactor_product (security : ℕ) (output : BackgroundColors security) :
    endpointFactor security output =
      ∏ index : Endpoint security, centeredFactor (FringeCertificate.uniformProfile security) (endpointColor security output index) := by
  simp [endpointFactor, legFactor, Endpoint, Fintype.prod_sum_type,
    Fintype.prod_prod_type, endpointColor, Fin.prod_univ_three]

def flatten (security : ℕ) (output : BackgroundColors security) : Fin (Parameters.dimension security) → ActualControls.Palette security :=
  endpointColor security output ∘ (endpointEquiv security).symm

theorem flatten_product (security : ℕ) (output : BackgroundColors security) :
    (∏ index : Fin (Parameters.dimension security), centeredFactor (FringeCertificate.uniformProfile security) (flatten security output index)) =
      endpointFactor security output := by
  rw [endpointFactor_product]
  exact Equiv.prod_comp (endpointEquiv security).symm
    (fun index => centeredFactor (FringeCertificate.uniformProfile security) (endpointColor security output index))

theorem finiteGenerating_map {Input Output Variable : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (map : Input → Output) (factor : Output → MvPolynomial Variable ℝ) :
    finiteGenerating (law.map map) factor = finiteGenerating law (factor ∘ map) := by
  unfold finiteGenerating
  simp only [FiniteDist.map_weight, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [apply_ite, map_zero, ite_mul, zero_mul, eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply]

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def flatLaw (security : ℕ) : FiniteDist (Fin (Parameters.dimension security) → ActualControls.Palette security) :=
  (backgroundLaw security).map (flatten security)

theorem flatLaw_generating (security : ℕ) :
    finiteGenerating (flatLaw security) (fun output => ∏ index,
      centeredFactor (FringeCertificate.uniformProfile security) (output index)) = backgroundGenerating security := by
  rw [flatLaw, finiteGenerating_map]
  have hfactor : (fun output : BackgroundColors security =>
      ∏ index : Fin (Parameters.dimension security),
        centeredFactor (FringeCertificate.uniformProfile security) (flatten security output index)) = endpointFactor security :=
    funext (flatten_product security)
  change finiteGenerating (backgroundLaw security) (fun output : BackgroundColors security =>
    ∏ index : Fin (Parameters.dimension security),
      centeredFactor (FringeCertificate.uniformProfile security) (flatten security output index)) = _
  rw [hfactor, backgroundLaw_generating]

theorem background_image_flatLaw (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order (ActualBackground.background security order horder) =
      TruncatedOutput.quotientMap order (finiteGenerating (flatLaw security)
        (fun output => ∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output index))) := by
  rw [flatLaw_generating]
  exact background_image security order horder

end

end CurrentAFT.BackgroundEndpointLaw

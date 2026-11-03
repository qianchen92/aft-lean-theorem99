import CurrentAFT.CurrentAffineLoad
import CurrentAFT.FiniteZeroSum
import AFT.Construction

/-! # The actual fixed rounding label and its uniform zero fiber -/
namespace CurrentAFT.CurrentZeroFiber
open AFT CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance dimensionNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by rw [← LobsterCoordinates.current_vertex_count security]; omega⟩⟩

abbrev Word (security : ℕ) := Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)

def coordinates (security : ℕ) : Word security ≃
    (Fin (edgeCount security) → ZMod (Parameters.modulus security)) × ZMod (Parameters.modulus security) where
  toFun word := (fun edge => word (coordinateNumbering security (.inl edge)),
    word (coordinateNumbering security (.inr ())))
  invFun pair index := Sum.elim pair.1 (fun _ : Unit => pair.2) ((coordinateNumbering security).symm index)
  left_inv word := by
    funext index
    obtain ⟨edge | point, rfl⟩ := (coordinateNumbering security).surjective index
    · simp
    · cases point; simp
  right_inv pair := by simp

theorem column_charge (security : ℕ) :
    totalCharge (injectionColumn (edgeCount security) (Parameters.modulus security)) =
      (Parameters.modulus security : ℤ) := by
  apply totalCharge_injectionColumn
  have hb : Parameters.modulus security ≤ Parameters.bodySize security := by
    rw [Parameters.bodySize_eq]
    exact Nat.le_mul_of_pos_right _ (pow_pos (Parameters.base_pos security) _)
  have hp := LobsterCoordinates.current_body_positive security
  dsimp only [edgeCount, bodyEdges]
  omega

/-- This is the carry label of the manuscript's fixed matrix with the
path columns first and the injection column last. -/
def label (security : ℕ) (word : Word security) : ZMod (Parameters.modulus security) :=
  fiberLabel (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (coordinates security word)

def ZeroFiber (security : ℕ) := {word : Word security // label security word = 0}

instance fiberFintype (security : ℕ) : Fintype (ZeroFiber security) := by
  unfold ZeroFiber
  infer_instance

def fiberEquiv (security : ℕ) : ZeroFiber security ≃
    AFT.ZeroFiber (edgeCount security) (Parameters.modulus security)
      (injectionColumn _ (Parameters.modulus security)) where
  toFun word := ⟨coordinates security word.val, word.property⟩
  invFun word := ⟨(coordinates security).symm word.val, by simpa [label] using word.property⟩
  left_inv word := by apply Subtype.ext; exact (coordinates security).symm_apply_apply word.val
  right_inv word := by apply Subtype.ext; exact (coordinates security).apply_symm_apply word.val

instance fiberNonempty (security : ℕ) : Nonempty (ZeroFiber security) := by
  obtain ⟨word⟩ : Nonempty (AFT.ZeroFiber (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security))) := inferInstance
  exact ⟨(fiberEquiv security).symm word⟩

def uniformFiber (security : ℕ) : FiniteDist (Word security) :=
  (FiniteDist.uniform (ZeroFiber security)).map Subtype.val

theorem uniformFiber_reindex (security : ℕ) :
    (uniformZeroFiber (edgeCount security) (Parameters.modulus security)
      (injectionColumn _ (Parameters.modulus security))).map (coordinates security).symm =
        uniformFiber security := by
  rw [uniformZeroFiber, uniformFiber, FiniteDist.map_map]
  rw [← FiniteDist.uniform_map_equiv (fiberEquiv security).symm, FiniteDist.map_map]
  rfl

def endpointCoordinates (security : ℕ) : Word security ≃
    (Fin (edgeCount security + 1) → ZMod (Parameters.modulus security)) :=
  Equiv.arrowCongr (dimensionEquiv security).symm (Equiv.refl _)

theorem endpointCoordinates_sum (security : ℕ) (word : Word security) :
    ∑ index, endpointCoordinates security word index = ∑ index, word index :=
  Equiv.sum_comp (dimensionEquiv security) word

theorem uniformEndpoint_reindex (security : ℕ) :
    (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)).map
      (endpointCoordinates security) = uniformZeroSum (edgeCount security) (Parameters.modulus security) := by
  ext word
  rw [FiniteDist.map_equiv_weight, FiniteZeroSum.uniformLaw_weight, uniformZeroSum_weight]
  have hsum : (∑ index, (endpointCoordinates security).symm word index) = ∑ index, word index :=
    Equiv.sum_comp (dimensionEquiv security).symm word
  rw [hsum]
  split_ifs
  · simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    rw [← LobsterCoordinates.current_vertex_count security]
    change (Parameters.modulus security : ℝ) / (Parameters.modulus security : ℝ) ^ (edgeCount security + 1) = _
    have hq : (Parameters.modulus security : ℝ) ≠ 0 := by exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
    rw [pow_succ]
    field_simp
  · rfl

def rawPullback (n q : ℕ) [NeZero q] (column : Fin (n + 1) → ℤ)
    (hcolumn : totalCharge column = (q : ℤ)) (endpoint : Fin (n + 1) → ZMod q) :
    (Fin n → ZMod q) × ZMod q :=
  if hzero : ∑ index, endpoint index = 0 then
    (canonicalEndpointEquiv n q column hcolumn ⟨endpoint, hzero⟩).val else 0

theorem rawPullback_uniform (n q : ℕ) [NeZero q] (column : Fin (n + 1) → ℤ)
    (hcolumn : totalCharge column = (q : ℤ)) :
    (uniformZeroSum n q).map (rawPullback n q column hcolumn) = uniformZeroFiber n q column := by
  rw [uniformZeroSum, FiniteDist.map_map]
  change (FiniteDist.uniform (EndpointHyperplane n q)).map _ = _
  calc
    _ = (FiniteDist.uniform (EndpointHyperplane n q)).map
        (fun endpoint => (canonicalEndpointEquiv n q column hcolumn endpoint).val) := by
      congr 1
      funext endpoint
      simp only [rawPullback, dif_pos endpoint.property]
    _ = _ := canonical_uniform_transport n q column hcolumn

def pullback (security : ℕ) (endpoint : Word security) : Word security :=
  (coordinates security).symm (rawPullback (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (column_charge security)
      (endpointCoordinates security endpoint))

/-- The target is uniform on the genuine fixed-label zero fiber, as proved
by the explicit endpoint equivalence. -/
theorem uniform_pullback (security : ℕ) :
    (FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security)) (Parameters.modulus security)).map
      (pullback security) = uniformFiber security := by
  unfold pullback
  calc
    _ = (((FiniteZeroSum.uniformLaw (Index := Fin (Parameters.dimension security))
        (Parameters.modulus security)).map (endpointCoordinates security)).map
          (rawPullback (edgeCount security) (Parameters.modulus security)
            (injectionColumn _ (Parameters.modulus security)) (column_charge security))).map
              (coordinates security).symm := by rw [FiniteDist.map_map, FiniteDist.map_map]
    _ = _ := by rw [uniformEndpoint_reindex, rawPullback_uniform, uniformFiber_reindex]

theorem coordinates_reduce (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    coordinates security (fun index => (input index : ZMod (Parameters.modulus security))) =
      reduceCoordinates (edgeCount security) (Parameters.modulus security) (CurrentAffineLoad.splitSource security input) := rfl

theorem label_reduce (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    label security (fun index => (input index : ZMod (Parameters.modulus security))) =
      ((∑ vertex, CurrentAffineLoad.rounding security input vertex / Parameters.modulus security : ℤ) :
        ZMod (Parameters.modulus security)) := by
  rw [label, coordinates_reduce, fiberLabel_reduceCoordinates _ _ _ (column_charge security)]
  unfold integerLabel totalCharge canonicalCarry CurrentAffineLoad.rounding
  exact congrArg (fun value : ℤ => (value : ZMod (Parameters.modulus security)))
    (Equiv.sum_comp (dimensionEquiv security).symm (fun vertex =>
      roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security))
        (CurrentAffineLoad.splitSource security input) vertex / Parameters.modulus security)).symm

theorem pullback_rounding (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ)
    (hcarry : (∑ vertex, CurrentAffineLoad.rounding security input vertex / Parameters.modulus security : ℤ) = 0) :
    pullback security (fun vertex => (CurrentAffineLoad.rounding security input vertex :
      ZMod (Parameters.modulus security))) =
        fun index => (input index : ZMod (Parameters.modulus security)) := by
  apply (coordinates security).injective
  rw [pullback, Equiv.apply_symm_apply, coordinates_reduce]
  let coordinateInput := CurrentAffineLoad.splitSource security input
  let endpoint := endpointProjection (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (column_charge security)
      (reduceCoordinates _ _ coordinateInput)
  have hep : endpointCoordinates security (fun vertex => (CurrentAffineLoad.rounding security input vertex :
      ZMod (Parameters.modulus security))) = endpoint.val := by
    funext vertex
    rw [endpointProjection_reduceCoordinates]
    change (roundingLoad _ _ _ ((dimensionEquiv security).symm (dimensionEquiv security vertex)) :
      ZMod (Parameters.modulus security)) = _
    rw [Equiv.symm_apply_apply]
  rw [hep, rawPullback, dif_pos endpoint.property]
  have hgeneric : totalCharge (canonicalCarry (edgeCount security) (Parameters.modulus security)
      (roundingLoad _ (injectionColumn _ (Parameters.modulus security)) coordinateInput)) = 0 := by
    have hs := Equiv.sum_comp (dimensionEquiv security).symm (fun vertex =>
      roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security))
        coordinateInput vertex / Parameters.modulus security)
    exact hs.symm.trans hcarry
  exact ((canonical_endpoint_agreement_iff_carry (edgeCount security) (Parameters.modulus security)
    (injectionColumn _ (Parameters.modulus security)) (column_charge security) coordinateInput).mpr
      (by rw [hgeneric]; exact dvd_zero _)).symm

end
end CurrentAFT.CurrentZeroFiber

import CurrentAFT.CurrentSourcePublicTransport
import CurrentAFT.CurrentAffineGeometry

/-! # Actual hidden-source coordinates and the independent public closure

The complete comparison source has `dimension + 1` entries. Exactly one
entry is the public closing edge. The other `dimension` entries follow
the fixed rounding-matrix order: body path, first leg inputs, second leg
inputs, and finally the unique queue input.
-/
namespace CurrentAFT.CurrentSourceLayout

open AFT CurrentSourceProtection GaussianProductProtection CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension

private def moveClosure (Path Legs Queue Closure : Type*) :
    ((Path ⊕ Legs) ⊕ Queue) ⊕ Closure ≃ (Path ⊕ Closure) ⊕ (Legs ⊕ Queue) where
  toFun
    | .inl (.inl (.inl path)) => .inl (.inl path)
    | .inl (.inl (.inr legs)) => .inr (.inl legs)
    | .inl (.inr queue) => .inr (.inr queue)
    | .inr closure => .inl (.inr closure)
  invFun
    | .inl (.inl path) => .inl (.inl (.inl path))
    | .inl (.inr closure) => .inr closure
    | .inr (.inl legs) => .inl (.inl (.inr legs))
    | .inr (.inr queue) => .inl (.inr queue)
  left_inv := by rintro (((path | legs) | queue) | closure) <;> rfl
  right_inv := by rintro ((path | closure) | (legs | queue)) <;> rfl

def bodyNumbering (security : ℕ) :
    (Fin (bodyEdges security) ⊕ Unit) ≃ Fin (Parameters.bodySize security) :=
  ((Equiv.sumCongr (Equiv.refl _) unitToFinOne).trans finSumFinEquiv).trans
    (bodyEquiv security).symm

def auxNumbering (security : ℕ) :
    ((Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit) ≃
      Fin (Parameters.legCount security * 2 + 1) :=
  ((Equiv.sumCongr finSumFinEquiv unitToFinOne).trans finSumFinEquiv).trans
    (finCongr (by omega))

def sourceNumbering (security : ℕ) :
    (Fin (Parameters.dimension security) ⊕ Unit) ≃ Fin (sourceCount security) :=
  (Equiv.sumCongr (coordinateNumbering security).symm (Equiv.refl Unit)).trans
    ((Equiv.sumCongr (Equiv.sumCongr
      (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security)).symm
      (Equiv.refl Unit)) (Equiv.refl Unit)).trans
    ((moveClosure _ _ _ _).trans
    ((Equiv.sumCongr (bodyNumbering security) (auxNumbering security)).trans finSumFinEquiv)))

theorem numbering_path (security : ℕ) (path : Fin (bodyEdges security)) :
    sourceNumbering security (.inl (coordinateNumbering security
      (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inl path))))) =
        bodyPosition security ((bodyEquiv security).symm path.castSucc) := by
  simp [sourceNumbering, moveClosure, bodyNumbering, bodyPosition, unitToFinOne]
  rfl

theorem numbering_first (security : ℕ) (leg : Fin (Parameters.legCount security)) :
    sourceNumbering security (.inl (coordinateNumbering security
      (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inl leg)))))) =
        auxPosition security (Fin.cast (by omega)
          ((leg.castAdd (Parameters.legCount security)).castAdd 1)) := by
  apply Fin.ext
  simp [sourceNumbering, moveClosure, auxNumbering, auxPosition, unitToFinOne]
  rfl

theorem numbering_second (security : ℕ) (leg : Fin (Parameters.legCount security)) :
    sourceNumbering security (.inl (coordinateNumbering security
      (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inr leg)))))) =
        auxPosition security (Fin.cast (by omega)
          ((Fin.natAdd (Parameters.legCount security) leg).castAdd 1)) := by
  apply Fin.ext
  simp [sourceNumbering, moveClosure, auxNumbering, auxPosition, unitToFinOne]
  rfl

theorem numbering_queue (security : ℕ) :
    sourceNumbering security (.inl (coordinateNumbering security (.inr ()))) =
      auxPosition security (Fin.last (Parameters.legCount security * 2)) := by
  apply Fin.ext
  simp [sourceNumbering, moveClosure, auxNumbering, auxPosition, unitToFinOne]
  rfl

theorem numbering_closure (security : ℕ) :
    sourceNumbering security (.inr ()) =
      bodyPosition security ((bodyEquiv security).symm (Fin.last (bodyEdges security))) := by
  apply Fin.ext
  simp [sourceNumbering, moveClosure, bodyNumbering, bodyPosition, unitToFinOne]
  rfl

def hiddenWord (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.dimension security) → ℤ := fun index => word (sourceNumbering security (.inl index))

def closureScalar (security : ℕ) (word : Fin (sourceCount security) → ℤ) : ℤ :=
  word (sourceNumbering security (.inr ()))

def hiddenCoordinates (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (Fin (edgeCount security) → ℤ) × ℤ :=
  ((fun edge => hiddenWord security word (coordinateNumbering security (.inl edge))),
    hiddenWord security word (coordinateNumbering security (.inr ())))

def bodyLatent (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.bodySize security) → ℤ := fun index => word (bodyPosition security index)

def firstInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.legCount security) → ℤ :=
  fun leg => word (auxPosition security (auxNumbering security (.inl (.inl leg))))

def secondInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.legCount security) → ℤ :=
  fun leg => word (auxPosition security (auxNumbering security (.inl (.inr leg))))

def queueInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) : ℤ :=
  word (auxPosition security (Fin.last (Parameters.legCount security * 2)))

theorem hiddenCoordinates_body (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (LobsterCoordinates.edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).1 =
        Fin.init (fun index => bodyLatent security word ((bodyEquiv security).symm index)) := by
  funext index
  change word (sourceNumbering security (.inl (coordinateNumbering security
    (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inl index)))))) = _
  rw [numbering_path]
  rfl

theorem hiddenCoordinates_first (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (LobsterCoordinates.edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).2.1 = firstInput security word := by
  funext index
  change word (sourceNumbering security (.inl (coordinateNumbering security
    (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inl index))))))) = _
  rw [numbering_first]
  rfl

theorem hiddenCoordinates_second (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (LobsterCoordinates.edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).2.2 = secondInput security word := by
  funext index
  change word (sourceNumbering security (.inl (coordinateNumbering security
    (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inr index))))))) = _
  rw [numbering_second]
  rfl

theorem hiddenCoordinates_queue (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (hiddenCoordinates security word).2 = queueInput security word := by
  change word (sourceNumbering security (.inl (coordinateNumbering security (.inr ())))) = _
  rw [numbering_queue]
  rfl

theorem bodyLatent_from_hidden (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin.snoc (LobsterCoordinates.edgeCoordinates ℤ (bodyEdges security) (Parameters.legCount security)
      (hiddenCoordinates security word).1).1 (closureScalar security word) =
        fun index => bodyLatent security word ((bodyEquiv security).symm index) := by
  rw [hiddenCoordinates_body]
  have hclosure : closureScalar security word =
      bodyLatent security word ((bodyEquiv security).symm (Fin.last (bodyEdges security))) := by
    unfold closureScalar
    rw [numbering_closure]
    rfl
  rw [hclosure, Fin.snoc_init_self]

/-- This is a genuine coordinate equivalence, including the public closure;
no source coordinate is dropped or duplicated. -/
def splitWord (security : ℕ) : (Fin (sourceCount security) → ℤ) ≃
    (Fin (Parameters.dimension security) → ℤ) × ℤ where
  toFun word := (hiddenWord security word, closureScalar security word)
  invFun pair index := Sum.elim pair.1 (fun _ => pair.2) ((sourceNumbering security).symm index)
  left_inv word := by
    funext index
    change Sum.elim (fun position => word (sourceNumbering security (.inl position)))
      (fun _ : Unit => word (sourceNumbering security (.inr ())))
        ((sourceNumbering security).symm index) = word index
    have h : (fun position => word (sourceNumbering security position)) =
        Sum.elim (fun position => word (sourceNumbering security (.inl position)))
          (fun _ : Unit => word (sourceNumbering security (.inr ()))) := by
      funext position
      rcases position with position | position
      · rfl
      · cases position; rfl
    rw [← h]
    exact congrArg word ((sourceNumbering security).apply_symm_apply index)
  right_inv pair := by
    apply Prod.ext
    · funext index
      simp [hiddenWord]
    · simp [closureScalar]

theorem fullMass_split (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    fullMass (width security) (sourceCount security) word =
      fullMass (width security) (Parameters.dimension security) (hiddenWord security word) *
        GaussianSource.integerMass (width security) (closureScalar security word) := by
  unfold fullMass
  rw [← Equiv.prod_comp (sourceNumbering security)]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, hiddenWord, closureScalar]

theorem cutoff_closure (security : ℕ) :
    cutoff security (sourceNumbering security (.inr ())) = DiffuseProfiles.edgeCutoff security := by
  rw [numbering_closure, cutoff_body]

def hiddenCutoff (security : ℕ) (index : Fin (Parameters.dimension security)) : ℕ :=
  cutoff security (sourceNumbering security (.inl index))

theorem protectedMass_split (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    protectedMass (width security) (cutoff security) word =
      protectedMass (width security) (hiddenCutoff security) (hiddenWord security word) *
        GaussianWindowProtection.protectedMass (width security) (DiffuseProfiles.edgeCutoff security)
          (closureScalar security word) := by
  unfold protectedMass
  rw [← Equiv.prod_comp (sourceNumbering security)]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, hiddenCutoff, hiddenWord,
    closureScalar]
  change _ * GaussianWindowProtection.protectedMass _
    (cutoff security (sourceNumbering security (.inr ()))) _ = _
  rw [cutoff_closure]

def hiddenProtectedWord (security : ℕ) (word : ProtectedWord (cutoff security)) :
    ProtectedWord (hiddenCutoff security) :=
  fun index => word (sourceNumbering security (.inl index))

def protectedClosure (security : ℕ) (word : ProtectedWord (cutoff security)) :
    GaussianSource.Window (DiffuseProfiles.edgeCutoff security) :=
  ⟨(word (sourceNumbering security (.inr ()))).val, by
    simpa only [cutoff_closure] using (word (sourceNumbering security (.inr ()))).property⟩

/-- The actual finite protected-window weight factors into the hidden
window product and the independent public closing-edge window. -/
theorem protectedLaw_weight_split (security : ℕ) (word : ProtectedWord (cutoff security)) :
    (protectedSourceLaw security).weight word =
      (GaussianProductProtection.protectedLaw (width security) (hiddenCutoff security)).weight
        (hiddenProtectedWord security word) *
      (GaussianSource.windowGaussian (width security) (DiffuseProfiles.edgeCutoff security)).weight
        (protectedClosure security word) := by
  change (GaussianProductProtection.protectedLaw (width security) (cutoff security)).weight word = _
  rw [← protectedMass_on_word (width security) (width_pos security) (cutoff security),
    protectedMass_split]
  apply congrArg₂ (· * ·)
  · exact protectedMass_on_word (width security) (width_pos security) (hiddenCutoff security)
      (hiddenProtectedWord security word)
  · have h := GaussianWindowProtection.protectedMass_window (width security)
      (DiffuseProfiles.edgeCutoff security) (width_pos security) (protectedClosure security word).val
    rw [dif_pos (protectedClosure security word).property] at h
    exact h

/-- The unbounded hidden part is exactly the manuscript's dimension-
dimensional lattice Gaussian, independently of the public closure. -/
theorem fullGaussian_mass_split (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (GaussianSource.latticeGaussian (sourceCount security) (width security) (width_pos security) word).toReal =
      (GaussianSource.latticeGaussian (Parameters.dimension security) (width security)
        (width_pos security) (hiddenWord security word)).toReal *
      (GaussianSource.integerGaussian (width security) (width_pos security) (closureScalar security word)).toReal := by
  rw [← fullMass_actual, fullMass_split]
  congr 1
  · rw [GaussianSource.latticeGaussian, GaussianSource.independentCoordinates_apply, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro index _
    exact GaussianWindowProtection.integerMass_actual (width security) (width_pos security) _
  · exact GaussianWindowProtection.integerMass_actual (width security) (width_pos security) _

end
end CurrentAFT.CurrentSourceLayout

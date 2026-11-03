import AFT.FiniteSetNumberingTransport
import AFT.ParameterProgram

/-! # Executable arithmetic public control pools and matched center words

Every set below is computed from integer comparisons and an explicitly
supplied permutation. The only ordering is the ordinary order on `Fin`.
-/
namespace AFT.PublicPoolProgram

def controlSet (population legs queue : ℕ) (placement : Equiv.Perm (Fin population)) :
    Finset (Fin population) :=
  Finset.univ.filter (fun index => index.val < legs ∧ queue ≤ (placement index).val)

def availableSet (population legs queue : ℕ) (placement : Equiv.Perm (Fin population)) :
    Finset (Fin population) :=
  Finset.univ.filter (fun index => legs ≤ index.val ∧ queue ≤ (placement index).val)

def matching (population legs queue : ℕ) (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card) :
    controlSet population legs queue placement ↪ availableSet population legs queue placement :=
  finiteSetMatching (Equiv.refl _) _ _ hsize

def matchingSet (population legs queue : ℕ) (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card) : Finset (Fin population) :=
  Finset.univ.map ⟨fun point => (matching population legs queue placement hsize point).val,
    fun _ _ h => (matching population legs queue placement hsize).injective (Subtype.ext h)⟩

def reserveSet (population legs queue : ℕ) (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card) : Finset (Fin population) :=
  availableSet population legs queue placement \ matchingSet population legs queue placement hsize

def pairWord {Color : Type*} (population legs queue : ℕ)
    (placement : Equiv.Perm (Fin population))
    (hsize : (controlSet population legs queue placement).card ≤
      (availableSet population legs queue placement).card)
    (marks centers : Fin population → Color) :
    Fin (controlSet population legs queue placement).card ⊕
      Fin (reserveSet population legs queue placement hsize).card → Color × Color
  | .inl index =>
      let control := finiteSetNumbering (Equiv.refl _) (controlSet population legs queue placement) index
      (marks control, centers (matching population legs queue placement hsize control))
  | .inr index =>
      let body := finiteSetNumbering (Equiv.refl _) (reserveSet population legs queue placement hsize) index
      (marks body, centers body)

/-- The sizes used by the runtime are literal integer operations on the
already executable bounded prime search. -/
def population (n : ℕ) : ℕ :=
  (ParameterProgram.modulus n).value * (max 2 n)^20 - 2*(max 2 n)^30

def legCount (n : ℕ) : ℕ := (max 2 n)^30

theorem population_eq (n : ℕ) : population n = Parameters.bodies n := by
  simp only [population, ParameterProgram.modulus_value, Parameters.bodies,
    Parameters.dimension, Parameters.meanDensity, Parameters.legs, Parameters.security]

theorem legCount_eq (n : ℕ) : legCount n = Parameters.legs n := rfl

end AFT.PublicPoolProgram

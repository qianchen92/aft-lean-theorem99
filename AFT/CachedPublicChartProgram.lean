import AFT.ActualChartCountedSampler
import AFT.ActualPublicChartProgram
import AFT.CountedRationalRejection

/-! # Stored public-chart metadata and legal finite-array output

The feature and palette tables are materialized before either Neumann loop.
The legal fallback uses that same stored safe/fiber union. This file proves
literal program agreement; the cost of constructing these integer metadata
is kept separate from the existing rational-arithmetic counter.
-/
namespace AFT.BoundaryCalibration
open V7Calibration RationalNumerics RationalRejectionProgram
open scoped BigOperators

structure PublicChartMetadata (charts colors features : ℕ) where
  feature : Vector (Vector (Fin colors) charts) features
  allowed : Vector (Finset (Fin colors)) features
  safe : Finset (Fin charts)
  fiber : Finset (Fin charts)

def actualPublicChartMetadata (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    PublicChartMetadata (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))
      (chartProgramModulus n) ((2*chartProgramCutoff constant n+1)*(2*chartProgramCutoff constant n+1)) :=
  let cutoff := chartProgramCutoff constant n
  let colors := chartProgramModulus n
  let feature := Vector.ofFn (fun index => Vector.ofFn (finiteProtectedFeatures cutoff colors index))
  let allowed := Vector.ofFn (finiteProtectedPalettes cutoff colors boundary baseline)
  let safe := finiteMarkedSafe (fun index chart => (feature.get index).get chart)
    (finiteAffineScale colors) allowed.get
  let fiber := finiteMarkedFiber (fun index chart => (feature.get index).get chart)
    (finiteAffineScale colors) allowed.get (finiteProtectedMark cutoff) mark
  ⟨feature,allowed,safe,fiber⟩

theorem actualPublicChartMetadata_feature (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    (fun index chart => ((actualPublicChartMetadata constant n boundary baseline mark).feature.get index).get chart)=
      finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n) := by
  funext index chart
  simp only [actualPublicChartMetadata,Vector.get_ofFn]

theorem actualPublicChartMetadata_allowed (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    (actualPublicChartMetadata constant n boundary baseline mark).allowed.get=
      finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline := by
  funext index
  simp only [actualPublicChartMetadata,Vector.get_ofFn]

theorem actualPublicChartMetadata_safe (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    (actualPublicChartMetadata constant n boundary baseline mark).safe=
      finiteMarkedSafe (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n))
        (finiteAffineScale (chartProgramModulus n))
        (finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline) := by
  change finiteMarkedSafe _ _ _=_
  rw [show (fun index chart => (Vector.ofFn (fun index => Vector.ofFn
    (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n) index))).get index |>.get chart)=
    finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n) by
      funext index chart;simp only [Vector.get_ofFn]]
  congr 1
  funext index
  exact Vector.get_ofFn _ index

theorem actualPublicChartMetadata_fiber (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    (actualPublicChartMetadata constant n boundary baseline mark).fiber=
      finiteMarkedFiber (finiteProtectedFeatures (chartProgramCutoff constant n) (chartProgramModulus n))
        (finiteAffineScale (chartProgramModulus n))
        (finiteProtectedPalettes (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline)
        (finiteProtectedMark (chartProgramCutoff constant n)) mark := by
  unfold actualPublicChartMetadata
  simp only [Vector.get_ofFn]
  congr 1
  funext index
  exact Vector.get_ofFn _ index

/-- The existing rational-arithmetic loop now reads the stored feature and
palette arrays. Metadata construction has its own accounting obligation. -/
def publicChartTicketFromMetadata (constant n : ℕ)
    (metadata : PublicChartMetadata (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))
      (chartProgramModulus n) ((2*chartProgramCutoff constant n+1)*(2*chartProgramCutoff constant n+1)))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    BetaReference.CountedNatural :=
  countedMarkedChartFinDraw (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n))
    (chartProgramModulus n) ((2*chartProgramCutoff constant n+1)*(2*chartProgramCutoff constant n+1))
    (fun index chart => (metadata.feature.get index).get chart) metadata.allowed.get metadata.safe metadata.fiber
    (finiteProtectedMark (chartProgramCutoff constant n)) (finiteProtectedAtom (chartProgramCutoff constant n)) n n word

def cachedPublicChartTicket (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    BetaReference.CountedNatural :=
  let metadata := actualPublicChartMetadata constant n boundary baseline mark
  publicChartTicketFromMetadata constant n metadata word

theorem cachedPublicChartTicket_eq (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    cachedPublicChartTicket constant n boundary baseline mark word=
      actualCountedChartTicket constant n boundary baseline mark word := by
  unfold cachedPublicChartTicket publicChartTicketFromMetadata
  dsimp only
  rw [actualPublicChartMetadata_feature,actualPublicChartMetadata_allowed,
    actualPublicChartMetadata_safe,actualPublicChartMetadata_fiber]
  rfl

/-- A complete legal chart index, with no choice from an abstract support. -/
def cachedSafePublicChartIndex (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) :=
  let metadata := actualPublicChartMetadata constant n boundary baseline mark
  let ticket := publicChartTicketFromMetadata constant n metadata word
  let index : Fin (chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)) :=
    ⟨ticket.value,by
      change (cachedPublicChartTicket constant n boundary baseline mark word).value<_
      rw [cachedPublicChartTicket_eq,actualCountedChartTicket_value]
      exact (actualFiniteAffineChartDraw constant n boundary baseline mark n n word).isLt⟩
  legalChartIndex _ (metadata.safe∪metadata.fiber) index

theorem cachedSafePublicChartIndex_value (constant n : ℕ) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n))
    (word : Fin (n+chartProgramModulus n*(chartProgramModulus n*chartProgramModulus n)+1) → Fin 2) :
    cachedSafePublicChartIndex constant n boundary baseline mark word=
      safeFiniteAffineChartDraw (chartProgramCutoff constant n) (chartProgramModulus n) boundary baseline mark n n word := by
  unfold cachedSafePublicChartIndex safeFiniteAffineChartDraw finiteAffineLegalSet
  dsimp only
  rw [actualPublicChartMetadata_safe,actualPublicChartMetadata_fiber]
  congr 1
  apply Fin.ext
  exact (congrArg BetaReference.CountedNatural.value (cachedPublicChartTicket_eq constant n boundary baseline mark word)).trans
    (actualCountedChartTicket_value constant n boundary baseline mark word)

/-- Decode the stored finite index and transport only public type indices. -/
def cachedActualPublicChartDraw (constant n : ℕ) (baseline : ℤ) :
    Fin (Parameters.modulus n) →
      (Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2) →
        Chart (ZMod (Parameters.modulus n)) :=
  cast (congrArg (fun colors => Fin colors →
    (Fin (n+colors*(colors*colors)+1) → Fin 2) → Chart (ZMod colors))
      (show chartProgramModulus n=Parameters.modulus n from ParameterProgram.modulus_value n))
    (fun mark word => finiteChartEquiv (chartProgramModulus n)
      (cachedSafePublicChartIndex constant n (actualBoundaryHalfProgram constant n) baseline mark word))

theorem cachedActualPublicChartDraw_value (constant n : ℕ) (baseline : ℤ)
    (mark : Fin (Parameters.modulus n))
    (word : Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2) :
    cachedActualPublicChartDraw constant n baseline mark word=actualPublicChartDraw constant n baseline mark word := by
  have he : (fun mark word => finiteChartEquiv (chartProgramModulus n)
      (cachedSafePublicChartIndex constant n (actualBoundaryHalfProgram constant n) baseline mark word))=
    (fun mark word => finiteChartEquiv (chartProgramModulus n)
      (safeFiniteAffineChartDraw (chartProgramCutoff constant n) (chartProgramModulus n)
        (actualBoundaryHalfProgram constant n) baseline mark n n word)) := by
    funext mark word
    rw [cachedSafePublicChartIndex_value]
  unfold cachedActualPublicChartDraw
  rw [he]
  rfl

def PublicChartMetadata.cells {charts colors features : ℕ} (metadata : PublicChartMetadata charts colors features) : ℕ :=
  charts*features+(∑ index,(metadata.allowed.get index).card)+metadata.safe.card+metadata.fiber.card

theorem PublicChartMetadata.cells_le {charts colors features : ℕ} (metadata : PublicChartMetadata charts colors features) :
    metadata.cells≤charts*features+colors*features+2*charts := by
  have ha := Finset.sum_le_sum (s:=Finset.univ) (fun (index : Fin features) _ =>
    Finset.card_le_univ (s:=metadata.allowed.get index))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at ha
  have hs := Finset.card_le_univ (s:=metadata.safe)
  have hf := Finset.card_le_univ (s:=metadata.fiber)
  simp only [Fintype.card_fin] at hs hf
  unfold PublicChartMetadata.cells
  nlinarith

/-- The entire explicit metadata, including both legal supports, occupies
polynomially many entries at the actual parameters. -/
theorem actualPublicChartMetadata_cells (constant n : ℕ) (hn : 2≤n) (boundary baseline : ℤ)
    (mark : Fin (chartProgramModulus n)) :
    (actualPublicChartMetadata constant n boundary baseline mark).cells≤
      (8*n^120)*(9*(constant+1)^2*n^4)+(2*n^40)*(9*(constant+1)^2*n^4)+16*n^120 := by
  have hh := (actualPublicChartMetadata constant n boundary baseline mark).cells_le
  have hb := actual_chart_array_bounds constant n hn
  apply hh.trans
  have hq := hb.1
  have hc := hb.2.1
  have hf := hb.2.2
  dsimp only [actualChartCountBound] at hc
  dsimp only [actualChartFeatureBound] at hf
  calc
    _≤(8*n^120)*(9*(constant+1)^2*n^4)+(2*n^40)*(9*(constant+1)^2*n^4)+2*(8*n^120) := by
      gcongr
    _=_ := by ring

end AFT.BoundaryCalibration

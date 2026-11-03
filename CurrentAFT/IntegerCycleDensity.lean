import CurrentAFT.CycleDensity

/-!
# Exact integer-to-residue root-density bridge

The integer roots use their actual finite difference window. When the
modulus exceeds its diameter, reduction is injective on that window and
preserves the complete centered weighted L2 norm exactly.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color Image Index : Type*} [Fintype Color] [Fintype Image]
  [Fintype Index] [DecidableEq Index]

theorem map_injective_weight (law : FiniteDist Color) (encode : Color → Image)
    (hinjective : Function.Injective encode) (color : Color) :
    (law.map encode).weight (encode color) = law.weight color := by
  rw [FiniteDist.map_weight]
  simp only [hinjective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact finite independence after coordinatewise deterministic mapping. -/
theorem independent_coordinate_map (reference : Index → FiniteDist Color) (encode : Color → Image) :
    (FiniteDist.independent reference).map (fun input index => encode (input index)) =
      FiniteDist.independent (fun index => (reference index).map encode) := by
  ext output
  simp only [FiniteDist.map_weight, FiniteDist.independent]
  have he := Fintype.prod_sum (fun index color =>
    if encode color = output index then (reference index).weight color else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr (by ext; simp)
  intro input _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

/-- Centering commutes pointwise with an injective finite encoding. -/
theorem centeredRootDensity_injective_map (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (encode : Color → Image)
    (hinjective : Function.Injective encode) (output : Index → Color) :
    centeredRootDensity (joint.map (fun input index => encode (input index)))
      (fun index => (reference index).map encode) (fun index => encode (output index)) =
        centeredRootDensity joint reference output := by
  unfold centeredRootDensity
  rw [FiniteDist.expectation_map]
  apply congrArg joint.expectation
  funext input
  apply Finset.prod_congr rfl
  intro index _
  unfold centeredRootAtom
  rw [map_injective_weight _ encode hinjective]
  simp only [hinjective.eq_iff]

/-- No norm is lost when the finite scalar encoding is injective. This
identity includes zero reference atoms outside the encoded image. -/
theorem centeredRootDensity_energy_injective_map (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (encode : Color → Image)
    (hinjective : Function.Injective encode) :
    (FiniteDist.independent (fun index => (reference index).map encode)).l2Sq
      (centeredRootDensity (joint.map (fun input index => encode (input index)))
        (fun index => (reference index).map encode)) =
      (FiniteDist.independent reference).l2Sq (centeredRootDensity joint reference) := by
  rw [← independent_coordinate_map, FiniteDist.l2Sq_map]
  apply congrArg (FiniteDist.independent reference).l2Sq
  funext output
  exact centeredRootDensity_injective_map joint reference encode hinjective output

/-- The true protected integer-root reference on its exact finite support. -/
def integerRootReference (width : ℝ) (cutoff : ℕ) :
    FiniteDist (GaussianSource.Window (2 * cutoff)) :=
  PathLikelihood.marginal (GaussianSource.windowGaussian width cutoff) (PathLikelihood.windowDifference cutoff)

/-- Selected integer roots, preserving the complete independent latent cycle. -/
def integerSelectedLaw (body order cutoff : ℕ) (width : ℝ) (sites : Selection body order) :
    FiniteDist (Fin order → GaussianSource.Window (2 * cutoff)) :=
  selectedFeatureLaw body order (GaussianSource.windowGaussian width cutoff)
    (PathLikelihood.windowDifference cutoff) sites

def integerAveragedSelectedLaw (body order cutoff : ℕ) (width : ℝ) (horder : order ≤ body) :
    FiniteDist (Fin order → GaussianSource.Window (2 * cutoff)) :=
  (selectionLaw body order horder).mix (integerSelectedLaw body order cutoff width)

/-- Exact reduction of the actual integer reference, with the subtraction
orientation reversed only through swapping the two iid latent scalars. -/
theorem integerRootReference_modulo (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    (integerRootReference width cutoff).map
      (fun color => ((color : ℤ) : ZMod modulus)) = gaussianRootReference width cutoff modulus := by
  unfold integerRootReference PathLikelihood.marginal
  rw [FiniteDist.map_map]
  convert marginal_sub_eq (GaussianSource.windowGaussian width cutoff)
    (fun scalar => ((scalar : ℤ) : ZMod modulus)) using 1
  apply congrArg ((GaussianSource.windowGaussian width cutoff).prod
    (GaussianSource.windowGaussian width cutoff)).map
  funext pair
  exact Int.cast_sub _ _

theorem integerSelectedLaw_modulo (body order cutoff modulus : ℕ) [NeZero modulus]
    (width : ℝ) (sites : Selection body order) :
    (integerSelectedLaw body order cutoff width sites).map
      (fun word index => ((word index : ℤ) : ZMod modulus)) =
        selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites := by
  rw [← selectedFeatureLaw_sub_eq]
  unfold integerSelectedLaw selectedFeatureLaw
  rw [FiniteDist.map_map]
  apply congrArg (FiniteDist.independent (fun _ : Fin body => GaussianSource.windowGaussian width cutoff)).map
  funext latent slot
  exact Int.cast_sub _ _

theorem integerAveragedSelectedLaw_modulo (body order cutoff modulus : ℕ) [NeZero modulus]
    (width : ℝ) (horder : order ≤ body) :
    (integerAveragedSelectedLaw body order cutoff width horder).map
      (fun word index => ((word index : ℤ) : ZMod modulus)) =
        averagedSelectedLaw body order modulus horder (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)) := by
  unfold integerAveragedSelectedLaw averagedSelectedLaw
  rw [FiniteDist.map_mix]
  simp_rw [integerSelectedLaw_modulo]

/-- Reduction is injective on the full integer difference window as soon
as the modulus exceeds its diameter. -/
theorem integerRoot_modulo_injective (cutoff modulus : ℕ) (hmodulus : 4 * cutoff < modulus) :
    Function.Injective (fun color : GaussianSource.Window (2 * cutoff) => ((color : ℤ) : ZMod modulus)) := by
  intro first second hequal
  have hfirst := Finset.mem_Icc.mp first.property
  have hsecond := Finset.mem_Icc.mp second.property
  have hmod : (4 : ℤ) * cutoff < modulus := by exact_mod_cast hmodulus
  have hshift : (((first : ℤ) + 2 * cutoff : ℤ) : ZMod modulus) =
      (((second : ℤ) + 2 * cutoff : ℤ) : ZMod modulus) := by
    simpa only [Int.cast_add] using (congrArg
      (fun color : ZMod modulus => color + ((2 * (cutoff : ℤ) : ℤ) : ZMod modulus)) hequal)
  rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hshift
  apply Subtype.ext
  omega

/-- The complete centered integer-root norm equals its residue norm.
This is a support bijection, rather than a one-way contraction claim. -/
theorem integer_centered_energy_eq_residue (body order cutoff modulus : ℕ) [NeZero modulus]
    (width : ℝ) (horder : order ≤ body) (hmodulus : 4 * cutoff < modulus) :
    (FiniteDist.independent (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus horder (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus)) =
      (FiniteDist.independent (fun _ : Fin order => integerRootReference width cutoff)).l2Sq
        (centeredRootDensity (integerAveragedSelectedLaw body order cutoff width horder)
          (fun _ => integerRootReference width cutoff)) := by
  have h := centeredRootDensity_energy_injective_map
    (integerAveragedSelectedLaw body order cutoff width horder)
    (fun _ => integerRootReference width cutoff)
    (fun color => ((color : ℤ) : ZMod modulus))
    (integerRoot_modulo_injective cutoff modulus hmodulus)
  simpa only [integerRootReference_modulo, integerAveragedSelectedLaw_modulo] using h

/-- The manuscript's first centered integer-root bound with an explicit
order-only constant. Its finite support is the exact actual root window. -/
theorem integer_averaged_centered_norm_le (body order cutoff modulus : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) (hmodulus : 4 * cutoff < modulus) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order => integerRootReference width cutoff)).l2Sq
      (centeredRootDensity (integerAveragedSelectedLaw body order cutoff width (by omega))
        (fun _ => integerRootReference width cutoff))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * Real.sqrt ((4 * cutoff + 1 : ℝ) ^ order) /
        (body : ℝ) ^ ((order + 1) / 2) := by
  rw [← integer_centered_energy_eq_residue body order cutoff modulus width (by omega) hmodulus]
  exact averaged_centered_norm_le body order modulus cutoff width horder hbody

/-- The full integer statement needs no modulus hypothesis: a finite
injective residue encoding is chosen internally solely for the proof. -/
theorem integer_averaged_centered_norm_le_full (body order cutoff : ℕ)
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order => integerRootReference width cutoff)).l2Sq
      (centeredRootDensity (integerAveragedSelectedLaw body order cutoff width (by omega))
        (fun _ => integerRootReference width cutoff))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * (4 * cutoff + 1 : ℝ) ^ ((order : ℝ) / 2) /
        (body : ℝ) ^ ((order + 1) / 2) := by
  letI : NeZero (4 * cutoff + 1) := ⟨by omega⟩
  have h := integer_averaged_centered_norm_le body order cutoff (4 * cutoff + 1)
    width horder hbody (by omega)
  rwa [sqrt_nat_power_rpow _ (by positivity)] at h

/-- The first actual integer centered root component vanishes in L2. -/
theorem integer_centered_singleton_energy_zero (body cutoff : ℕ) (width : ℝ) (hbody : 2 ≤ body) :
    (FiniteDist.independent (fun _ : Fin 1 => integerRootReference width cutoff)).l2Sq
      (centeredRootDensity (integerAveragedSelectedLaw body 1 cutoff width (by omega))
        (fun _ => integerRootReference width cutoff)) = 0 := by
  letI : NeZero (4 * cutoff + 1) := ⟨by omega⟩
  rw [← integer_centered_energy_eq_residue body 1 cutoff (4 * cutoff + 1) width (by omega) (by omega)]
  exact averaged_centered_singleton_energy_zero body (4 * cutoff + 1) hbody
    (GaussianSource.windowGaussian width cutoff) (fun scalar => ((scalar : ℤ) : ZMod (4 * cutoff + 1)))

end

end CurrentAFT.CycleSelections

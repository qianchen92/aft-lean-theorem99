import AFT.LeadingGaussianScale
import AFT.GaussianSignedSum

/-! # Actual low-degree leading table energy, with no representation-size loss -/
namespace AFT.RepresentedPolynomial
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

 theorem leadingGaussianValue_output_sum (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (table : Table (InputSeed Color)) (value : Color → ℂ) :
    leadingGaussianValue reference (outputHom primary body primaryChannel bodyChannel table) value=
      ∑ powers∈table.support,((MvPolynomial.coeff powers table : ℝ) : ℂ)*
        leadingGaussianValue reference
          (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1)) value := by
  conv_lhs => rw [MvPolynomial.as_sum table]
  simp only [map_sum,leadingGaussianValue,MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro powers _
  rw [show MvPolynomial.monomial powers (MvPolynomial.coeff powers table)=
    MvPolynomial.C (MvPolynomial.coeff powers table)*MvPolynomial.monomial powers 1 by
      rw [MvPolynomial.C_mul_monomial,mul_one]]
  have hc (scalar : ℝ) : outputHom primary body primaryChannel bodyChannel (MvPolynomial.C scalar)=
      MvPolynomial.C scalar := (outputHom primary body primaryChannel bodyChannel).commutes scalar
  simp only [map_mul,hc,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C]
  rfl

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open MeasureTheory GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A true finite leading output has low-degree Fock norm controlled by its
literal input activity; neither the number of seeds nor the palette size
appears as a count of representation terms. -/
theorem actual_leading_table_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ primaryPool bodyPool : ℕ,0<primaryPool →0<bodyPool →
    primaryPool ≤ Parameters.dimension n →bodyPool ≤ Parameters.dimension n →
    ∀ cutoff table,
    truncate (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder) cutoff table=table →
    ∀ scale : ℝ,0 ≤ scale →scale ≤ 1 →
    (∫ value,Complex.normSq (leadingGaussianValue (actualReferenceLaw C n (beta n)).weight
      (actualLeadingOutput C n (beta n) table) (fun color => (scale : ℂ)*value color)) ∂FockGaussian.field) ≤
    (leadingGaussianFactor n cutoff * activity
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2)) table)^2 := by
  filter_upwards [actual_leading_monomial_scaled_energy_eventually C hC beta hbeta]
    with n he primaryPool bodyPool hp hb hpN hbN cutoff table ht scale hs hs1
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2)
  let function := fun (powers : InputSeed (Fin (Parameters.modulus n)) →₀ ℕ) (value : Fin (Parameters.modulus n) → ℂ) => leadingGaussianValue (actualReferenceLaw C n (beta n)).weight
    (actualLeadingOutput C n (beta n) (MvPolynomial.monomial powers 1)) (fun color => (scale : ℂ)*value color)
  have hm powers : MemLp (function powers) 2 FockGaussian.field :=
    leading_monomial_scaled_memLp _ _ _ _ _ powers scale
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed (sq_nonneg _)
  have hbnd powers : 0 ≤ leadingGaussianFactor n cutoff*monomialWeight weight powers :=
    mul_nonneg (leadingGaussianFactor_nonneg n cutoff) (monomialWeight_nonneg weight hw powers)
  have henergy powers (hmem : powers∈table.support) :
      (∫ value,Complex.normSq (function powers value) ∂FockGaussian.field) ≤
        (leadingGaussianFactor n cutoff*monomialWeight weight powers)^2 := by
    have horder : weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff := by
      have hcut : powers∈(truncate (fun seed => seed.primaryOrder+seed.bodyOrder) cutoff table).support := by rw [ht]; exact hmem
      exact (Finset.mem_filter.mp hcut).2
    exact he primaryPool bodyPool hp hb hpN hbN cutoff powers horder scale hs hs1
  have hh := GaussianSignedSum.field_sum_energy_le table.support function
    (fun powers => MvPolynomial.coeff powers table)
    (fun powers => leadingGaussianFactor n cutoff*monomialWeight weight powers)
    (fun powers _ => hm powers) (fun powers _ => hbnd powers) henergy
  have hsum : (∑ powers∈table.support,|MvPolynomial.coeff powers table| *
      (leadingGaussianFactor n cutoff*monomialWeight weight powers))=
      leadingGaussianFactor n cutoff*activity weight table := by
    unfold activity Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro powers _
    simp only [MvPolynomial.coeff]
    ring
  rw [hsum] at hh
  have heq (value : Fin (Parameters.modulus n) → ℂ) := leadingGaussianValue_output_sum (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (actualReferenceLaw C n (beta n)).weight (actualPrimaryChannel C n) (actualBodyChannel n) table
    (fun color => (scale : ℂ)*value color)
  unfold actualLeadingOutput
  simp_rw [heq]
  exact hh

end
end AFT.V7Calibration

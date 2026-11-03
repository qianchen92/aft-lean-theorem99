import AFT.V7PrimaryInverse

/-!
# Actual public anchor support and the calibrated legal-input projection
-/

namespace AFT.V7Calibration

open scoped BigOperators

/-- Every point of the actual reflected public anchor remains safe after
any displacement admitted by the physical margin. -/
theorem publicAnchorStart_safe (modulus width : ℕ) (color : Fin modulus) (coin : Bool)
    (shift margin : ℤ) (hmodulus : 6 * width + 1 ≤ modulus)
    (hmargin : margin + |shift| ≤ width) (output : ℤ)
    (houtput : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :
    margin ≤ output ∧ output < (modulus : ℤ) - margin := by
  have hq : 0 < modulus := Nat.zero_lt_of_lt color.isLt
  have hqcast : ((modulus - 1 : ℕ) : ℤ) = (modulus : ℤ) - 1 := by omega
  have hmod : 6 * (width : ℤ) + 1 ≤ modulus := by exact_mod_cast hmodulus
  have hleft (hhalf : 2 * (color.val : ℤ) ≤ (modulus : ℤ) - 1)
      (hc : output ∈ anchorInterval ((modulus : ℤ) - color.val - 2 * width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := (modulus : ℤ) - 1 - color.val + shift - output
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_left_safe modulus width color.val offset shift margin |shift|
      hmod (by positivity) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  have hright (hhalf : (modulus : ℤ) - 1 ≤ 2 * (color.val : ℤ))
      (hc : output ∈ anchorInterval ((modulus : ℤ) - 1 - color.val + width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := output - ((modulus : ℤ) - 1 - color.val + shift)
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_right_safe modulus width color.val offset shift margin |shift|
      hmod (by exact_mod_cast color.isLt) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  unfold publicAnchorStart at houtput
  split_ifs at houtput with hl hr hc
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput

/-- The actual two translated anchors occupy the interior palette; the
proof retains their common underlying source state. -/
theorem error_anchor_support {υ : Type*} (parameter : ℕ) (boundary : ℤ)
    (bodyShift sourceShift : υ → ℤ)
    (hbMargin : boundary ≤ Parameters.safeMargin parameter)
    (hbody : ∀ index, (Parameters.safeMargin parameter : ℤ) + |bodyShift index| ≤ Parameters.anchorWidth parameter)
    (hsource : ∀ index, (Parameters.safeMargin parameter : ℤ) + |sourceShift index| ≤ Parameters.anchorWidth parameter)
    (index : υ × Bool) (color : Fin (Parameters.modulus parameter)) :
    anchorInterval (errorStarts parameter sourceShift index color) (Parameters.anchorWidth parameter) ∪
      anchorInterval (errorStarts parameter sourceShift index color + errorShift bodyShift sourceShift index)
        (Parameters.anchorWidth parameter) ⊆
      (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ.image (fun color => (color.val : ℤ)) := by
  intro output hout
  have hs : (Parameters.safeMargin parameter : ℤ) ≤ output ∧
      output < (Parameters.modulus parameter : ℤ) - Parameters.safeMargin parameter := by
    rcases Finset.mem_union.mp hout with hleft | hright
    · exact publicAnchorStart_safe _ _ _ _ _ _ (Parameters.anchor_clearance parameter)
        (hsource index.1) output hleft
    · have heq : errorStarts parameter sourceShift index color + errorShift bodyShift sourceShift index =
          publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color index.2 +
            bodyShift index.1 := by unfold errorStarts errorShift; ring
      rw [heq] at hright
      exact publicAnchorStart_safe _ _ _ _ _ _ (Parameters.anchor_clearance parameter)
        (hbody index.1) output hright
  have hbounds : 0 ≤ output ∧ output < Parameters.modulus parameter := by omega
  let point : Fin (Parameters.modulus parameter) := ⟨output.toNat, by omega⟩
  have heq : (point.val : ℤ) = output := by dsimp [point]; omega
  refine Finset.mem_image.mpr ⟨point, ?_, heq⟩
  rw [Finset.mem_compl, mem_boundaryPalette, heq]
  omega

/-- The concrete inverse from `response_inverse_eventually` conjugates
the actual boundary projection into legal canonical inputs. -/
theorem response_safe_projection {τ υ : Type*} [Fintype τ] [Fintype υ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ)
    (bodyShift sourceShift : υ → ℤ) (noiseLaw : FiniteDist υ)
    (primaryLaw : Fin (Parameters.modulus parameter) → ℝ)
    (hb : 0 ≤ boundary) (hbMargin : boundary ≤ Parameters.safeMargin parameter)
    (hclear : 2 * boundary < Parameters.modulus parameter)
    (hbody : ∀ index, (Parameters.safeMargin parameter : ℤ) + |bodyShift index| ≤ Parameters.anchorWidth parameter)
    (hsource : ∀ index, (Parameters.safeMargin parameter : ℤ) + |sourceShift index| ≤ Parameters.anchorWidth parameter)
    (hp : ∀ color, 0 < primaryLaw color)
    (hv : ∑ color, signResponse parameter cutoffScale boundary startsPlus startsMinus sources sourceLaw color = 0)
    (operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ))
    (hoperator : operator.toLinearMap = responseOperator parameter cutoffScale boundary
      startsPlus startsMinus sources sourceLaw bodyShift sourceShift noiseLaw) :
    let interior := (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ
    (∀ profile, legalInputProjection operator (boundaryIdealProjection interior primaryLaw) profile ∈
      canonicalInteriorProfiles interior) ∧
    (∀ profile, operator (legalInputProjection operator (boundaryIdealProjection interior primaryLaw) profile) =
      boundaryIdealProjection interior primaryLaw (operator profile)) ∧
    (∀ profile ∈ canonicalInteriorProfiles interior,
      legalInputProjection operator (boundaryIdealProjection interior primaryLaw) profile = profile) := by
  dsimp only
  have hinj : Function.Injective (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ)) := by
    intro a b heq
    apply Fin.ext
    dsimp only at heq
    exact_mod_cast heq
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hinterior : (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ.Nonempty := by
    rw [boundaryPalette, compl_compl]
    exact TrimmedSlice.paletteSlice_nonempty _ _ _ hb (by simpa using hclear)
  have hmass : (∑ color ∈ (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ, primaryLaw color) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun color _ => hp color) hinterior)
  have hsign : signResponse parameter cutoffScale boundary startsPlus startsMinus sources sourceLaw ∈
      canonicalInteriorProfiles (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ := by
    refine ⟨hv, ?_⟩
    intro color hc
    have hc' : color ∈ boundaryPalette (Parameters.modulus parameter) boundary := by simpa using hc
    exact TrimmedSlice.actualSignResponse_zero_boundary _ _ _ _ _ _ _ _ _ ((mem_boundaryPalette _ _ _).mp hc')
  exact finitePrimary_safe_projection (fun color : Fin (Parameters.modulus parameter) => (color.val : ℤ))
    (errorStarts parameter sourceShift) (errorShift bodyShift sourceShift) (Parameters.anchorWidth parameter)
    (errorLaw noiseLaw).weight hinj (pow_ne_zero _ (ne_of_gt hx))
    (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ
    (error_anchor_support parameter boundary bodyShift sourceShift hbMargin hbody hsource)
    (GaussianSource.v7Activation cutoffScale parameter) primaryLaw
    (signResponse parameter cutoffScale boundary startsPlus startsMinus sources sourceLaw)
    (paletteSign (Parameters.modulus parameter)) hmass hsign operator hoperator

end AFT.V7Calibration

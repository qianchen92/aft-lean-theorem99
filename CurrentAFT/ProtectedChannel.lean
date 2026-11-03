import CurrentAFT.ChargedEndpoint
import CurrentAFT.PublicCore

/-!
# Public charge for the assembled protected channel

The latent body edges, both inputs of each leg, and the shared queue may
have any joint finite seed law. The exact algebraic charge identity is
therefore valid after averaging those variables, without replacing their
joint law by a product of endpoint marginals.

This module verifies a channel invariant. It does not assert the Fourier
response or the Gaussian coupling estimates for that channel.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Seed Leg : Type*} [Fintype Seed] [Fintype Leg]

/-- A conditional endpoint channel retaining the full cycle and all
same-seed leg and queue dependencies, at one fixed public placement. -/
def protectedAssemblyChannel (body modulus : ℕ) [NeZero modulus]
    (seedLaw : FiniteDist Seed) (centers : Fin body → ℤ) (shift : Leg → ℤ)
    (latent : Seed → Fin body → ℤ) (bodyPlacement : Seed → Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Seed → Leg → ℤ)
    (queue : Finset (Fin body)) (scalar : Seed → ℤ)
    (finalRelabeling : Seed → Equiv.Perm (PublicCharge.EndpointIndex body Leg)) :
    FiniteDist (PublicCharge.EndpointIndex body Leg → ZMod modulus) :=
  seedLaw.map fun seed => PublicCharge.relabelEndpoint (finalRelabeling seed)
    (fun index => (PublicCharge.assembledEndpoint (G := ℤ) centers shift ((modulus : ℤ) - 1)
      (latent seed) (bodyPlacement seed) attachment (second seed) (primary seed) queue
        (scalar seed) index : ZMod modulus))

/-- The assembled channel satisfies the exact public-core charge interface.
All hidden variables are averaged only after proving the pointwise identity. -/
theorem protectedAssemblyChannel_charge (body modulus : ℕ) [NeZero modulus]
    (seedLaw : FiniteDist Seed) (centers : Fin body → ℤ) (shift : Leg → ℤ)
    (latent : Seed → Fin body → ℤ) (bodyPlacement : Seed → Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Seed → Leg → ℤ)
    (queue : Finset (Fin body)) (hqueue : queue.card = modulus) (scalar : Seed → ℤ)
    (finalRelabeling : Seed → Equiv.Perm (PublicCharge.EndpointIndex body Leg)) :
    (protectedAssemblyChannel body modulus seedLaw centers shift latent bodyPlacement
      attachment second primary queue scalar finalRelabeling).eventMass
        (fun endpoint => ∑ index, endpoint index = 0) =
      if PublicCharge.PublicChargeTest modulus centers shift then 1 else 0 := by
  unfold protectedAssemblyChannel
  apply eventMass_of_pointwise_charge
  intro seed
  exact PublicCharge.public_charge_iff_zeroSum modulus centers shift (latent seed)
    (bodyPlacement seed) attachment (second seed) (primary seed) queue hqueue (scalar seed)
      (finalRelabeling seed)

/-- The public core is normalized before the hidden channel, and the
construction's actual assembly discharges the channel-charge hypothesis.
The placement, attachments and queue are fixed throughout this equality. -/
theorem protectedAssembly_public_core_mix {Core : Type*} [Fintype Core]
    (body modulus : ℕ) [NeZero modulus]
    (proposal : FiniteDist Core) (weight : Core → ℝ) (seedLaw : Core → FiniteDist Seed)
    (centers : Core → Fin body → ℤ) (shift : Core → Leg → ℤ)
    (latent : Core → Seed → Fin body → ℤ)
    (bodyPlacement : Core → Seed → Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Core → Seed → Leg → ℤ)
    (queue : Finset (Fin body)) (hqueue : queue.card = modulus) (scalar : Core → Seed → ℤ)
    (finalRelabeling : Core → Seed → Equiv.Perm (PublicCharge.EndpointIndex body Leg))
    (hpositive : 0 < publicCoreMass proposal weight
      (fun core => PublicCharge.PublicChargeTest modulus (centers core) (shift core))) :
    let channel := fun core => protectedAssemblyChannel body modulus (seedLaw core)
      (centers core) (shift core) (latent core) (bodyPlacement core) attachment
        (second core) (primary core) queue (scalar core) (finalRelabeling core)
    (positivePublicCoreLaw proposal weight
      (fun core => PublicCharge.PublicChargeTest modulus (centers core) (shift core))
        hpositive).mix channel =
      positiveEndpointLaw proposal weight channel (fun endpoint => ∑ index, endpoint index = 0)
        (by
          rw [chargedMass_eq_publicCoreMass proposal weight channel
            (fun endpoint => ∑ index, endpoint index = 0)
            (fun core => PublicCharge.PublicChargeTest modulus (centers core) (shift core))
            (fun core => protectedAssemblyChannel_charge body modulus (seedLaw core)
              (centers core) (shift core) (latent core) (bodyPlacement core) attachment
                (second core) (primary core) queue hqueue (scalar core) (finalRelabeling core))]
          exact hpositive) := by
  dsimp only
  apply positivePublicCoreLaw_mix
  intro core
  exact protectedAssemblyChannel_charge body modulus (seedLaw core) (centers core)
    (shift core) (latent core) (bodyPlacement core) attachment (second core) (primary core)
      queue hqueue (scalar core) (finalRelabeling core)

end

end CurrentAFT
